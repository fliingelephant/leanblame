/-
The Lean script that makes one module's sorried copy (`LeanBlame.Lean.Sorried`): the module's source
with the proof of each `theorem`, `lemma` and `example` replaced by `sorry`, except the proofs that
start at a kept place.

`export` runs it with the library's `lean --run` (it needs the library's environment extensions, as
`Export.statementScript` does), one process per module, after `Sorried` appends a `main` that calls
`LeanBlameSorried.main`. It imports what the module imports, then runs Lean's own command loop with
one step added between parsing and elaborating a command: the proofs are swapped for `sorry`; with
the options `lean` uses, so that what the kept proofs make has the names it has in the library. Then
it compares the copy's constants with the module's `.olean`: kind, universe parameters and type of
every constant, the value of every definition, and the proofs that were kept. Any difference, and
any error while elaborating, is a problem; `export` stops on one. Its definitions live in their own
namespace so that no library name shadows them.

Input, a JSON file: `module`, `source`, `olean`, `keep` (`[line, column]` where the declarations
whose proofs stay begin, as Lean's declaration ranges have them), `keep_names` (their names: their
proofs are compared too), `options` (the module's Lean options, as Lake gives them), `out`. Output,
into `out`: `text` (the copy: the module after its imports, ending in a line break, then an `end`
for each namespace or section it leaves open, so that it can sit in a section of a file that merges
modules), `problems`,
and `missing`: the module's constants that the copy lacks (the auxiliary lemmas of proofs that became
`sorry`), except names that Lean makes again on demand (equation lemmas).
-/
import Lean

open Lean Elab Frontend

namespace LeanBlameSorried

/-- A place in a source file: line and column, as Lean's declaration ranges have them. -/
abbrev Pos := Nat × Nat

/-- A byte range of the source. -/
abbrev Range := String.Pos.Raw × String.Pos.Raw

structure Input where
  module : Name
  source : System.FilePath
  olean : System.FilePath
  keep : Array Pos
  keepNames : Array Name
  options : Options
  out : System.FilePath

def Input.read (path : System.FilePath) : IO Input := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let keys := ["module", "source", "olean", "keep", "keep_names", "options", "out"]
  let .obj fields := j | throw (IO.userError s!"{path}: not a JSON object")
  for (k, _) in fields do
    unless keys.contains k do throw (IO.userError s!"{path}: unknown key `{k}`")
  let get (k : String) : IO Json := IO.ofExcept (j.getObjVal? k)
  let str (k : String) : IO String := do IO.ofExcept ((← get k).getStr?)
  let keep ← IO.ofExcept ((← get "keep").getArr?) >>= (·.mapM fun p => IO.ofExcept do
    let a ← p.getArrVal? 0 >>= (·.getNat?)
    let b ← p.getArrVal? 1 >>= (·.getNat?)
    return (a, b))
  let keepNames ← IO.ofExcept ((← get "keep_names").getArr?) >>= (·.mapM fun n => do
    let s ← IO.ofExcept n.getStr?
    let some n := Syntax.decodeNameLit ("`" ++ s) | throw (IO.userError s!"not a name: {s}")
    return n)
  let options ← IO.ofExcept ((← get "options").getObj?) >>= fun o =>
    o.toList.foldlM (init := ({} : Options)) fun opts (k, v) =>
      match v with
      | .bool b => pure (opts.setBool k.toName b)
      | .str s => pure (opts.set k.toName s)
      | .num n =>
        match n.mantissa.toNat?, n.exponent with
        | some m, 0 => pure (opts.set k.toName m)
        | _, _ => throw (IO.userError s!"option {k}: {v}")
      | _ => throw (IO.userError s!"option {k}: {v}")
  return { module := (← str "module").toName, source := ← str "source", olean := ← str "olean",
           keep, keepNames, options, out := ← str "out" }

/-- The syntax without source positions, to put where a proof was. -/
partial def bare : Syntax → Syntax
  | .node _ k args => .node .none k (args.map bare)
  | .atom _ v => .atom .none v
  | .ident _ raw n pre => .ident .none raw n pre
  | .missing => .missing

def proofKinds : Array SyntaxNodeKind :=
  #[``Parser.Command.declValSimple, ``Parser.Command.declValEqns, ``Parser.Command.whereStructInst]

/-- A `theorem`, `lemma` or `example`: the keyword first, the proof last. -/
def holdsProof (stx : Syntax) : Bool :=
  stx.getNumArgs ≥ 2 && proofKinds.contains stx.getArgs.back!.getKind &&
    match stx[0] with
    | .atom _ v => v == "theorem" || v == "lemma" || v == "example"
    | _ => false

/-- `stx` with the proof of every declaration (a node `[modifiers, theorem]`) that does not begin
at a kept place replaced by `sorry`; the byte ranges of the proofs replaced are collected. -/
partial def strip (keep : Pos → Bool) (fileMap : FileMap) (sorryVal : Syntax) :
    Syntax → StateM (Array Range) Syntax
  | stx@(.node info k args) => do
    if args.size == 2 && holdsProof args[1]! then
      let start := stx.getPos?.map fileMap.toPosition
      if start.any (fun p => keep (p.line, p.column)) then return stx
      let holder := args[1]!
      let proof := holder.getArgs.back!
      let (some a, some b) := (proof.getPos?, proof.getTailPos?) | return stx
      modify (·.push (a, b))
      return .node info k #[args[0]!, holder.setArg (holder.getNumArgs - 1) sorryVal]
    return .node info k (← args.mapM (strip keep fileMap sorryVal))
  | stx => pure stx

/-- Lean's own command loop (`Frontend.processCommand`), with `rewrite` between parsing and
elaborating. -/
partial def loop (rewrite : Syntax → StateM (Array Range) Syntax) (ranges : IO.Ref (Array Range)) :
    FrontendM Unit := do
  updateCmdPos
  let cmdState ← getCommandState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace,
                 openDecls := scope.openDecls }
  let (cmd, ps, messages) := Parser.parseCommand (← getInputContext) pmctx (← getParserState) cmdState.messages
  setParserState ps
  setMessages messages
  let (cmd', rs) := (rewrite cmd).run #[]
  ranges.modify (· ++ rs)
  elabCommandAtFrontend cmd'
  unless Parser.isTerminalCommand cmd do loop rewrite ranges

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

/-- How the copy's constant `c` differs from the library's `o`, if it does. A theorem's proof is
compared only when `proofToo`. -/
def differs (c o : ConstantInfo) (proofToo : Bool) : Option String :=
  if kindOf c != kindOf o then some s!"a {kindOf c} in the copy, a {kindOf o} in the library"
  else if c.levelParams != o.levelParams then some "its universe parameters differ"
  else if c.type != o.type then some "its type differs"
  else match c, o with
    | .thmInfo a, .thmInfo b => if proofToo && a.value != b.value then some "its proof differs" else none
    | .defnInfo a, .defnInfo b => if a.value != b.value then some "its value differs" else none
    | .opaqueInfo a, .opaqueInfo b => if a.value != b.value then some "its value differs" else none
    | .inductInfo a, .inductInfo b =>
      if a.ctors != b.ctors || a.all != b.all || a.numParams != b.numParams || a.numIndices != b.numIndices
      then some "its constructors differ" else none
    | _, _ => none

/-- The commands that close the scopes left open, innermost first; the last scope is the file's. -/
def closing (scopes : List Command.Scope) : String :=
  String.join (scopes.dropLast.map fun s =>
    if s.header.isEmpty then "end\n" else s!"end {Name.mkSimple s.header}\n")

/-- The source from `start` to `stop`, with each range (all inside) replaced by `:= sorry`. -/
def replace (input : String) (ranges : Array Range) (start stop : String.Pos.Raw) : String := Id.run do
  let bytes := input.toUTF8
  let mut out := ByteArray.empty
  let mut pos := start.byteIdx
  for (a, b) in ranges.qsort (·.1.byteIdx < ·.1.byteIdx) do
    out := out ++ bytes.extract pos a.byteIdx ++ ":= sorry".toUTF8
    pos := b.byteIdx
  return String.fromUTF8! (out ++ bytes.extract pos stop.byteIdx)

def run (i : Input) : IO Json := do
  let input ← IO.FS.readFile i.source
  let ictx := Parser.mkInputContext input i.source.toString
  let (header, ps, msgs) ← Parser.parseHeader ictx
  if HeaderSyntax.isModule header then
    throw (IO.userError s!"{i.module}: files of the module system are not supported yet")
  -- Merged with other modules, it would import `Init` too.
  unless header.raw[1].isNone do
    throw (IO.userError s!"{i.module}: `prelude` files are not supported")
  -- As `lean` elaborates a file (`runFrontend`): a theorem's proof in a task of its own, which
  -- also decides the names of what the proof makes. Linters only print.
  let opts := Elab.async.setIfNotSet i.options true |>.setBool `linter.all false
  let (env, msgs) ← processHeader header opts msgs ictx (mainModule := i.module)
  if msgs.hasErrors then
    throw (IO.userError s!"{i.module}: importing failed: {← msgs.toList.mapM (·.toString)}")
  let sorryVal ← match Parser.runParserCategory env `command "theorem x : True := sorry" with
    | .ok stx => pure (bare stx[1][3])
    | .error e => throw (IO.userError e)
  let keep : Std.HashSet Pos := .ofArray i.keep
  let ranges ← IO.mkRef #[]
  let (_, st) ← ((loop (strip keep.contains ictx.fileMap sorryVal) ranges).run { inputCtx := ictx }).run
    { commandState := Command.mkState env msgs opts, parserState := ps, cmdPos := ps.pos }
  -- Errors of the commands, and of the proofs elaborated in tasks.
  let tasks := Language.SnapshotTree.mk { diagnostics := .empty } st.commandState.snapshotTasks
  let messages := tasks.getAll.foldl (· ++ ·.diagnostics.msgLog) st.commandState.messages
  let mut problems := #[]
  for m in messages.toList do
    if m.severity == .error then problems := problems.push (← m.toString)
  let (data, _) ← readModuleData i.olean
  let original : Std.HashMap Name ConstantInfo := .ofList (data.constNames.zip data.constants).toList
  let keepNames : Std.HashSet Name := .ofArray i.keepNames
  let copy := st.commandState.env
  let mut present : Std.HashSet Name := {}
  for (n, c) in copy.constants.map₂.toList do
    present := present.insert n
    match original[n]? with
    | none => problems := problems.push s!"{n} is in the copy but not in the library"
    | some o => if let some why := differs c o (keepNames.contains n) then problems := problems.push s!"{n}: {why}"
  let missing := data.constNames.filter fun n => !present.contains n && !isReservedName copy n
  -- From the end of the imports to the command that ended the file: the end, or `#exit`.
  let body := replace input (← ranges.get) ps.pos st.cmdPos
  let body := if body.isEmpty || body.endsWith "\n" then body else body ++ "\n"
  return Json.mkObj [("text", Json.str (body ++ closing st.commandState.scopes)),
    ("problems", toJson problems), ("missing", toJson (missing.map toString))]

/-- Imports run the imported modules' initializers, as `lean` does for a file it compiles. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: lean --run SCRIPT INPUT.json")
  enableInitializersExecution
  let i ← Input.read path
  IO.FS.writeFile i.out (← run i).compress
  return 0

end LeanBlameSorried
