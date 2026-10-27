/-
The Lean script that makes one module's sorried copy (`LeanBlame.Lean.Sorried`): the module's source
with the proof of each `theorem`, `lemma` and `example` replaced by `sorry`, except the proofs that
start at a kept place, cut into one piece per command.

`export` runs it with the library's `lean --run` (it needs the library's environment extensions, as
`Export.statementScript` does), one process per module, after `Sorried` appends a `main` that calls
`LeanBlameSorried.main`. It imports what the module imports, then runs Lean's own command loop with
one step added between parsing and elaborating a command: the proofs are swapped for `sorry`; with
the options `lean` uses, so that what the kept proofs make has the names it has in the library. Then
it compares the copy's constants with the module's `.olean`: kind, universe parameters and type of
every constant, the value of every definition, and the proofs that were kept. Any difference, and
any error while elaborating, is a problem; `export` stops on one. Its definitions live in their own
namespace so that no library name shadows them.

A piece is a command with the comments before it. It says which constants the command declares, and
which constants of the library it uses: those its syntax names (Lean's info trees, as for hover), and
those in the types and values of what it declares. A challenge keeps the pieces its theorems need,
and every piece that is not a declaration (`open`, `variable`, `namespace`, notation…) or that is
an instance, since Lean uses those without naming them (a coercion leaves no trace).

Input, a JSON file: `module`, `source`, `olean`, `keep` (`[line, column]` where the declarations
whose proofs stay begin, as Lean's declaration ranges have them), `keep_names` (their names: their
proofs are compared too), `own` (the library's modules), `options` (the module's Lean options, as
Lake gives them), `out`. Output, into `out`: `pieces` (the module after its imports, up to its end
or `#exit`, as `text`, `keep`, `declares`, `uses`; then a piece with an `end` for each namespace or
section the module leaves open, so that it can sit in a section of a file that merges modules), and
`problems`.
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
  own : Array Name
  options : Options
  out : System.FilePath

def Input.read (path : System.FilePath) : IO Input := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let keys := ["module", "source", "olean", "keep", "keep_names", "own", "options", "out"]
  let .obj fields := j | throw (IO.userError s!"{path}: not a JSON object")
  for (k, _) in fields do
    unless keys.contains k do throw (IO.userError s!"{path}: unknown key `{k}`")
  let get (k : String) : IO Json := IO.ofExcept (j.getObjVal? k)
  let str (k : String) : IO String := do IO.ofExcept ((← get k).getStr?)
  let keep ← IO.ofExcept ((← get "keep").getArr?) >>= (·.mapM fun p => IO.ofExcept do
    let a ← p.getArrVal? 0 >>= (·.getNat?)
    let b ← p.getArrVal? 1 >>= (·.getNat?)
    return (a, b))
  let names (k : String) : IO (Array Name) := do
    IO.ofExcept ((← get k).getArr?) >>= (·.mapM fun n => do
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
           keep, keepNames := ← names "keep_names", own := ← names "own", options, out := ← str "out" }

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

/-- A declaration, which a copy may leave out when nothing needs it: `def`, `theorem`, `structure`
and the like, a `mutual` block, or one of them after `… in`. -/
partial def cuttable (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Command.declaration || stx.isOfKind ``Parser.Command.mutual ||
    stx.isOfKind ``Parser.Command.in && cuttable stx[2]

/-- An instance written as one (`instance`, `@[instance]`): Lean finds it by itself, and a coercion
uses it without naming it. Instances Lean makes (`deriving`, `SizeOf`) are named where used. -/
partial def writesInstance (stx : Syntax) : Bool :=
  if stx.isOfKind ``Parser.Command.in then writesInstance stx[2]
  else stx.isOfKind ``Parser.Command.declaration &&
    (stx[1].isOfKind ``Parser.Command.instance || (stx[0].find? (·.isOfKind ``Parser.Attr.instance)).isSome)

/-- A command as the loop read it: where its first token starts and its last one ends, whether a
challenge keeps it whatever it needs, the constants it added, and the constants its syntax names
(Lean's info trees, as for hover: its own and those of what it elaborated in tasks). -/
structure Cmd where
  start : String.Pos.Raw
  stop : String.Pos.Raw
  keep : Bool
  declares : Array Name
  names : Array Name
  deriving Inhabited

/-- The constants an info tree names. -/
def refs (_ : ContextInfo) (info : Info) (acc : Array Name) : Array Name :=
  match info with
  | .ofTermInfo ti => acc ++ ti.expr.getUsedConstants
  | .ofFieldInfo fi => acc.push fi.projName
  | _ => acc

/-- Lean's own command loop (`Frontend.processCommand`), with `rewrite` between parsing and
elaborating. Lean starts each command with no messages and no info trees, so each command's go to
`log` and `cmds` as soon as it is elaborated, with what it elaborated in tasks. -/
partial def loop (rewrite : Syntax → StateM (Array Range) Syntax) (ranges : IO.Ref (Array Range))
    (cmds : IO.Ref (Array Cmd)) (known : IO.Ref (Std.HashSet Name)) (log : IO.Ref MessageLog) :
    FrontendM Unit := do
  updateCmdPos
  let cmdState ← getCommandState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace,
                 openDecls := scope.openDecls }
  let (cmd, ps, parsed) := Parser.parseCommand (← getInputContext) pmctx (← getParserState) {}
  setParserState ps
  log.modify (· ++ parsed)
  let (cmd', rs) := (rewrite cmd).run #[]
  ranges.modify (· ++ rs)
  elabCommandAtFrontend cmd'
  let st ← getCommandState
  let tasks := (Language.SnapshotTree.mk { diagnostics := .empty }
    (st.snapshotTasks.extract cmdState.snapshotTasks.size)).getAll
  log.modify fun l => tasks.foldl (· ++ ·.diagnostics.msgLog) (l ++ st.messages)
  unless Parser.isTerminalCommand cmd do
    -- `constants` waits for the proofs elaborated in tasks, and so has what they made.
    let seen ← known.get
    let added := st.env.constants.map₂.foldl (init := #[]) fun acc n _ =>
      if seen.contains n then acc else acc.push n
    known.set (seen.insertMany added)
    let names := (st.infoState.trees.toArray ++ tasks.filterMap (·.infoTree?)).foldl (fun acc t => t.foldInfo refs acc) #[]
    let (some start, some stop) := (cmd.getPos?, cmd.getTailPos?)
      | throw (IO.userError s!"a command without a position: {cmd}")
    cmds.modify (·.push { start, stop, keep := !cuttable cmd || writesInstance cmd, declares := added, names })
    loop rewrite ranges cmds known log

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
def closing (scopes : List Command.Scope) : List String :=
  scopes.dropLast.map fun s => if s.header.isEmpty then "end" else s!"end {Name.mkSimple s.header}"

/-- One command of the copy, with the comments before it. -/
structure Piece where
  text : String
  keep : Bool
  declares : Array Name
  uses : Array Name

instance : ToJson Piece where
  toJson p := Json.mkObj [("text", p.text), ("keep", p.keep), ("declares", toJson (p.declares.map toString)),
    ("uses", toJson (p.uses.map toString))]

/-- The source from `start` to `stop`, with each range inside replaced by `:= sorry`. -/
def replace (input : String) (ranges : Array Range) (start stop : String.Pos.Raw) : String := Id.run do
  let bytes := input.toUTF8
  let mut out := ByteArray.empty
  let mut pos := start.byteIdx
  for (a, b) in (ranges.filter fun (a, b) => start ≤ a && b ≤ stop).qsort (·.1.byteIdx < ·.1.byteIdx) do
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
  let cmds ← IO.mkRef #[]
  let known ← IO.mkRef {}
  let log ← IO.mkRef {}
  let (_, st) ← ((loop (strip keep.contains ictx.fileMap sorryVal) ranges cmds known log).run { inputCtx := ictx }).run
    { commandState := Command.mkState env msgs opts, parserState := ps, cmdPos := ps.pos }
  let mut problems := #[]
  for m in (← log.get).toList do
    if m.severity == .error then problems := problems.push (← m.toString)
  let (data, _) ← readModuleData i.olean
  let original : Std.HashMap Name ConstantInfo := .ofList (data.constNames.zip data.constants).toList
  let keepNames : Std.HashSet Name := .ofArray i.keepNames
  let copy := st.commandState.env
  for (n, c) in copy.constants.map₂.toList do
    match original[n]? with
    | none => problems := problems.push s!"{n} is in the copy but not in the library"
    | some o => if let some why := differs c o (keepNames.contains n) then problems := problems.push s!"{n}: {why}"
  let cmds ← cmds.get
  let declared : Std.HashSet Name := cmds.foldl (·.insertMany ·.declares) {}
  let own : Std.HashSet Name := .ofArray i.own
  let ofLibrary (n : Name) : Bool := !isReservedName copy n &&
    (declared.contains n || ((copy.getModuleIdxFor? n).bind (copy.header.moduleNames[·.toNat]?)).any own.contains)
  let rs ← ranges.get
  let mut pieces := #[]
  for c in cmds, k in [:cmds.size] do
    let mine : Std.HashSet Name := .ofArray c.declares
    let terms := c.declares.flatMap fun n => match copy.find? n with
      | some ci => ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      | none => #[]
    let uses := (c.names ++ terms).filter fun n => !mine.contains n && ofLibrary n
    -- From the end of the command before, so that the comments before a command go with it.
    let start := if k == 0 then c.start else cmds[k - 1]!.stop
    pieces := pieces.push {
      text := replace input rs start c.stop
      keep := c.keep
      declares := c.declares.qsort (·.toString < ·.toString)
      uses := (uses.qsort (·.toString < ·.toString)).eraseReps : Piece }
  let close := closing st.commandState.scopes
  unless close.isEmpty do
    pieces := pieces.push { text := "\n" ++ "\n".intercalate close, keep := true, declares := #[], uses := #[] }
  return Json.mkObj [("pieces", toJson pieces), ("problems", toJson problems)]

/-- Imports run the imported modules' initializers, as `lean` does for a file it compiles. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: lean --run SCRIPT INPUT.json")
  enableInitializersExecution
  let i ← Input.read path
  IO.FS.writeFile i.out (← run i).compress
  return 0

end LeanBlameSorried
