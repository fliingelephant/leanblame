/-
Challenge pieces (docs/decisions.md, "Challenges"): the piece graph that the comparator
challenges of the library's tagged theorems are cut from, taken from the library's source as
written; nothing is elaborated again.

A piece is text in one file of a challenge; its links are the pieces it needs. Most pieces are one
command as written: a declaration; an instance; an `attribute` command, for one of its names; or a
command that sets the scope of what comes after it (`namespace`, `section`, `end`, `open`,
`variable`, `universe`, `set_option`, `include`, `omit`, local attributes). A declaration needs the
commands that declare the library's constants in its kernel terms (proofs included, since `sorry`
there would reach every proof of a statement that uses it) and every name in its text that Lean's
record of the build (the module's `.ilean`) says refers to one, so that a lemma given to `simp` but
not used counts too; and the instances of its module, since Lean uses instances without naming them.
Every command needs the `namespace` and `section` around it, with their `end`s, and one that does not
open or close a scope needs the scope commands before it. An `attribute` command comes with the
declaration it names, or, for a constant from outside the library, with its module. A tagged
theorem's statement is a piece of `Challenge.lean`: its command with the proof replaced by `sorry`,
among copies of the scope commands it needs; it needs what its statement uses. The challenge of
chosen theorems is their statements, what those need, what that needs, and so on (`Graph.cut`): it
holds what they need and nothing else, and what several need once.

The pieces of a module sit in a `section` of their own, which first sets the Lean options Lake builds
the module with, so that what one module opens and sets ends with it; an `end` closes each scope the
module leaves open. `ChallengeDeps.lean` imports what the modules it holds import from outside the
library. A file holds the pieces of several modules, where a name could read differently: another
module's declaration, or its imports, may share it. So each recorded name is checked to read back as
the constant it named, in the scope it was written in, among everything the library imports (Lean's
name resolution); a name that would not is written as Lean writes names (`unresolveNameGlobal`). An
`open` needs its namespace to exist: one that no module from outside the library which its module
imports makes is declared first (`namespace N end N`); declaring one that exists changes nothing.
Lean names a private declaration after its module: one whose name a declaration of another module in
the graph has too is written with its module (`«secret (M)»`). Module-system words (`public`, `meta`,
`@[expose]`) and the `trusted` attribute are dropped: a challenge is a plain file that does not
import LeanBlame.

What stops a challenge is part of the graph, not an error of `export`: a piece has a problem when it
needs a declaration no command declares or a module that does not read, when its module has a Lean
option a file cannot set, or when it is a statement with no proof to replace; the lakefile has one
when the library requires a package by path. A challenge cannot state a theorem whose proof the
other theorems need.
-/
import Lean
import Lean.Server.References
import LeanBlame.Core.Store

namespace LeanBlame.Pieces

open Lean Elab

/-- The files of a challenge. -/
def lakefileFile : String := "lakefile.toml"
def toolchainFile : String := "lean-toolchain"
def depsFile : String := "ChallengeDeps.lean"
def challengeFile : String := "Challenge.lean"
def files : Array String := #[lakefileFile, toolchainFile, depsFile, challengeFile]

/-- A piece of the piece graph (docs/schemas.md §6): its text in one file of a challenge;
the pieces it needs, by index; the tagged theorem it states (in `Challenge.lean`) or declares with
its proof (in `ChallengeDeps.lean`); and why a challenge that holds it cannot be made. -/
structure Piece where
  file : String
  text : String
  needs : Array Nat
  tagged : Option String
  problem : Option String
  deriving Inhabited

/-- The pieces the challenges of the library's tagged theorems are cut from, in the order their
files hold them. -/
structure Graph where
  pieces : Array Piece
  deriving Inhabited

instance : ToJson Piece where
  toJson p := Json.mkObj [("file", p.file), ("text", p.text), ("needs", toJson p.needs),
    ("theorem", toJson p.tagged), ("problem", toJson p.problem)]

instance : ToJson Graph where
  toJson g := Json.mkObj [("pieces", toJson g.pieces)]

def Piece.fromJson? (j : Json) : Except String Piece := do
  let o ← JsonObj.read j "piece" ["file", "text", "needs", "theorem", "problem"]
  let p : Piece := { file := ← o.get String "file", text := ← o.get String "text", needs := ← o.get (Array Nat) "needs"
                     tagged := ← o.get (Option String) "theorem", problem := ← o.get (Option String) "problem" }
  unless files.contains p.file do throw s!"piece: `{p.file}` is not a file of a challenge"
  return p

def Graph.fromJson? (j : Json) : Except String Graph := do
  let o ← JsonObj.read j "piece graph" ["pieces"]
  let pieces ← (← o.get (Array Json) "pieces").mapM Piece.fromJson?
  unless pieces.all (·.needs.all (· < pieces.size)) do throw "piece graph: a piece needs a piece it lacks"
  return { pieces }

def read (root : System.FilePath) (hash : String) : IO Graph := do
  let p := Store.objectPath root .pieces hash
  unless ← p.pathExists do fail s!"piece graph {hash} is not in the store"
  match Json.parse (← IO.FS.readFile p) >>= Graph.fromJson? with
  | .ok g => return g
  | .error e => fail s!"{p}: {e}"

/-- The challenge of the tagged theorems `names` (docs/schemas.md §6), each file with its
text: their statements, the pieces those need, the pieces these need, and so on, each file the text
of its pieces in order. Or why it cannot be made: the problems of the pieces it holds, and each named
theorem whose proof its `ChallengeDeps.lean` holds. -/
def Graph.cut (g : Graph) (names : Array String) : Except (Array String) (Array (String × String)) := do
  let mut todo := #[]
  for n in names do
    match g.pieces.findIdx? fun p => p.file == challengeFile && p.tagged == some n with
    | some i => todo := todo.push i
    | none => throw #[s!"{n} has no statement in the piece graph"]
  let mut held : Std.HashSet Nat := {}
  while h : todo.size > 0 do
    let i := todo[todo.size - 1]
    todo := todo.pop
    unless held.contains i do
      held := held.insert i
      todo := todo ++ g.pieces[i]!.needs
  let order := held.toArray.qsort (· < ·)
  let problems := dedup <| order.filterMap (g.pieces[·]!.problem) ++ order.filterMap fun i =>
    let p := g.pieces[i]!
    if p.file != depsFile then none else (p.tagged.filter names.contains).map
      (s!"{·}: the other theorems need its proof, so the challenge cannot state it")
  unless problems.isEmpty do throw problems
  return files.map fun f => (f, String.join (order.filterMap fun i =>
    let p := g.pieces[i]!
    if p.file == f then some p.text else none).toList)

/-- Where Lean's declaration ranges put `n` in its source; a module of the module system keeps
those of its private declarations at the private level. -/
def declRange? (env : Environment) (n : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .exported) env n <|> declRangeExt.find? (level := .server) env n <|>
    declRangeExt.find? (level := .private) env n

/-- A name as `Name.toString` prints it (as `.ilean` files have them), read back; a component of
digits only is a number, as in private names. -/
def nameOf? (text : String) : Option Name :=
  (Syntax.decodeNameLit ("`" ++ text)).map fix
where
  fix : Name → Name
    | .str p s => if !s.isEmpty && s.all Char.isDigit then .num (fix p) s.toNat! else .str (fix p) s
    | .num p k => .num (fix p) k
    | .anonymous => .anonymous

/-! ## Reading a module -/

/-- What a command does in a challenge. -/
inductive Role where
  /-- `namespace` or `section`: opens scopes, which `end` closes. -/
  | opens
  | closes
  /-- `open`, `variable`, `universe`, `set_option`, `include`, `omit`, a local attribute: sets the
  scope of the declarations after it. -/
  | sets
  /-- A global `attribute` command. -/
  | attribute
  /-- Declares constants (the declaration ranges say), or nothing a challenge needs. -/
  | other
  deriving BEq, Inhabited

/-- A command as Lean's parser read it, with the namespace and `open`s its names are read in (after
an `… in` prefix). -/
structure Cmd where
  stx : Syntax
  start : String.Pos.Raw
  stop : String.Pos.Raw
  role : Role
  ns : Name
  openDecls : List OpenDecl
  /-- The scopes it opens, outermost first: `namespace A.B` opens `A` and `B`. -/
  opens : Array String := #[]
  /-- How many scopes it closes: `end A.B` closes two. -/
  closes : Nat := 0
  /-- The namespaces its `open`s open, as Lean resolves them. -/
  opened : Array Name := #[]
  declares : Array Name := #[]
  deriving Inhabited

/-- One module, read. -/
structure Read where
  module : Name
  bytes : ByteArray
  fileMap : FileMap
  /-- The environment with this module as the main one, so that its private names read. -/
  env : Environment
  options : Options
  cmds : Array Cmd
  /-- The command that declares each of the module's constants. -/
  owner : NameMap Nat
  /-- Each name in the source that refers to one of the library's constants: start, end, constant. -/
  refs : Array (String.Pos.Raw × String.Pos.Raw × Name)
  /-- Where the source writes the name of each constant it declares, as `refs`. -/
  defs : Array (String.Pos.Raw × String.Pos.Raw × Name)
  /-- Whether each command writes an instance. -/
  instances : Array Bool

/-- The library's constants that the names in `c` refer to. -/
def Read.named (r : Read) (c : Cmd) (stop := c.stop) : Array Name :=
  r.refs.filterMap fun (a, _, n) => if c.start ≤ a && a < stop then some n else none

/-- The longest name recorded from `a` that ends by `b`, with its end: a shorter one is the head of
a dotted name (`h.symm`). -/
def Read.refAt? (r : Read) (a b : String.Pos.Raw) : Option (String.Pos.Raw × Name) :=
  r.refs.foldl (init := none) fun best (s, e, n) =>
    if s != a || e.byteIdx > b.byteIdx then best
    else match best with
      | some (e', _) => if e.byteIdx > e'.byteIdx then some (e, n) else best
      | none => some (e, n)

def proofKinds : Array SyntaxNodeKind :=
  #[``Parser.Command.declValSimple, ``Parser.Command.declValEqns, ``Parser.Command.whereStructInst]

/-- A `theorem`, `lemma` or `example`: the keyword first, the proof last. -/
def holdsProof (stx : Syntax) : Bool :=
  stx.getNumArgs ≥ 2 && proofKinds.contains stx.getArgs.back!.getKind &&
    match stx[0] with
    | .atom _ v => v == "theorem" || v == "lemma" || v == "example"
    | _ => false

/-- The proof of the theorem `stx` declares. -/
partial def proofOf? (stx : Syntax) : Option Syntax :=
  if stx.getNumArgs == 2 && holdsProof stx[1] then some stx[1].getArgs.back!
  else stx.getArgs.findSome? proofOf?

/-- The command after every `… in` prefix. -/
partial def innermost (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Parser.Command.in then innermost stx[2] else stx

/-- An instance written as one (`instance`, `@[instance]`). -/
def writesInstance (stx : Syntax) : Bool :=
  let d := innermost stx
  d.isOfKind ``Parser.Command.declaration &&
    (d[1].isOfKind ``Parser.Command.instance || (d[0].find? (·.isOfKind ``Parser.Attr.instance)).isSome)

def setsScope : Array SyntaxNodeKind :=
  #[``Parser.Command.open, ``Parser.Command.variable, ``Parser.Command.universe,
    ``Parser.Command.set_option, ``Parser.Command.include, ``Parser.Command.omit]

/-- Attributes a plain file without LeanBlame does not have. -/
def dropsAttribute (inst : Syntax) : Bool :=
  let a := inst[1]
  a.getKind == `LeanBlame.Attr.trusted || (a.isOfKind ``Parser.Attr.simple && a[0].getId == `expose)

/-- The attributes an `attribute` command sets, without those a challenge drops. -/
def attributesKept (stx : Syntax) : Array Syntax :=
  stx[2].getSepArgs.filter (!dropsAttribute ·)

/-- A `local` or `scoped` attribute, which lasts as long as its scope. -/
def scopedAttribute (inst : Syntax) : Bool :=
  inst.isOfKind ``Parser.Term.attrInstance && inst[0][0].getNumArgs > 0

def roleOf (stx : Syntax) : Role :=
  let d := innermost stx
  if d.isOfKind ``Parser.Command.namespace || d.isOfKind ``Parser.Command.section then .opens
  else if d.isOfKind ``Parser.Command.end then .closes
  else if setsScope.contains d.getKind then .sets
  else if d.isOfKind ``Parser.Command.attribute then
    if d[2].getSepArgs.all scopedAttribute then .sets else .attribute
  else .other

/-- Run `x` on the command state; an error stops `export`. -/
def runCmd (ctx : Command.Context) (s : Command.State) (x : Command.CommandElabM Unit) :
    IO Command.State := do
  match ← EIO.toIO' ((x ctx).run s) with
  | .ok (_, s') =>
    if s'.messages.hasErrors then
      let errs ← s'.messages.toList.filterMapM fun m =>
        if m.severity == .error then some <$> m.toString else pure none
      fail ("\n".intercalate errs)
    return s'
  | .error e => fail (← e.toMessageData.toString)

/-- Elaborate the command written `text`. -/
def elabText (ctx : Command.Context) (s : Command.State) (text : String) : IO Command.State := do
  match Parser.runParserCategory s.env `command text with
  | .ok stx => runCmd ctx s (Command.elabCommand stx)
  | .error e => fail s!"`{text}`: {e}"

/-- The components of a name, as `end` names scopes. -/
def headers (n : Name) : Array String :=
  n.components.toArray.map toString

/-- The namespaces the `open` command `stx` opens, as Lean resolves them in `scope`. -/
def openedBy (env : Environment) (scope : Command.Scope) (stx : Syntax) : Array Name :=
  let d := stx[1]
  let ids := if d.isOfKind ``Parser.Command.openSimple then d[0].getArgs
    else if d.isOfKind ``Parser.Command.openScoped then d[1].getArgs
    else #[d[0]]
  ids.flatMap fun id =>
    (ResolveName.resolveNamespace env scope.currNamespace scope.openDecls id.getId).toArray

/-- Follow Lean's scopes through `stx` as the module sets them: `namespace`, `section`, `end` and
`open` decide how names read. Module-system words of a `section` change nothing here. Returns the
state, the namespace and `open`s the command's names read in, and the namespaces it opens. -/
partial def track (ctx : Command.Context) (s : Command.State) (stx : Syntax) :
    IO (Command.State × Name × List OpenDecl × Array Name) := do
  if stx.isOfKind ``Parser.Command.in then
    let s ← elabText ctx s "section"
    let isOpen := stx[0].isOfKind ``Parser.Command.open
    let opened := if isOpen then openedBy s.env s.scopes.head! stx[0] else #[]
    let s ← if isOpen then runCmd ctx s (Command.elabCommand stx[0]) else pure s
    let (s, ns, opens, inner) ← track ctx s stx[2]
    return (← elabText ctx s "end", ns, opens, opened ++ inner)
  let scope := s.scopes.head!
  let opened := if stx.isOfKind ``Parser.Command.open then openedBy s.env scope stx else #[]
  let s ← if stx.isOfKind ``Parser.Command.namespace then elabText ctx s s!"namespace {stx[1].getId}"
    else if stx.isOfKind ``Parser.Command.section then
      elabText ctx s (match stx[2].getOptional? with | some i => s!"section {i.getId}" | none => "section")
    else if stx.isOfKind ``Parser.Command.end || stx.isOfKind ``Parser.Command.open then
      runCmd ctx s (Command.elabCommand stx)
    else pure s
  let now := s.scopes.head!
  -- A `namespace` or `section` command's own names read where it stands.
  if stx.isOfKind ``Parser.Command.namespace || stx.isOfKind ``Parser.Command.section then
    return (s, scope.currNamespace, scope.openDecls, opened)
  return (s, now.currNamespace, now.openDecls, opened)

/-- The command among `cmds` (in order) that holds the byte `p`. -/
def containing (cmds : Array Cmd) (p : String.Pos.Raw) : Option Nat := Id.run do
  let mut lo := 0
  let mut hi := cmds.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if cmds[mid]!.stop.byteIdx ≤ p.byteIdx then lo := mid + 1 else hi := mid
  match cmds[lo]? with
  | some c => if c.start.byteIdx ≤ p.byteIdx then some lo else none
  | none => none

/-- The command that declares `n`, by the names Lean gave what it made for a declaration
(`T.mk`, `f.match_1`, `t.proof_1`; in a module of the module system, private ones such as
`_private.M.0.t._simp_1` for a public `t`). -/
def ownerUp (owner : NameMap Nat) : Name → Option Nat
  | .anonymous => none
  | p@(.str q _) | p@(.num q _) => (owner.find? p).orElse fun _ => ownerUp owner q

/-- Read module `m` (its source `file`, its `.ilean`) in `env`, which imports the whole library
(`library`): its commands, the command that declares each of its constants, and the names in it
that refer to the library's constants. -/
def readModule (env : Environment) (options : Options) (library : NameSet) (m : Name)
    (file ilean : System.FilePath) : IO Read := do
  let source ← IO.FS.readFile file
  let ictx := Parser.mkInputContext source file.toString
  let (header, ps, msgs) ← Parser.parseHeader ictx
  if msgs.hasErrors then fail s!"{m}: its header does not parse"
  -- Merged with other modules, it would import `Init` too.
  unless header.raw[1].isNone do fail s!"{m}: `prelude` files are not supported"
  let env := env.setMainModule m
  let ctx : Command.Context := { fileName := file.toString, fileMap := ictx.fileMap, snap? := none, cancelTk? := none }
  let mut s := Command.mkState env {} options
  let mut ps := ps
  let mut cmds : Array Cmd := #[]
  repeat
    let scope := s.scopes.head!
    let pmctx := { env := s.env, options := scope.opts, currNamespace := scope.currNamespace,
                   openDecls := scope.openDecls }
    let (stx, ps', parsed) := Parser.parseCommand ictx pmctx ps {}
    ps := ps'
    if parsed.hasErrors then
      let errs ← parsed.toList.mapM (·.toString)
      fail s!"{m}: Lean's parser fails, with every import of the library:\n{"\n".intercalate errs}"
    if Parser.isTerminalCommand stx then break
    let (some start, some stop) := (stx.getPos?, stx.getTailPos?)
      | fail s!"{m}: a command without a position"
    let (s', ns, openDecls, opened) ← try track ctx s stx
      catch e => fail s!"{m}:{(ictx.fileMap.toPosition start).line}: {e}"
    s := s'
    let d := innermost stx
    let role := roleOf stx
    let opens := if role != .opens then #[]
      else if d.isOfKind ``Parser.Command.namespace then headers d[1].getId
      else match d[2].getOptional? with | some i => headers i.getId | none => #[""]
    -- `end A.B` closes two scopes; its name is `identWithPartialTrailingDot`, two nodes.
    let closes := if role != .closes then 0 else if d[1].getNumArgs == 0 then 1
      else d[1][0].getId.components.length
    cmds := cmds.push { stx, start, stop, role, ns, openDecls, opens, closes, opened }
  let some idx := env.getModuleIdx? m | fail s!"module {m} was not imported"
  let some data := env.header.moduleData[idx.toNat]? | fail s!"module {m} has no data"
  let mut owner : NameMap Nat := {}
  let mut later := #[]
  for n in data.constNames do
    match (declRange? env n).bind (containing cmds <| ictx.fileMap.ofPosition ·.range.pos) with
    | some i => owner := owner.insert n i
    | none => later := later.push n
  for n in later do
    let up := (ownerUp owner n.getPrefix).orElse fun _ => (privateToUserName? n).bind (ownerUp owner ·.getPrefix)
    if let some i := up then owner := owner.insert n i
  for (n, i) in owner do
    cmds := cmds.modify i fun c => { c with declares := c.declares.push n }
  -- Lean's record of the build: where each name that refers to a constant is.
  let il ← Server.Ilean.load ilean
  let mut refs := #[]
  let mut defs := #[]
  for (ident, info) in il.references do
    let .const _ text := ident | continue
    let some n := nameOf? text | continue
    let some i := env.getModuleIdxFor? n | continue
    let some mod := env.header.moduleNames[i.toNat]? | continue
    unless library.contains mod do continue
    for u in info.usages do
      let r := u.range
      refs := refs.push (ictx.fileMap.lspPosToUtf8Pos r.start, ictx.fileMap.lspPosToUtf8Pos r.end, n)
    if let some d := info.definition? then
      defs := defs.push (ictx.fileMap.lspPosToUtf8Pos d.range.start, ictx.fileMap.lspPosToUtf8Pos d.range.end, n)
  return { module := m, bytes := source.toUTF8, fileMap := ictx.fileMap, env, options, cmds,
           owner, refs, defs, instances := cmds.map (writesInstance ·.stx) }

/-! ## Writing a command for a challenge -/

/-- A change to the source: the bytes from `start` to `stop` become `text`. -/
structure Edit where
  start : String.Pos.Raw
  stop : String.Pos.Raw
  text : String

/-- The source from `start` to `stop` with `edits` made. -/
def apply (bytes : ByteArray) (start stop : String.Pos.Raw) (edits : Array Edit) : String := Id.run do
  let mut out := ByteArray.empty
  let mut pos := start.byteIdx
  for e in (edits.filter fun e => start ≤ e.start && e.stop ≤ stop).qsort (·.start.byteIdx < ·.start.byteIdx) do
    if e.start.byteIdx < pos then continue
    out := out ++ bytes.extract pos e.start.byteIdx ++ e.text.toUTF8
    pos := e.stop.byteIdx
  return String.fromUTF8! (out ++ bytes.extract pos stop.byteIdx)

/-- Where `stx` starts, and where the whitespace after it ends. -/
def span? (stx : Syntax) : Option (String.Pos.Raw × String.Pos.Raw) := do
  let a ← stx.getPos?
  let b ← match stx.getTailInfo with
    | .original _ _ trailing _ => some trailing.stopPos
    | _ => stx.getTailPos?
  return (a, b)

/-- The source of `stx`, without the whitespace around it. -/
def textOf (stx : Syntax) : String :=
  ((stx.getSubstring? (withLeading := false) (withTrailing := false)).map (·.toString)).getD ""

/-- The name of the parts `parts`. -/
def ofParts (parts : List Name) : Name := parts.foldl (· ++ ·) .anonymous

/-- A private name written with its module (`make`): `secret` of module `M` as `«secret (M)»`. -/
def withModule (s : String) (m : Name) : String := s!"{s} ({m})"

/-- The private declaration a name written with its module (`withModule`) names, if `modules` has
that module: `A.«b (M)».c` is `A.b.c` of `M`. -/
def unclash? (modules : NameSet) (u : Name) : Option (Name × Name) :=
  let parts := u.components
  parts.findSome? fun p => match p with
    | .str .anonymous s => match s.splitOn " (" with
      | [x, rest] =>
        let m := (rest.splitOn ")").head!.toName
        if rest.endsWith ")" && modules.contains m then
          some (m, ofParts (parts.map fun q => if q == p then Name.mkSimple x else q))
        else none
      | _ => none
    | _ => none

/-- The name in `renamed` that `n` is or starts with, and its new last part. -/
def renamedPrefix? (renamed : NameMap String) : Name → Option (Name × String)
  | .anonymous => none
  | p@(.str q _) | p@(.num q _) => match renamed.find? p with
    | some s => some (p, s)
    | none => renamedPrefix? renamed q

/-- Syntax whose identifiers are not names read in a scope: what a declaration declares, field
names, constructor names of `cases` and `induction`, named arguments. -/
def nameless : Array SyntaxNodeKind :=
  #[``Parser.Command.declId, ``Parser.Term.structInstLVal, ``Parser.Term.proj, ``Parser.Term.dotIdent,
    ``Parser.Tactic.inductionAltLHS, ``Parser.Term.namedArgument, ``Parser.Term.namedPattern]

/-- The changes that write command `c` for a challenge: module-system words and the dropped
attributes go; a name the `.ilean` says refers to a constant, which reads in `r.env` (with the
command's namespace and `open`s) as other constants too or instead, is written as Lean writes it. A
challenge holds some of the constants of `r.env`, so a name that reads as that constant alone, or as
no constant (a local, such as a field the command declares), reads the same there. -/
partial def edits (r : Read) (c : Cmd) (renamed : NameMap String) (stx : Syntax) (parent : SyntaxNodeKind) :
    StateT (Array Edit) IO Unit := do
  let drop (s : Syntax) : StateT (Array Edit) IO Unit := do
    if let some (a, b) := span? s then modify (·.push { start := a, stop := b, text := "" })
  match stx with
  | .node _ k args =>
    if k == ``Parser.Command.public || k == ``Parser.Command.meta then return ← drop stx
    if k == ``Parser.Command.sectionHeader then
      for i in [0, 1, 3] do drop stx[i]
      return
    if k == ``Parser.Term.attributes then
      let insts := stx[1].getSepArgs
      let kept := insts.filter (!dropsAttribute ·)
      if kept.size < insts.size then
        let some (a, b) := span? stx | return
        let text := if kept.isEmpty then "" else "@[" ++ ", ".intercalate (kept.toList.map textOf) ++ "] "
        modify (·.push { start := a, stop := b, text })
        return
    if k == ``Parser.Command.attribute then
      let kept := attributesKept stx
      if kept.size < stx[2].getSepArgs.size then
        let (some a, some b) := (stx[2].getPos?, stx[2].getTailPos?) | return
        modify (·.push { start := a, stop := b, text := ", ".intercalate (kept.toList.map textOf) })
    for a in args do edits r c renamed a k
  | .ident .. =>
    if nameless.contains parent then return
    let (some a, some b) := (stx.getPos?, stx.getTailPos?) | return
    let some (e, n) := r.refAt? a b | return
    -- A private name written with its module: `renames` writes it.
    if (renamedPrefix? renamed n).isSome then return
    if c.declares.contains n then return
    if e != b && r.bytes.get! e.byteIdx != '.'.toNat.toUInt8 then return
    let some written := nameOf? (String.fromUTF8! (r.bytes.extract a.byteIdx e.byteIdx)) | return
    let reads := (ResolveName.resolveGlobalName r.env r.options c.ns c.openDecls written).filterMap
      fun (x, fields) => if fields.isEmpty then some x else none
    if reads.isEmpty || reads == [n] then return
    let ctx : Core.Context := { fileName := "", fileMap := r.fileMap, options := r.options,
                                currNamespace := c.ns, openDecls := c.openDecls }
    let (better, _) ← (unresolveNameGlobal n : CoreM Name).toIO ctx { env := r.env }
    modify (·.push { start := a, stop := e, text := better.toString })
  | _ => pure ()

/-- The changes that write the private names `renamed` gives a new last part in command `c`: where
it declares one, and each name in it that refers to one or to what Lean made with one
(`«secret (M)».eq_1`). The part of the written name that names the declaration changes; a name
written without it (a field `.v` of a renamed structure) stays. -/
def renames (r : Read) (c : Cmd) (renamed : NameMap String) : Array Edit :=
  (r.defs ++ r.refs).filterMap fun (a, e, n) => do
    guard (c.start ≤ a && a < c.stop)
    let (base, s) ← renamedPrefix? renamed n
    let parts := (← nameOf? (String.fromUTF8! (r.bytes.extract a.byteIdx e.byteIdx))).components
    let after := (privateToUserName n).getNumParts - (privateToUserName base).getNumParts
    guard (after < parts.length)
    let new := ofParts (parts.set (parts.length - 1 - after) (Name.mkSimple s))
    return { start := a, stop := e, text := new.toString }

/-- The changes that write command `c` for a challenge. -/
def changes (r : Read) (c : Cmd) (renamed : NameMap String) : IO (Array Edit) := do
  let (_, es) ← (edits r c renamed c.stx .anonymous).run #[]
  return es ++ renames r c renamed

/-- The statement of the theorem command `c` declares, with the changes `es`: its text with the
proof replaced by `sorry`. -/
def statementOf? (r : Read) (c : Cmd) (es : Array Edit) : Option String := do
  let p ← proofOf? (innermost c.stx)
  let a ← p.getPos?
  let b ← p.getTailPos?
  return apply r.bytes c.start c.stop ((es.filter (·.stop ≤ a)).push { start := a, stop := b, text := ":= sorry" })

/-- Whether `n` or a name it starts with is in `set`. -/
def under (set : NameMap α) : Name → Bool
  | .anonymous => false
  | p@(.str q _) | p@(.num q _) => set.contains p || under set q

/-! ## The piece graph -/

/-- The namespaces Lean makes for constant `n` (`Lean.registerNamePrefixes`): the prefixes of its
user name, up to the first that is not made of words alone, unless the name's last part starts with
`_`. -/
def namespacesOf (n : Name) (acc : NameSet) : NameSet :=
  match privateToUserName n with
  | .str p s => if s.startsWith "_" then acc else go p acc
  | _ => acc
where
  words : Name → Bool
    | .str .anonymous _ => true
    | .str p _ => words p
    | _ => false
  go : Name → NameSet → NameSet
    | p@(.str q _), acc => if words p then go q (acc.insert p) else acc
    | _, acc => acc

/-- The modules `roots` import, directly or not, and the roots. -/
def importClosure (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let m := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if let some i := env.getModuleIdx? m then
      todo := todo ++ (env.header.moduleData[i.toNat]?.map (·.imports.map (·.module))).getD #[]
  return seen

/-- The constants in the kernel terms of `n`: its type, and with `value` its value or proof. -/
def termUses (env : Environment) (n : Name) (value : Bool) : Array Name :=
  match env.find? n with
  | some ci => ci.type.getUsedConstants ++
      (if value then ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[] else #[])
  | none => #[]

/-- How the commands of a module nest. -/
structure Scopes where
  /-- For each command: the commands that open the scopes around it, and, unless it opens or closes
  a scope, the commands before it that set the scopes it is in. -/
  context : Array (Array Nat)
  /-- Each scope: the command that opens it, its name as `end` writes it, and the command that
  closes it, if the module does. `namespace A.B` opens two scopes, and `end A.B` closes two. -/
  scopes : Array (Nat × String × Option Nat)
  deriving Inhabited

def scopesOf (r : Read) : Scopes := Id.run do
  let mut scopes : Array (Nat × String × Option Nat) := #[]
  -- The scopes open now, innermost last, and the commands that set each, the file's first.
  let mut stack : Array Nat := #[]
  let mut sets : Array (Array Nat) := #[#[]]
  let mut context := #[]
  for c in r.cmds, i in [:r.cmds.size] do
    let around := dedup (stack.map fun k => scopes[k]!.1)
    context := context.push <|
      if c.role == .opens || c.role == .closes then around else around ++ sets.flatten
    match c.role with
    | .opens =>
      for h in c.opens do
        stack := stack.push scopes.size
        scopes := scopes.push (i, h, none)
        sets := sets.push #[]
    | .closes =>
      for _ in [:c.closes] do
        let some k := stack.back? | break
        stack := stack.pop
        sets := sets.pop
        scopes := scopes.modify k fun (o, h, _) => (o, h, some i)
    | .sets => sets := sets.modify (sets.size - 1) (·.push i)
    | _ => pure ()
  return { context, scopes }

/-- The library's constant that the `a`-th name of the `attribute` command `c` refers to, if one does. -/
def Read.target? (r : Read) (c : Cmd) (a : Nat) : Option Name := do
  let id := (innermost c.stx)[4][a]
  let (_, n) ← r.refAt? (← id.getPos?) (← id.getTailPos?)
  return n

/-- The `attribute` commands of `r` that keep an attribute: each command, each place of a name it
gives them to, and the library's constant that name refers to, if one does. -/
def attributesOf (r : Read) : Array (Nat × Nat × Option Name) := Id.run do
  let mut out := #[]
  for c in r.cmds, i in [:r.cmds.size] do
    let d := innermost c.stx
    unless c.role == .attribute && !(attributesKept d).isEmpty do continue
    for a in [:d[4].getNumArgs] do
      out := out.push (i, a, r.target? c a)
  return out

/-- A package the library's lakefile requires (Lake: a package of `lake-manifest.json` that is not
inherited): its git URL, commit and subdirectory; `git` and `rev` are `none` for a path
dependency. -/
structure Require where
  name : String
  git : Option String
  rev : Option String
  subDir : Option String
  deriving Inhabited, Repr

/-- LeanBlame's own package, which a challenge leaves out. -/
def leanblamePackage : String := "leanblame"

/-- A TOML string. -/
def tomlString (s : String) : String := (Json.str s).compress

/-- A challenge's `lakefile.toml`: what the library's lakefile requires (`required`) but LeanBlame,
by git, and the libraries `ChallengeDeps` and `Challenge`. It sets no Lean options: each module's
part of the challenge does. And why it cannot be written: a package required by path. -/
def lakefile (required : Array Require) : String × Option String := Id.run do
  let mut reqs : Array String := #[]
  let mut byPath : Array String := #[]
  for r in required.filter (·.name != leanblamePackage) do
    match r.git with
    | some git => reqs := reqs.push <| "\n".intercalate <| ["[[require]]", s!"name = {tomlString r.name}",
        s!"git = {tomlString git}"] ++ (r.rev.map (s!"rev = {tomlString ·}")).toList ++
        (r.subDir.map (s!"subDir = {tomlString ·}")).toList
    | none => byPath := byPath.push s!"{r.name} is required by path; a challenge requires it by git"
  let text := "\n\n".intercalate (["name = \"challenge\""] ++ reqs.toList ++
    ["ChallengeDeps", "Challenge"].map (s!"[[lean_lib]]\nname = \"{·}\"")) ++ "\n"
  return (text, if byPath.isEmpty then none else some ("; ".intercalate byPath.toList))

/-- A piece while `make` builds the graph. `deps`: in `ChallengeDeps.lean`, else in `Challenge.lean`. -/
inductive Key where
  | lakefile
  | toolchain
  /-- `import M`, for a module from outside the library. -/
  | outside (m : Name)
  /-- `namespace N end N`, for an `open N`. -/
  | declare (n : Name)
  /-- `import ChallengeDeps`. -/
  | importDeps
  /-- The `section` of module `m`, which first sets the Lean options Lake builds `m` with. -/
  | head (deps : Bool) (m : Name)
  /-- Command `i` of module `m`, as written. -/
  | cmd (deps : Bool) (m : Name) (i : Nat)
  /-- The `attribute` command `i` of module `m`, for its `a`-th name alone. -/
  | attr (m : Name) (i a : Nat)
  /-- The instances of module `m`, which come with its declarations; no text of its own. -/
  | instances (m : Name)
  /-- The statement of the tagged theorem `t`. -/
  | statement (t : Name)
  /-- The `end` of scope `s` of module `m`, which `m` leaves open. -/
  | close (deps : Bool) (m : Name) (s : Nat)
  /-- The `end` of the `section` of module `m`. -/
  | tail (deps : Bool) (m : Name)
  deriving BEq, Hashable, Inhabited

def Key.file : Key → String
  | .lakefile => lakefileFile
  | .toolchain => toolchainFile
  | .importDeps | .statement _ => challengeFile
  | .head d _ | .cmd d _ _ | .close d _ _ | .tail d _ => if d then depsFile else challengeFile
  | .outside _ | .declare _ | .attr .. | .instances _ => depsFile

/-- The piece graph of the tagged theorems `theorems` of the library (`library`, in import order;
sources on `srcPath`; Lean options from `options`): every piece their statements need, what those
need, and so on. A challenge's lakefile requires what the library's requires (`required`); its
toolchain is the library's (`toolchain`). -/
def make (env : Environment) (library : Array Name) (srcPath : SearchPath) (options : Name → Options)
    (theorems : Array Name) (required : Array Require) (toolchain : String) : IO Graph := do
  let libSet : NameSet := library.foldl (·.insert ·) {}
  let moduleOf (n : Name) : Option Name := do
    let i ← env.getModuleIdxFor? n
    let m ← env.header.moduleNames[i.toNat]?
    if libSet.contains m then some m else none
  -- Each module read once; `fresh`: those read since `make` last looked at their `attribute` commands.
  let reads ← IO.mkRef ({} : Std.HashMap Name (Except String Read))
  let fresh ← IO.mkRef (#[] : Array Name)
  let readOf (m : Name) : IO (Except String Read) := do
    if let some r := (← reads.get)[m]? then return r
    let r ← try
        let some file ← srcPath.findWithExt "lean" m | throw <| .userError s!"cannot find the source of {m}"
        pure (.ok (← readModule env (options m) libSet m file ((← findOLean m).withExtension "ilean")))
      catch e => pure (.error (toString e))
    reads.modify (·.insert m r)
    fresh.modify (·.push m)
    return r
  -- A module that holds a piece reads.
  let readOk (m : Name) : IO Read := do
    match ← readOf m with
    | .ok r => return r
    | .error e => fail e
  let scopesRef ← IO.mkRef ({} : Std.HashMap Name Scopes)
  let scopesIn (m : Name) : IO Scopes := do
    if let some s := (← scopesRef.get)[m]? then return s
    let s := scopesOf (← readOk m)
    scopesRef.modify (·.insert m s)
    return s
  -- The piece that declares the library's constant `n`, or why none does; `none` for a constant
  -- from outside the library.
  let ownerOf (n : Name) : IO (Option (Except String Key)) := do
    if isReservedName env n then return none
    let some m := moduleOf n | return none
    return some <| match ← readOf m with
      | .error e => .error e
      | .ok r => match r.owner.find? n with
        | some i => .ok (.cmd true m i)
        | none => .error s!"{n}: no command of {m} declares it"
  -- The pieces that declare the constants `ns`, but `self`, and why some have none.
  let declarers (self : Option Key) (ns : Array Name) : IO (Array Key × Array String) := do
    let mut keys : Array Key := #[]
    let mut problems : Array String := #[]
    for n in dedup ns do
      match ← ownerOf n with
      | some (.ok k) => if some k != self then keys := keys.push k
      | some (.error e) => problems := problems.push e
      | none => pure ()
    return (dedup keys, problems)
  -- The namespaces that modules from outside the library make, each with those modules.
  let makersRef ← IO.mkRef (none : Option (Std.HashMap Name (Array Name)))
  let makers : IO (Std.HashMap Name (Array Name)) := do
    if let some x := ← makersRef.get then return x
    let map := (importClosure env library).foldl (init := ({} : Std.HashMap Name (Array Name))) fun map mod =>
      if libSet.contains mod then map else
      match (env.getModuleIdx? mod).bind (env.header.moduleData[·.toNat]?) with
      | none => map
      | some d => d.constNames.foldl (init := map) fun map n =>
        (namespacesOf n {}).foldl (init := map) fun map ns =>
          map.alter ns fun ms => let ms := ms.getD #[]; some (if ms.back? == some mod then ms else ms.push mod)
    makersRef.set (some map)
    return map
  let closures ← IO.mkRef ({} : Std.HashMap Name NameSet)
  let closureOf (m : Name) : IO NameSet := do
    if let some c := (← closures.get)[m]? then return c
    let c := importClosure env #[m]
    closures.modify (·.insert m c)
    return c
  -- Of the namespaces an `open` of module `m` opens, those that no module from outside the library
  -- which `m` imports makes.
  let undeclared (m : Name) (opened : Array Name) : IO (Array Name) := do
    if opened.isEmpty then return #[]
    let mk ← makers
    let cl ← closureOf m
    return opened.filter fun ns => !((mk[ns]?).getD #[]).any cl.contains
  let importsOf (m : Name) : Array Name :=
    (((env.getModuleIdx? m).bind (env.header.moduleData[·.toNat]?)).map (·.imports.map (·.module))).getD #[]
  -- What module `m` imports from outside the library, through the library's modules it imports; not
  -- `Init`, which every file imports, nor LeanBlame, which a challenge leaves out.
  let outsideOf (m : Name) : Array Name := Id.run do
    let mut out := #[]
    let mut seen : NameSet := {}
    let mut todo := #[m]
    while h : todo.size > 0 do
      let x := todo[todo.size - 1]
      todo := todo.pop
      if seen.contains x then continue
      seen := seen.insert x
      for i in importsOf x do
        if libSet.contains i then todo := todo.push i
        else if i != `Init && !(`LeanBlame).isPrefixOf i && !out.contains i then out := out.push i
    return out
  let optionDecls ← getOptionDecls
  -- The Lean options Lake builds module `m` with, as `set_option` commands, and why a file cannot
  -- set some.
  let optionsOf (m : Name) : Array String × Array String := Id.run do
    let mut lines := #[]
    let mut problems := #[]
    for (k, v) in options m do
      if (optionDecls.find? k).any fun d => (moduleOf d.declName).isSome then
        problems := problems.push s!"{m}: the library itself declares Lean option {k}, which a challenge file cannot set"
      match v with
      | .ofBool b => lines := lines.push s!"set_option {k} {b}"
      | .ofNat n => lines := lines.push s!"set_option {k} {n}"
      | .ofString v => lines := lines.push s!"set_option {k} {v.quote}"
      | _ => problems := problems.push s!"{m}: Lean option {k} has a value `set_option` cannot write"
    return (lines, problems)
  let (lakeText, lakeProblem) := lakefile required
  -- Where each tagged theorem is written.
  let mut written : Std.HashMap Name (Name × Nat) := {}
  for t in theorems do
    let some m := moduleOf t | continue
    let .ok r ← readOf m | continue
    if let some i := r.owner.find? t then written := written.insert t (m, i)
  let statementAt : Std.HashMap (Name × Nat) Name := written.fold (init := {}) fun acc t place => acc.insert place t
  -- What piece `k` needs, and why a challenge that holds it cannot be made.
  let step (k : Key) : IO (Array Key × Array String) := do
    match k with
    | .lakefile => return (#[], lakeProblem.toArray)
    | .toolchain | .outside _ | .declare _ | .importDeps | .tail .. => return (#[], #[])
    | .head deps m => return (((outsideOf m).map Key.outside).push (.tail deps m), (optionsOf m).2)
    | .instances m =>
      let r ← readOk m
      return (((Array.range r.cmds.size).filter (r.instances[·]!)).map (Key.cmd true m ·), #[])
    | .close deps m s => return (#[.cmd deps m (← scopesIn m).scopes[s]!.1], #[])
    | .cmd deps m i =>
      let r ← readOk m
      let sc ← scopesIn m
      let c := r.cmds[i]!
      let mut needs := #[Key.head deps m] ++ sc.context[i]!.map (Key.cmd deps m ·)
      -- The other end of each scope it opens or closes.
      for (o, _, e) in sc.scopes, s in [:sc.scopes.size] do
        if o == i then needs := needs.push (match e with | some e => .cmd deps m e | none => .close deps m s)
        if e == some i then needs := needs.push (.cmd deps m o)
      needs := needs ++ (← undeclared m c.opened).map Key.declare
      if deps && !c.declares.isEmpty then needs := needs.push (.instances m)
      let (keys, problems) ← declarers (some (.cmd true m i)) (c.declares.flatMap (termUses env · true) ++ r.named c)
      return (needs ++ keys, problems)
    | .attr m i a =>
      let r ← readOk m
      let c := r.cmds[i]!
      let attrEnd := ((innermost c.stx)[3].getTailPos?).getD c.stop
      let (keys, problems) ← declarers none (r.named c attrEnd ++ (r.target? c a).toArray)
      return (#[Key.head true m] ++ (← scopesIn m).context[i]!.map (Key.cmd true m ·) ++ keys, problems)
    | .statement t =>
      let base := #[Key.importDeps, .lakefile, .toolchain]
      let some m := moduleOf t | return (base, #[s!"{t} is a theorem of another library: its challenge is that library's"])
      let r ← match ← readOf m with
        | .ok r => pure r
        | .error e => return (base, #[e])
      let some i := r.owner.find? t | return (base, #[s!"{t}: no command of {m} declares it"])
      let c := r.cmds[i]!
      let some p := proofOf? (innermost c.stx) | return (base, #[s!"{t}: its command has no proof to replace by `sorry`"])
      let (some a, some _) := (p.getPos?, p.getTailPos?) | return (base, #[s!"{t}: its proof has no position"])
      -- A proof inside the statement may make constants of the command (`second_site._proof_1`):
      -- the statement makes them again.
      let (keys, problems) ← declarers none ((termUses env t false ++ r.named c a).filter (r.owner.find? · != some i))
      return (base.push (.head false m) ++ (← scopesIn m).context[i]!.map (Key.cmd false m ·) ++ keys, problems)
  -- Every piece the statements need, what those need, and so on. An `attribute` command comes with
  -- the declaration it names, or, for a constant from outside the library, with its module's
  -- `section`s: the commands of a module are known once the module is read.
  let mut visited : Std.HashMap Key (Array Key × Array String) := {}
  let mut attributes : Std.HashMap Name (Array (Nat × Nat × Option Name)) := {}
  let mut attrsOn : Std.HashMap Name (Array Key) := {}
  let mut attrsIn : Std.HashMap Name (Array Key) := {}
  let mut declared : NameSet := {}
  let mut todo : Array Key := theorems.map Key.statement
  while h : todo.size > 0 do
    let k := todo[todo.size - 1]
    todo := todo.pop
    if visited.contains k then continue
    let (needs, problems) ← step k
    visited := visited.insert k (needs, problems)
    todo := todo ++ needs
    match k with
    | .cmd true m i =>
      for n in (← readOk m).cmds[i]!.declares do
        declared := declared.insert n
        todo := todo ++ attrsOn.getD n #[]
    | .head _ m => todo := todo ++ attrsIn.getD m #[]
    | _ => pure ()
    for m in ← fresh.swap #[] do
      let .ok r ← readOf m | continue
      let found := attributesOf r
      attributes := attributes.insert m found
      for (i, a, target) in found do
        let x := Key.attr m i a
        match target with
        | some n =>
          attrsOn := attrsOn.alter n fun xs => some ((xs.getD #[]).push x)
          if declared.contains n then todo := todo.push x
        | none =>
          attrsIn := attrsIn.alter m fun xs => some ((xs.getD #[]).push x)
          if visited.contains (.head true m) || visited.contains (.head false m) then todo := todo.push x
  -- What comes with piece `k`.
  let comesWith (k : Key) : IO (Array Key) := do
    match k with
    | .cmd true m i => return (← readOk m).cmds[i]!.declares.flatMap (attrsOn.getD · #[])
    | .head _ m => return attrsIn.getD m #[]
    | _ => return #[]
  -- One file holds the pieces of several modules, and Lean names a private declaration after its
  -- module: a private declaration whose name a declaration of another module in the graph has too is
  -- written with its module (`withModule`); what Lean makes with it follows its name.
  let mut byName : Std.HashMap Name (Array (Name × Name)) := {}
  for (k, _) in visited do
    if let .cmd true m i := k then
      for n in (← readOk m).cmds[i]!.declares do
        byName := byName.alter (privateToUserName n) fun ds => some ((ds.getD #[]).push (m, n))
  let mut clashing : NameMap Name := {}
  for (_, ds) in byName do
    if ds.any (·.1 != ds[0]!.1) then
      for (m, n) in ds do
        if isPrivateName n then clashing := clashing.insert n m
  let mut renamed : NameMap String := {}
  for (n, m) in clashing do
    if under clashing n.getPrefix then continue
    if let .str _ s := privateToUserName n then renamed := renamed.insert n (withModule s m)
  -- The pieces in the order of their files: the lakefile and the toolchain; `ChallengeDeps.lean`: its
  -- imports, the namespaces it declares, then each module's part; `Challenge.lean`: its import, then
  -- each module's part. A statement that no module's part holds (it has a problem) is last.
  let has := visited.contains
  let sortedBy (f : Key → Option Name) : Array Name :=
    (visited.toArray.filterMap (f ·.1)).qsort (·.toString < ·.toString)
  let mut order : Array Key := #[.lakefile, .toolchain]
  order := order ++ (sortedBy fun | .outside x => some x | _ => none).map Key.outside
  order := order ++ (sortedBy fun | .declare x => some x | _ => none).map Key.declare
  for deps in [true, false] do
    unless deps do order := order.push .importDeps
    for m in library do
      unless has (.head deps m) do continue
      let r ← readOk m
      let sc ← scopesIn m
      let attrs := attributes.getD m #[]
      order := order.push (.head deps m)
      if deps then order := order.push (.instances m)
      for i in [:r.cmds.size] do
        order := order.push (.cmd deps m i)
        if deps then order := order ++ (attrs.filter (·.1 == i)).map fun (_, a, _) => Key.attr m i a
        else if let some t := statementAt[(m, i)]? then order := order.push (.statement t)
      for s in (List.range sc.scopes.size).reverse do order := order.push (.close deps m s)
      order := order.push (.tail deps m)
  let placed : Std.HashSet Key := order.foldl (·.insert ·) {}
  order := (order ++ (theorems.map Key.statement).filter (!placed.contains ·)).filter has
  unless order.size == visited.size do fail "a piece of the graph has no place in a challenge's files"
  let index : Std.HashMap Key Nat := order.foldl (init := {}) fun acc k => acc.insert k acc.size
  -- Texts: a piece on lines of its own after a blank line; an import on one line.
  let editsRef ← IO.mkRef ({} : Std.HashMap (Name × Nat) (Array Edit))
  let editsOf (m : Name) (i : Nat) : IO (Array Edit) := do
    if let some es := (← editsRef.get)[(m, i)]? then return es
    let r ← readOk m
    let es ← changes r r.cmds[i]! renamed
    editsRef.modify (·.insert (m, i) es)
    return es
  let theoremSet : NameSet := theorems.foldl (·.insert ·) {}
  let mut pieces := #[]
  for k in order do
    let (needs, problems) := visited.getD k (#[], #[])
    let needs ← (dedup (needs ++ (← comesWith k))).mapM fun n => match index[n]? with
      | some j => pure j
      | none => fail "a piece needs a piece the graph lacks"
    let text ← match k with
      | .lakefile => pure lakeText
      | .toolchain => pure s!"leanprover/lean4:{toolchain}\n"
      | .outside x => pure s!"import {x}\n"
      | .declare n => pure s!"\nnamespace {n}\nend {n}\n"
      | .importDeps => pure "import ChallengeDeps\n"
      | .instances _ => pure ""
      | .head _ m => pure ("\n" ++ "\n".intercalate ("section" :: (optionsOf m).1.toList) ++ "\n")
      | .tail .. => pure "\nend\n"
      | .close _ m s => do
        let h := (← scopesIn m).scopes[s]!.2.1
        pure (if h.isEmpty then "\nend\n" else s!"\nend {h}\n")
      | .cmd _ m i => do
        let r ← readOk m
        let c := r.cmds[i]!
        pure ("\n" ++ apply r.bytes c.start c.stop (← editsOf m i) ++ "\n")
      | .attr m i a => do
        let r ← readOk m
        let c := r.cmds[i]!
        let d := innermost c.stx
        let es ← editsOf m i
        let (some attrEnd, some s, some e) := (d[3].getTailPos?, d[4][a].getPos?, d[4][a].getTailPos?)
          | fail s!"{m}: an `attribute` command without positions"
        pure ("\n" ++ apply r.bytes c.start attrEnd es ++ " " ++ apply r.bytes s e es ++ "\n")
      | .statement t => do
        let some (m, i) := written[t]? | pure ""
        let r ← readOk m
        pure (((statementOf? r r.cmds[i]! (← editsOf m i)).map ("\n" ++ · ++ "\n")).getD "")
    let tagged ← match k with
      | .statement t => pure (some t.toString)
      | .cmd true m i => pure (((← readOk m).cmds[i]!.declares.find? theoremSet.contains).map toString)
      | _ => pure none
    pieces := pieces.push { file := k.file, text, needs, tagged
                            problem := if problems.isEmpty then none else some ("; ".intercalate (dedup problems).toList) }
  return { pieces }

end LeanBlame.Pieces
