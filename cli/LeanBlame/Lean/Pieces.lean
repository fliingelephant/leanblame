/-
Challenge pieces (docs/design/04-architecture.md, "Challenges"): the parts of the library's
source that comparator challenges for its tagged declarations are made of, taken as written;
nothing is elaborated again.

What is needed comes from the kernel: what the statements of the tagged theorems reach, every other
tagged declaration, and then everything those reach, proofs included, since `sorry` there would
reach every proof of a statement that uses them. Where it is written comes from Lean: its parser
cuts each module that holds something needed into commands, and its declaration ranges say which
command declares which constant. A piece is one command, as written: a needed declaration; an
instance of a module that has a needed declaration, since Lean uses instances without naming them;
an `attribute` command on needed declarations; or a command that sets the scope of a kept
declaration after it (`namespace`, `section`, `end`, `open`, `variable`, `universe`, `set_option`,
`include`, `omit`, local attributes). A declaration needs the library's constants in its kernel terms
and every name in its text that Lean's record of the build (the module's `.ilean`) says refers to
one, so that a lemma given to `simp` but not used counts too.

The pieces go into one file (`ChallengeDeps.lean`, as lean-eval has it), where a name could read
differently: another module's declaration, or its imports, may share it. So each recorded name is
checked to read back as the constant it named, in the scope it was written in, among everything the
library imports (Lean's name resolution); a name that would not is written as Lean writes names
(`unresolveNameGlobal`). An `open` needs its namespace to exist: one that no piece before it
makes, and no constant of the modules the challenge imports, is declared first (`namespace N end N`);
declaring one that exists changes nothing.
Lean names a private declaration after its module: one whose name a kept declaration of another
module has too is written with its module (`«secret (M)»`). Each module's pieces sit in a `section`
of their own that first sets the Lean options Lake builds the module with. Module-system words
(`public`, `meta`, `@[expose]`) and the `trusted` attribute are dropped: a challenge is a plain file
that does not import LeanBlame. A tagged theorem's piece also has its statement: its text with the
proof replaced by `sorry`, for `Challenge.lean`.

What stops a challenge is recorded, not an error of `export`: a tagged theorem that what every
challenge holds uses (every challenge holds its proof), a declaration no command declares, a module
that does not read, a Lean option a file cannot set. `challenge` refuses what it stops.
-/
import Lean
import Lean.Server.References
import LeanBlame.Core.Store

namespace LeanBlame.Pieces

open Lean Elab

/-- A tagged theorem, and its command with the proof replaced by `sorry`. -/
structure Statement where
  name : String
  text : String
  deriving Inhabited

/-- One command of a module that a challenge needs, as written (docs/design/04-architecture.md,
"Challenges"). `ChallengeDeps.lean` holds every piece without a statement; `Challenge.lean` repeats
the scope commands (`scope`: `namespace`, `section`, `end`, `open`, `variable` and the like) around
the statements. -/
structure Piece where
  text : String
  scope : Bool
  statement : Option Statement
  deriving Inhabited

/-- The pieces of one module, in source order, in a `section` of their own (which first declares
the namespaces its `open`s need) closed by an `end` for each scope it leaves open, so that it can sit
in a file that merges modules. -/
structure Module where
  module : String
  pieces : Array Piece
  deriving Inhabited

instance : ToJson Statement where
  toJson s := Json.mkObj [("name", s.name), ("text", s.text)]

instance : ToJson Piece where
  toJson p := Json.mkObj [("text", p.text), ("scope", p.scope), ("statement", toJson p.statement)]

instance : ToJson Module where
  toJson m := Json.mkObj [("module", m.module), ("pieces", toJson m.pieces)]

def Statement.fromJson? (j : Json) : Except String Statement := do
  let o ← JsonObj.read j "statement" ["name", "text"]
  return { name := ← o.get String "name", text := ← o.get String "text" }

def Piece.fromJson? (j : Json) : Except String Piece := do
  let o ← JsonObj.read j "piece" ["text", "scope", "statement"]
  let statement ← match ← o.get Json "statement" with
    | .null => pure none
    | s => some <$> Statement.fromJson? s
  return { text := ← o.get String "text", scope := ← o.get Bool "scope", statement }

def Module.fromJson? (j : Json) : Except String Module := do
  let o ← JsonObj.read j "pieces" ["module", "pieces"]
  return { module := ← o.get String "module", pieces := ← (← o.get (Array Json) "pieces").mapM Piece.fromJson? }

def read (root : System.FilePath) (hash : String) : IO Module := do
  let p := Store.objectPath root .pieces hash
  unless ← p.pathExists do fail s!"pieces {hash} are not in the store"
  match Json.parse (← IO.FS.readFile p) >>= Module.fromJson? with
  | .ok m => return m
  | .error e => fail s!"{p}: {e}"

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
    let closes := if role != .closes then 0 else match d[1].getOptional? with
      | some i => i.getId.components.length | none => 1
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
    -- The longest name recorded from here; a shorter one is the head of a dotted name (`h.symm`).
    let found := r.refs.filter fun (s, e, _) => s == a && e.byteIdx ≤ b.byteIdx
    let longest := found.foldl (init := none) fun best x =>
      match best with
      | some y => if x.2.1.byteIdx > y.2.1.byteIdx then some x else best
      | none => some x
    let some (_, e, n) := longest | return
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

/-! ## What a challenge needs -/

/-- A scope command that `make` writes itself. -/
def scopeOnly (text : String) : Piece :=
  { text, scope := true, statement := none }

/-- `ns` and every prefix of it. -/
def prefixesOf : Name → NameSet → NameSet
  | .anonymous, acc => acc
  | p@(.str q _), acc | p@(.num q _), acc => prefixesOf q (acc.insert p)

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

/-- The scope commands that the kept commands `ks` of `r` need: each command that sets the scope of
one before it, and the `namespace` or `section` and its `end` around one. A command that opens or
closes several scopes (`namespace A.B`, `end A.B`) is needed for each, so with the other scopes it
opens or closes. -/
def scopeOf (r : Read) (ks : Std.HashSet Nat) : Array Nat := Id.run do
  -- Each scope: the commands that open and close it, and whether a kept command is in it. For the
  -- scopes open now, the file's first: the `sets` commands not yet followed by a kept command.
  let mut scopes : Array (Nat × Option Nat × Bool) := #[]
  let mut stack : Array Nat := #[]
  let mut sets : Array (Array Nat) := #[#[]]
  let mut out := #[]
  for c in r.cmds, i in [:r.cmds.size] do
    match c.role with
    | .opens =>
      for _ in [:c.opens.size] do
        stack := stack.push scopes.size
        scopes := scopes.push (i, none, false)
        sets := sets.push #[]
    | .closes =>
      for _ in [:c.closes] do
        let some k := stack.back? | break
        stack := stack.pop
        sets := sets.pop
        scopes := scopes.modify k fun (o, _, u) => (o, some i, u)
    | .sets => sets := sets.modify (sets.size - 1) (·.push i)
    | _ =>
      if ks.contains i then
        out := sets.foldl (· ++ ·) out
        sets := sets.map fun _ => #[]
        for k in stack do scopes := scopes.modify k fun (o, e, _) => (o, e, true)
  let mut need : Std.HashSet Nat := {}
  let mut grew := true
  while grew do
    grew := false
    for (o, e, used) in scopes do
      if (used || need.contains o || e.any need.contains) && !(need.contains o && e.all need.contains) then
        need := e.toArray.foldl (·.insert ·) (need.insert o)
        grew := true
  return out ++ need.toArray

/-- The pieces of every module of the library (`library`, in import order; sources on `srcPath`,
Lean options from `options`) that holds something the tagged declarations (`tagged`, each with
whether it is a theorem) need, each module with its pieces; and why a challenge cannot be made, of
one tagged theorem or of any. -/
def make (env : Environment) (library : Array Name) (srcPath : SearchPath) (options : Name → Options)
    (tagged : Array (Name × Bool)) : IO (Array Module × Array Store.ChallengeProblem) := do
  let libSet : NameSet := library.foldl (·.insert ·) {}
  let moduleOf (n : Name) : Option Name := do
    let i ← env.getModuleIdxFor? n
    let m ← env.header.moduleNames[i.toNat]?
    if libSet.contains m then some m else none
  let problems ← IO.mkRef (#[] : Array Store.ChallengeProblem)
  -- A problem of the challenge of the tagged theorem `t`, or (`none`) of every challenge.
  let problem (t : Option Name) (text : String) : IO Unit :=
    problems.modify fun ps => let p : Store.ChallengeProblem := { name := t.map toString, problem := text }
      if ps.contains p then ps else ps.push p
  let reads ← IO.mkRef ({} : Std.HashMap Name (Except String Read))
  let readOf (m : Name) : IO (Except String Read) := do
    if let some r := (← reads.get)[m]? then return r
    let r ← try
        let some file ← srcPath.findWithExt "lean" m | throw <| .userError s!"cannot find the source of {m}"
        pure (.ok (← readModule env (options m) libSet m file ((← findOLean m).withExtension "ilean")))
      catch e => pure (.error (toString e))
    reads.modify (·.insert m r)
    return r
  -- The commands kept for `ChallengeDeps.lean`; those of tagged theorems, for `Challenge.lean`.
  let mut kept : Std.HashMap Name (Std.HashSet Nat) := {}
  let mut stated : Std.HashMap Name (Std.HashMap Nat Name) := {}
  let mut todo : Array Name := #[]
  for (t, isTheorem) in tagged do
    let some m := moduleOf t | continue
    -- What stops a tagged theorem's statement stops its challenge; any other tagged declaration is
    -- in every challenge.
    let whose := if isTheorem then some t else none
    match ← readOf m with
    | .error e => problem whose e
    | .ok r =>
      match r.owner.find? t with
      | none => problem whose s!"{t}: no command of {m} declares it"
      | some i =>
        if isTheorem then
          stated := stated.alter m fun s => some ((s.getD {}).insert i t)
          let c := r.cmds[i]!
          let headerEnd := ((proofOf? (innermost c.stx)).bind (·.getPos?)).getD c.stop
          -- A proof inside the statement may make constants of the command (`second_site._proof_1`):
          -- the statement makes them again.
          todo := todo ++ (termUses env t false ++ r.named c headerEnd).filter (r.owner.find? · != some i)
        else todo := todo.push t
  let mut seen : NameSet := {}
  let mut more := true
  while more do
    more := false
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if seen.contains n || isReservedName env n then continue
      seen := seen.insert n
      let some m := moduleOf n | continue
      match ← readOf m with
      | .error e => problem none e
      | .ok r =>
        match r.owner.find? n with
        | none => problem none s!"{n}: no command of {m} declares it"
        | some i =>
          let had := kept.getD m {}
          unless had.contains i do
            -- A module that gives a challenge something gives it its instances too.
            let add := if had.isEmpty then #[i] ++ (Array.range r.cmds.size).filter (r.instances[·]!) else #[i]
            for j in add do
              if (kept.getD m {}).contains j then continue
              kept := kept.alter m fun s => some ((s.getD {}).insert j)
              let c := r.cmds[j]!
              todo := todo ++ c.declares.flatMap (termUses env · true) ++ r.named c
    for (m, r) in ← reads.get do
      let .ok r := r | continue
      let ks := (stated.getD m {}).fold (fun ks i _ => ks.insert i) (kept.getD m {})
      if ks.isEmpty then continue
      for j in scopeOf r ks do
        if (kept.getD m {}).contains j then continue
        kept := kept.alter m fun s => some ((s.getD {}).insert j)
        let named := r.named r.cmds[j]!
        unless named.isEmpty do
          todo := todo ++ named
          more := true
  let read : Std.HashMap Name Read := (← reads.get).fold (init := {}) fun acc m r =>
    match r with | .ok r => acc.insert m r | .error _ => acc
  -- A tagged theorem that what every challenge holds uses is there with its proof: it has no
  -- challenge of its own.
  for (m, ss) in stated.toArray do
    for (i, t) in ss.toArray do
      if (kept.getD m {}).contains i then
        problem (some t) "a declaration that every challenge holds uses it, so every challenge holds its proof"
        stated := stated.modify m (·.erase i)
  -- One file holds the pieces of every module, and Lean names a private declaration after its
  -- module: a private declaration whose name a kept declaration of another module has too is
  -- written with its module (`withModule`); what Lean makes with it follows its name.
  let mut byName : Std.HashMap Name (Array (Name × Name)) := {}
  for (m, r) in read do
    for i in kept.getD m {} do
      for n in r.cmds[i]!.declares do
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
  -- What the kept commands declare: an `attribute` command on these alone comes along.
  let mut declared : NameSet := {}
  for (m, r) in read do
    for i in kept.getD m {} do
      declared := r.cmds[i]!.declares.foldl (·.insert ·) declared
  -- The namespaces that the modules outside the library which the challenge imports make: those
  -- exist wherever the challenge is.
  let outside ← IO.mkRef (none : Option NameSet)
  let isOutside (ns : Name) : IO Bool := do
    if let some set := ← outside.get then return set.contains ns
    let imported := importClosure env (library.filter fun m => kept.contains m || stated.contains m)
    let set := imported.foldl (init := {}) fun acc m =>
      if libSet.contains m then acc else
      match (env.getModuleIdx? m).bind (env.header.moduleData[·.toNat]?) with
      | some d => d.constNames.foldl (fun acc n => namespacesOf n acc) acc
      | none => acc
    outside.set (some set)
    return set.contains ns
  let optionDecls ← getOptionDecls
  -- The namespaces the challenge has made so far, file order.
  let mut made : NameSet := {}
  let mut out := #[]
  for m in library do
    let some r := read[m]? | continue
    let ks := kept.getD m {}
    let ss := stated.getD m {}
    if ks.isEmpty && ss.isEmpty then continue
    -- The Lean options Lake builds the module with, set for its pieces.
    let mut setOptions := #[]
    for (k, v) in options m do
      if (optionDecls.find? k).any fun d => (moduleOf d.declName).isSome then
        problem none s!"{m}: the library itself declares Lean option {k}, which a challenge file cannot set"
      match v with
      | .ofBool b => setOptions := setOptions.push s!"set_option {k} {b}"
      | .ofNat n => setOptions := setOptions.push s!"set_option {k} {n}"
      | .ofString v => setOptions := setOptions.push s!"set_option {k} {v.quote}"
      | _ => problem none s!"{m}: Lean option {k} has a value `set_option` cannot write"
    let mut pieces := #[]
    let mut scopes : Array String := #[]
    let mut declare : Array Name := #[]
    for c in r.cmds, i in [:r.cmds.size] do
      let onKept := c.role == .attribute && !(attributesKept (innermost c.stx)).isEmpty &&
        (r.named c).all declared.contains
      unless ks.contains i || ss.contains i || onKept do continue
      let es ← changes r c renamed
      let statement ← match ss[i]? with
        | some t => match statementOf? r c es with
          | some text => pure (some ({ name := toString t, text } : Statement))
          | none => do problem (some t) "its command has no proof to replace by `sorry`"; pure none
        | none => pure none
      if ss.contains i && statement.isNone then continue
      match c.role with
      | .opens => scopes := scopes ++ c.opens
      | .closes => scopes := scopes.extract 0 (scopes.size - c.closes)
      | _ => pure ()
      -- Lean refuses an `open` of a namespace nothing has made yet.
      for ns in c.opened do
        unless made.contains ns || declare.contains ns || (← isOutside ns) do declare := declare.push ns
      if c.role == .opens && (innermost c.stx).isOfKind ``Parser.Command.namespace then
        made := prefixesOf (c.ns ++ (innermost c.stx)[1].getId) made
      if ks.contains i then
        made := c.declares.foldl (fun made n => namespacesOf n made) made
      pieces := pieces.push { text := apply r.bytes c.start c.stop es, statement
                              scope := c.role == .opens || c.role == .closes || c.role == .sets }
    made := declare.foldl (fun made ns => prefixesOf ns made) made
    -- Each module in a `section` of its own, so that what it opens and sets ends with it: first the
    -- Lean options Lake builds it with, then the namespaces its `open`s need.
    let first := "\n".intercalate ("section" :: setOptions.toList ++ declare.toList.map fun ns => s!"namespace {ns}\nend {ns}")
    let close := scopes.reverse.toList.map (fun h => if h.isEmpty then "end" else s!"end {h}") ++ ["end"]
    out := out.push { module := toString m,
                      pieces := #[scopeOnly first] ++ pieces.push (scopeOnly ("\n".intercalate close)) }
  return (out, ← problems.get)

end LeanBlame.Pieces
