/-
`leanblame export [--boundary FILE] [--lib NAME]...` (docs/design/04-architecture.md).

Builds the libraries with `lake build`, imports their modules, and makes the boundary list: the
declarations tagged `@[trusted "id"]` (own and imported), or named by the blueprint
`--boundary FILE`, plus the members of tagged structures and inductives, with `id`, `parent`,
`module`, `kind`, `role` and the printed statement. Exports the library's constants and the
boundary list with the toolchain's `leanexport` writer (in-process), and writes both files into the
object store, with their graph: the export hashed through the backend
(docs/design/04-architecture.md, "Storage"). Makes the sorried copy of each module (`Sorried`). Then points
`.leanblame/current` at them, with the commit, toolchain and dependencies they were made from.
Prints the two hashes.
-/
import Lean
import Lake.Load.Manifest
import Lake.Toml
import Lake.Util.Git
import LeanExport.Basic
import LeanBlame.Attr
import LeanBlame.Core.Records
import LeanBlame.Core.Walk
import LeanBlame.Lean.Blueprint
import LeanBlame.Lean.Sorried
import LeanBlame.Lean.Source

namespace LeanBlame.Export

open Lean

/-- A declaration put on the boundary by `@[trusted]` or by a blueprint, with its id and its
informal text. -/
structure Tag where
  name : Name
  id : Option String
  /-- In a blueprint: the first declaration of its label, which carries the label as its id. -/
  parent : Option Name := none
  informal : String

/-- Library names: `--lib` flags, else the default `lean_lib` targets of `lakefile.toml`. -/
def libraryNames (root : System.FilePath) (requested : Array String) : IO (Array String) := do
  unless requested.isEmpty do return requested
  let path := root / "lakefile.toml"
  unless ← path.pathExists do
    fail "cannot find the library: no lakefile.toml here (for lakefile.lean, pass --lib NAME)"
  let t ← match ← parseToml (← IO.FS.readFile path) path.toString pure with
    | .ok t => pure t
    | .error es => fail s!"{path}: {"; ".intercalate es.toList}"
  let libs ← match t.find? `lean_lib with
    | none => pure #[]
    | some (.array _ vs) => vs.mapM fun
      | .table _ lt => match lt.find? `name with
        | some (.string _ n) => pure n
        | _ => fail s!"{path}: a lean_lib without a name"
      | _ => fail s!"{path}: lean_lib is not a list of tables"
    | some _ => fail s!"{path}: lean_lib is not a list of tables"
  let defaults ← match t.find? `defaultTargets with
    | none => pure #[]
    | some (.array _ vs) => vs.mapM fun
      | .string _ n => pure n
      | _ => fail s!"{path}: defaultTargets is not a list of strings"
    | some _ => fail s!"{path}: defaultTargets is not a list of strings"
  let chosen := if defaults.isEmpty then libs else libs.filter defaults.contains
  if chosen.isEmpty then fail s!"{path} declares no default lean_lib; pass --lib NAME"
  return chosen

/-- The modules of each library, from Lake (`lake query --json LIB:modules`). -/
def libraryModules (root : System.FilePath) (libs : Array String) : IO (Array (String × Array Name)) := do
  let out ← IO.Process.run
    { cmd := "lake", args := #["query", "--json"] ++ libs.map (· ++ ":modules"), cwd := root }
  let lines := (out.lines.toArray.map (·.copy)).filter (!·.trimAscii.isEmpty)
  unless lines.size == libs.size do fail s!"unexpected output from `lake query`: {out}"
  let mut byLib := #[]
  for lib in libs, line in lines do
    let .ok (.arr xs) := Json.parse line | fail s!"unexpected output from `lake query`: {line}"
    let mods ← xs.mapM fun
      | .str m => pure m.toName
      | _ => fail s!"unexpected output from `lake query`: {line}"
    byLib := byLib.push (lib, mods)
  if byLib.all (·.2.isEmpty) then fail "`lake query` reported no modules"
  return byLib

/-- The commit of the git repository holding `root`; an error outside git: a record names the commit it
signs. -/
def gitHead (root : System.FilePath) : IO String := do
  let some rev ← (root : Lake.GitRepo).getHeadRevision?
    | fail "not a git repository with commits: a record names the commit it signs"
  return rev

/-- `rev` when no file under `root` differs from it, tracked or untracked; else `none`, with a
warning: such an export cannot be signed. -/
def commitIfClean (root : System.FilePath) (rev : String) : IO (Option String) := do
  let some changes ← (root : Lake.GitRepo).captureGit? #["status", "--porcelain", "--", "."]
    | fail "`git status` failed"
  if changes.isEmpty then return some rev
  IO.eprintln "warning: uncommitted changes in the library: this export names no commit and cannot be signed"
  return none

/-- From `lake-manifest.json`, which `lake build` writes: the commits of git dependencies (path
dependencies have none), and what the lakefile requires (the packages that are not inherited). -/
def manifestDeps (root : System.FilePath) : IO (Array (String × String) × Array Require) := do
  let some m ← Lake.Manifest.load? (root / "lake-manifest.json")
    | fail "no lake-manifest.json after `lake build`"
  let name (p : Lake.PackageEntry) := p.name.toString (escape := false)
  let deps := m.packages.filterMap fun p => match p.src with
    | .git (rev := rev) .. => some (name p, rev)
    | .path .. => none
  let requires := m.packages.filterMap fun p =>
    if p.inherited then none else some <| match p.src with
      | .git url rev _ subDir? => { name := name p, git := some url, rev := some rev, subDir := subDir?.map toString }
      | .path .. => { name := name p, git := none, rev := none, subDir := none }
  return (deps, requires)

/-- The module defining `n`. (`env.header.moduleNames` would copy the module list on every call.) -/
def moduleOf (env : Environment) (n : Name) : Except String Name :=
  match env.getModuleIdxFor? n with
  | some idx => match env.header.modules[idx.toNat]? with
    | some m => .ok m.module
    | none => .error s!"{n}: no module {idx}"
  | none => .error s!"{n} is in no imported module"

/-- The `@[trusted]` declarations, tagged in any module, own or imported, with their ids and
docstrings; and the problems. Two modules that do not import each other can tag one declaration;
that is refused here. -/
def trustedTags (env : Environment) : IO (Array Tag × Array String) := do
  let mut tags := #[]
  let mut errors := #[]
  let mut taggedIn : NameMap Name := {}
  for (m, t) in (LeanBlame.tags env).qsort (·.2.decl.cmp ·.2.decl == .lt) do
    let (n, id) := (t.decl, t.id)
    if let some m' := taggedIn.find? n then
      errors := errors.push s!"{n}: tagged in {m'} and in {m}; a declaration has one tag"; continue
    taggedIn := taggedIn.insert n m
    let some doc ← findSimpleDocString? env n
      | errors := errors.push s!"{n}: tagged declarations need a docstring (the informal text)"; continue
    let informal := normalizeInformal doc
    if informal.isEmpty then
      errors := errors.push s!"{n}: tagged declarations need a non-empty docstring"; continue
    tags := tags.push { name := n, id, informal }
  return (tags, errors)

/-- The tags of a verso-blueprint manifest (`--boundary FILE`), and the problems. A label is the id
of the first declaration it names; the label's other declarations name that one as their parent. -/
def blueprintTags (f : System.FilePath) : IO (Array Tag × Array String) := do
  let accepted := "--boundary takes a verso-blueprint blueprint-manifest.json"
  let j ← match Json.parse (← IO.FS.readFile f) with
    | .ok j => pure j
    | .error e => fail s!"{f}: {accepted}: {e}"
  unless j.getObjVal? "previews" matches .ok _ do fail s!"{f}: {accepted}"
  let (nodes, errors) ← Blueprint.nodes f j
  let tags := nodes.flatMap fun n =>
    let informal := normalizeInformal n.text
    n.names.mapIdx fun i name => match i with
      | 0 => { name, id := some n.label, informal }
      | _ => { name, id := none, parent := n.names[0]?, informal }
  return (tags, errors)

/-- A declaration of the boundary list while `expand` makes it: its own id, and the declaration
whose id stands for it. -/
structure Entry where
  name : Name
  ci : ConstantInfo
  informal : String
  ownId : Option String
  parent : Option Name

/-- What `n` is, in the words of Lean's documentation (doc-gen4): `def`, `theorem`, `axiom`,
`opaque`, `instance`, `inductive`, `structure`, `class`, `constructor`, and `field` for a structure's
projection. Not hashed: the hash takes the kernel's kind (`Source.kindOf`). -/
def kindWord (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  if env.isProjectionFn n then "field" else
  match ci with
  | .inductInfo _ =>
    if isClass env n then "class" else if isStructure env n then "structure" else "inductive"
  | .ctorInfo _ => "constructor"
  | .defnInfo _ => if Meta.isInstanceCore env n then "instance" else Source.kindOf ci
  | _ => Source.kindOf ci

/-- Where `n` stands in the source: its module's place in the import order (after every module it
imports), then the line and column where it starts. -/
def sourcePlace (env : Environment) (n : Name) : Option (Nat × Nat × Nat) := do
  let idx ← env.getModuleIdxFor? n
  let r ← Sorried.declRange? env n
  return (idx.toNat, r.range.pos.line, r.range.pos.column)

/-- The name of `n` under `root`, the declaration whose id stands for it: `x` for `Sample.Point.x`
under `Sample.Point`; all of `n` when it is not under `root`. -/
def relativeName (root n : Name) : String :=
  if root.isPrefixOf n && root != n then (n.replacePrefix root .anonymous).toString else n.toString

/-- The boundary list's declarations in source order, with their constants: the tagged ones, and the
constructors and projections of tagged inductives and structures that are not tagged themselves, with
their own docstring or else the parent's text. `parent` names the declaration whose id stands for
this one: the first declaration of its blueprint label, else the tagged inductive or structure it is
a constructor or projection of; a parent without an id of its own is passed over for its own
parent. A declaration without an id of its own has the id `<parent's id>/<name under the parent>`.
`module`, `kind` and `role` come from `env`; the statement is filled in by `withStatements`. Source
order is `sourcePlace`'s, a member without a place of its own at its parent's, ties by name. Also the
problems. -/
def expand (env : Environment) (tags : Array Tag) : IO (Array (Name × BoundaryDecl) × Array String) := do
  let tagged : NameSet := tags.foldl (·.insert ·.name) {}
  let members (n : Name) : Array Name := match env.find? n with
    | some (.inductInfo iv) =>
      iv.ctors.toArray ++ (((getStructureInfo? env n).map (·.fieldInfo.map (·.projFn))).getD #[])
    | _ => #[]
  let parentOf : NameMap Name := tags.foldl (init := {}) fun m t =>
    (members t.name).foldl (init := m) fun m c => m.insert c t.name
  let mut entries : Array Entry := #[]
  let mut errors := #[]
  for t in tags do
    let some ci := env.find? t.name
      | errors := errors.push s!"{t.name}: tagged but not in the environment"; continue
    if ci.isUnsafe then
      errors := errors.push s!"{t.name}: `unsafe` declarations cannot be tagged"; continue
    if ci matches .recInfo _ then
      errors := errors.push s!"{t.name}: recursors cannot be tagged"; continue
    entries := entries.push
      { name := t.name, ci, informal := t.informal, ownId := t.id, parent := t.parent <|> parentOf.find? t.name }
    for m in members t.name do
      if tagged.contains m then continue
      let some mi := env.find? m | errors := errors.push s!"{m}: member of {t.name} not found"; continue
      let informal := (((← findSimpleDocString? env m).map normalizeInformal).filter (· != "")).getD t.informal
      entries := entries.push { name := m, ci := mi, informal, ownId := none, parent := some t.name }
  let byName : NameMap Entry := entries.foldl (init := {}) fun m e => m.insert e.name e
  let rec root (fuel : Nat) (p : Name) : Name :=
    match fuel, byName.find? p with
    | fuel + 1, some { ownId := none, parent := some q, .. } => root fuel q
    | _, _ => p
  let mut out := #[]
  -- An id names one declaration: a copied `@[trusted "id"]` is caught here.
  let mut owner : Std.HashMap String Name := {}
  for e in entries do
    let parent := e.parent.map (root entries.size)
    let id? := e.ownId <|> parent.bind fun p =>
      (byName.find? p).bind (·.ownId) |>.map (s!"{·}/{relativeName p e.name}")
    let some id := id?
      | errors := errors.push s!"{e.name}: tagged without an id; run `leanblame id` in the library that tags it"
        continue
    if let some other := owner[id]? then
      errors := errors.push s!"{other} and {e.name} have the same id {id}; remove it from one of them and run `leanblame id`"
    owner := owner.insert id e.name
    let module ← IO.ofExcept (moduleOf env e.name)
    let some place := sourcePlace env e.name <|> parent.bind (sourcePlace env)
      | errors := errors.push s!"{e.name}: Lean has no source position for it"; continue
    let d : BoundaryDecl := {
      name := e.name.toString, id, parent := parent.map (·.toString), module := module.toString
      kind := kindWord env e.name e.ci, role := Source.roleOf e.ci, informal := e.informal, statement := default }
    out := out.push (place, e.name, d)
  let before (a b : (Nat × Nat × Nat) × Name × BoundaryDecl) : Bool :=
    let ((m, l, c), (m', l', c')) := (a.1, b.1)
    if m != m' then m < m' else if l != l' then l < l' else if c != c' then c < c'
    else a.2.2.name < b.2.2.name
  return ((out.qsort before).map (·.2), errors)

/-- The Lean script that prints the statements (docs/design/14-schemas.md §1) of the constants named
in `names`, one per line, as JSON into `out`. It runs in the library with `lake env lean`, so the
library's notations and other environment extensions are loaded as in an editor; this process
cannot load them, since the library imports `LeanBlame.Attr`, which is linked into it. Its
definitions live in their own namespace so that no library name shadows them. The
signature is pretty-printed with every constant reference tagged (`Widget.tagCodeInfos`, the way
doc-gen4 renders signatures) and flattened to segments; a reference prints with its surrounding
spaces (` + ` for `HAdd.hAdd`), which stay outside its segment. A printer error stops `export`. -/
def statementScript (mods : Array Name) (names out : System.FilePath) : String :=
  "import Lean\n" ++ String.join (mods.toList.map fun m => s!"import {m}\n") ++ r#"
open Lean Meta Widget

namespace LeanBlameStatements

def constOf (i : SubexprInfo) : Option Name :=
  match i.info.val.info with
  | .ofTermInfo t => match t.expr.consumeMData with
    | .const n _ => some n
    | _ => none
  | _ => none

def segment (text : String) (const : Option Name := none) : Json :=
  Json.mkObj [("text", Json.str text), ("const", match const with | some c => Json.str c.toString | none => Json.null)]

/-- The text directly under a tag belongs to the constant that tag refers to, if any: the name of a
constant, or the symbol of a notation whose head it is (` = ` for `Eq`). Nested tags decide for
their own text. -/
partial def flatten (cur : Option Name) : CodeWithInfos → Array Json → Array Json
  | .text s, acc =>
    match cur with
    | none => if s.isEmpty then acc else acc.push (segment s)
    | some n =>
      let chars := s.toList
      let lead := chars.takeWhile Char.isWhitespace
      let trail := (chars.reverse.takeWhile Char.isWhitespace).reverse
      let core := String.ofList ((chars.drop lead.length).take (chars.length - lead.length - trail.length))
      let acc := if lead.isEmpty then acc else acc.push (segment (String.ofList lead))
      let acc := if core.isEmpty then acc else acc.push (segment core (some n))
      if trail.isEmpty then acc else acc.push (segment (String.ofList trail))
  | .append xs, acc => xs.foldl (fun acc x => flatten cur x acc) acc
  | .tag i t, acc => flatten (constOf i) t acc

def segments (c : Name) : MetaM Json := do
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppSignature c
  let ctx : Elab.ContextInfo := {
    env := ← getEnv, fileMap := default, mctx := ← getMCtx, options := ← getOptions
    currNamespace := ← getCurrNamespace, openDecls := ← getOpenDecls, ngen := ← getNGen }
  let code ← tagCodeInfos ctx infos (TaggedText.prettyTagged fmt (w := 100))
  return Json.arr (flatten none code #[])

/-- `pp.tagAppFns`: the head of an application gets its own tag, so it becomes a segment. `plain`
is for Lean to read again (a comparator challenge restates theorems with it): no notation, no field
notation, and coercions as the functions they are, since `↑x` alone may not say its target. -/
def statement (c : Name) : MetaM Json := do
  let pretty (o : Options) := o.setBool `pp.tagAppFns true
  let plain (o : Options) := pretty o |>.setBool `pp.notation false |>.setBool `pp.fieldNotation false
    |>.setBool `pp.coercions false
  let under (f : Options → Options) (x : MetaM Json) : MetaM Json :=
    withTheReader Core.Context (fun ctx => { ctx with options := f ctx.options }) x
  return Json.mkObj [("pretty", ← under pretty (segments c)), ("plain", ← under plain (segments c))]

def run (names out : System.FilePath) : MetaM Unit := do
  let mut fields := #[]
  for line in ← IO.FS.lines names do
    let some c := Syntax.decodeNameLit ("`" ++ line) | throwError "not a constant name: {line}"
    fields := fields.push (line, ← statement c)
  IO.FS.writeFile out (Json.mkObj fields.toList).compress

end LeanBlameStatements
"# ++ s!"\n#eval LeanBlameStatements.run {repr names.toString} {repr out.toString}\n"

/-- `declarations` with their statements, printed by `statementScript` in the library. -/
def withStatements (root : System.FilePath) (mods : Array Name)
    (declarations : Array (Name × BoundaryDecl)) : IO (Array (Name × BoundaryDecl)) := do
  let names ← Store.tmpPath root "names"
  let out ← Store.tmpPath root "statements"
  let script ← Store.tmpPath root "statements.lean"
  IO.FS.writeFile names (String.join (declarations.toList.map fun (n, _) => n.toString ++ "\n"))
  IO.FS.writeFile script (statementScript mods names out)
  let r ← IO.Process.output { cmd := "lake", args := #["env", "lean", script.toString], cwd := root }
  let cleanup : IO Unit := do
    for f in [names, out, script] do
      if ← f.pathExists then IO.FS.removeFile f
  if r.exitCode != 0 then
    cleanup
    fail s!"printing the statements failed (exit {r.exitCode}):\n{r.stdout}{r.stderr}"
  let text ← IO.FS.readFile out
  cleanup
  let o ← IO.ofExcept (Json.parse text >>= (JsonObj.read · "printed statements"
    (declarations.toList.map fun (n, _) => n.toString)))
  declarations.mapM fun (n, d) => do
    match o.get Statement n.toString with
    | .ok st => pure (n, { d with statement := st })
    | .error e => fail s!"printing the statements: {e}"

/-- Whether a user could tag `n`, that is, Lean did not generate it (docs/design/03): not a compiler
auxiliary, recursor or recursor derivative, `noConfusion`, matcher, equation lemma or other
reserved name, nor anything Lean's own `isAutoDeclOrPrivate_Internal` counts as generated
(`T.brecOn.go`, `T.ctorIdx`, …). Constructors are tagged with their type. -/
def taggable (n : Name) (ci : ConstantInfo) : CoreM Bool := do
  let env ← getEnv
  if n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n || isRecCore env n ||
      Meta.isMatcherCore env n || ci.isCtor || isReservedName env n then
    return false
  return !(← isAutoDeclOrPrivate_Internal n)

/-- A constant name that reads back from its printed form, as boundary lists name constants. -/
def roundTrips (n : Name) : Bool :=
  Syntax.decodeNameLit ("`" ++ n.toString) == some n

/-- Run the toolchain's exporter on `env` from `roots` into `path`; returns the SHA-256 (hex) of the
bytes, computed as they are written. -/
def dumpToFile (env : Environment) (roots : Array Name) (path : System.FilePath) : IO String := do
  let sha ← IO.mkRef ({} : Sha256.State)
  IO.FS.withFile path .write fun h =>
    let write (b : ByteArray) : IO Unit := do h.write b; sha.modify (·.update b)
    IO.withStdout { IO.FS.Stream.ofHandle h with write, putStr := (write ·.toUTF8) }
      (LeanExport.dumpEnv env (some roots.toList))
  return Sha256.toHex (← sha.get).finish

/-- A built library with its modules imported. -/
structure Loaded where
  libs : Array String
  /-- The modules of each library. -/
  byLib : Array (String × Array Name)
  mods : Array Name
  deps : Array (String × String)
  requires : Array Require
  env : Environment
  /-- Where the sources are (`LEAN_SRC_PATH` of `lake env`). -/
  srcPath : System.SearchPath
  /-- The toolchain (`LEAN_SYSROOT`) and where its `lean` finds the modules (`LEAN_PATH`). -/
  sysroot : System.FilePath
  leanPath : String

/-- Build the libraries of `root` (with the mathlib cache when they depend on mathlib) and import
their modules. -/
def load (root : System.FilePath) (libsGiven : Array String) : IO Loaded := do
  let libs ← libraryNames root libsGiven
  -- docs/design/04: build using the mathlib cache, when `lake-manifest.json` names mathlib.
  if (← Lake.Manifest.load? (root / "lake-manifest.json")).any (·.packages.any (·.name == `mathlib)) then
    IO.eprintln "leanblame: lake exe cache get"
    runToStderr "lake" #["exe", "cache", "get"] root "`lake exe cache get`"
  IO.eprintln s!"leanblame: lake build {" ".intercalate libs.toList}"
  -- The modules are imported from the build directory. With Lake's artifact cache on, a build may
  -- leave them only in the cache unless Lake is asked to restore them.
  runToStderr "lake" (#["build"] ++ libs) root "`lake build`" (env := #[("LAKE_RESTORE_ARTIFACTS", some "true")])
  let (deps, requires) ← manifestDeps root
  let byLib ← libraryModules root libs
  let mods := dedup (byLib.flatMap (·.2))
  let vars := (← IO.Process.run { cmd := "lake", args := #["env", "printenv"], cwd := root }).lines.toArray
  let var (k : String) : IO String := do
    let some v := vars.findSome? fun l => (l.dropPrefix? (k ++ "=")).map (·.copy)
      | fail s!"`lake env printenv` did not report {k}"
    return v
  let sysroot := System.FilePath.mk (← var "LEAN_SYSROOT")
  let leanPath ← var "LEAN_PATH"
  initSearchPath sysroot (System.SearchPath.parse leanPath)
  IO.eprintln s!"leanblame: importing {mods.size} modules of {", ".intercalate libs.toList}"
  let env ← importModules (mods.map fun m => { module := m }) {} (loadExts := false)
  return { libs, byLib, mods, deps, requires, env, srcPath := System.SearchPath.parse (← var "LEAN_SRC_PATH"),
           sysroot, leanPath }

structure Result where
  exportHash : String
  boundary : String
  boundaryList : BoundaryList
  /-- Constants hashed into the claims. -/
  hashed : Nat

/-- Run the export in library root `root`; `backend` hashes it. -/
def run (backend : Core.Backend) (root : System.FilePath) (boundaryFile? : Option System.FilePath)
    (libsGiven : Array String) : IO Result := do
  let rev ← gitHead root
  let ledger ← Ledger.load root
  let { libs, byLib, mods, deps, requires, env, srcPath, sysroot, leanPath } ← load root libsGiven
  -- Checked after the build, which may update `lake-manifest.json`.
  let commit ← commitIfClean root rev
  let toolchain := "v" ++ Lean.versionString
  let (tags, errors) ← match boundaryFile? with
    | some f => blueprintTags f
    | none => trustedTags env
  let (declarations, errors') ← expand env tags
  let problems := errors ++ errors'
  unless problems.isEmpty do
    fail ("export failed:\n" ++ "\n".intercalate (problems.toList.map ("  " ++ ·)))
  IO.eprintln "leanblame: printing statements"
  let declarations ← withStatements root mods declarations
  let boundaryList : BoundaryList := { library := ", ".intercalate libs.toList, declarations := declarations.map (·.2) }
  -- The constants to export: the library's own non-internal constants and the boundary list.
  let mut roots : Array Name := #[]
  let mut own : Array (Name × ConstantInfo) := #[]
  for m in mods do
    let some idx := env.getModuleIdx? m | fail s!"module {m} was not imported"
    let some data := env.header.moduleData[idx.toNat]? | fail s!"module {m} has no data"
    for n in data.constNames do
      -- A name in several modules belongs to the first, as in `moduleOf`.
      unless env.getModuleIdxFor? n == some idx do continue
      let some ci := env.constants.map₁[n]? | fail s!"{n} of module {m} is not in the environment"
      own := own.push (n, ci)
      unless n.isInternal do roots := roots.push n
  -- The library's taggable constants, for `status`'s untagged declarations of this library.
  let owned ← (own.filterMapM fun (n, ci) => return if ← taggable n ci then some n.toString else none).toIO'
    { fileName := "", fileMap := default } { env }
  let modules ← Sorried.make root env byLib (.ofList own.toList) srcPath sysroot leanPath
  for (n, d) in declarations do
    unless roundTrips n do fail s!"{d.name}: this name does not read back from its printed form"
    roots := roots.push n
  roots := (roots.qsort (fun a b => a.cmp b == .lt)).eraseReps
  -- Run the toolchain's exporter on `env`, hashing the bytes as they are written.
  let tmp ← Store.tmpPath root "export"
  IO.eprintln s!"leanblame: leanexport ({roots.size} roots)"
  let exportHash := mkHash (← dumpToFile env roots tmp)
  let boundary ← Store.putString root .boundaries (jsonText boundaryList)
  -- The graph: every claim hash, computed now, as the other commands only read it; a stored graph
  -- of the same export and boundary list has already passed.
  let hashed ← match ← Graph.load? root exportHash boundary boundaryList with
    | some h => pure h
    | none =>
      let h ← try
          let src ← Source.ofExport (← Source.parseFile tmp) fun n => IO.ofExcept (moduleOf env n)
          Walk.hashExport backend src boundaryList exportHash boundary
        catch e => IO.FS.removeFile tmp; fail s!"cannot hash the export: {e}"
      Graph.save root h
      pure h
  discard <| Store.putFile root .exports tmp (hashHex exportHash)
  let ownedHash ← Store.putString root .owned ("\n".intercalate (owned.qsort (· < ·)).toList ++ "\n")
  Store.writeCurrent root
    { exportHash, boundary, owned := ownedHash, modules, commit, toolchain, deps, requires }
  -- Sweep. Exports and boundary lists stay while the current pointer or a record names them, graphs
  -- with their export; copies while the current pointer names them; evidence while its claim is
  -- current; a proof while evidence or a record names it.
  let mut exports : Std.HashSet String := ({} : Std.HashSet String).insert (hashHex exportHash)
  let mut boundaries : Std.HashSet String := ({} : Std.HashSet String).insert (hashHex boundary)
  let mut proofs : Std.HashSet String := {}
  for r in ledger.records do
    if let .approve a := r.record then
      exports := exports.insert (hashHex a.exportHash)
      boundaries := boundaries.insert (hashHex a.boundary)
      for c in a.constants do
        if let some e := c.evidence then proofs := proofs.insert (hashHex e)
  let evidence : Std.HashSet String := hashed.nodes.fold (init := {}) fun acc _ n =>
    if n.informal.isSome then acc.insert s!"{hashHex n.claim}.json" else acc
  let mut removed := (← Store.sweep root .exports exports) + (← Store.sweep root .boundaries boundaries)
  removed := removed + (← Store.sweep root .owned (({} : Std.HashSet String).insert (hashHex ownedHash)))
  removed := removed + (← Store.sweep root .sorried (.ofList (modules.toList.map (s!"{hashHex ·.key}.json"))))
  removed := removed + (← Store.sweepDir (Store.evidenceDir root) evidence)
  removed := removed + (← Store.sweep root .proofs (proofs.union (← Store.evidenceProofs root)))
  Graph.sweep root exports
  if removed > 0 then IO.eprintln s!"leanblame: removed {removed} objects nothing names any more"
  return { exportHash, boundary, boundaryList, hashed := hashed.nodes.size }

end LeanBlame.Export
