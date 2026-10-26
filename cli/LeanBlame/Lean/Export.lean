/-
`leanblame export [--lib NAME]...` (docs/design/04-architecture.md).

Builds the library with `lake build`, imports its modules, and makes the
boundary list: the declarations tagged `@[trusted "id"]` (own and imported),
plus the members of tagged structures and inductives, with `module`, `kind`,
`role`, the printed statement and the provenance fields from the library itself. Exports the library's constants and the boundary list with the
toolchain's `leanexport` writer (in-process), and writes both files into the
object store, with their graph: the export hashed through the backend
(docs/design/15-generic-core.md). Prints the two hashes.
-/
import Lean
import Lake.Load.Manifest
import Lake.Toml
import Lake.Util.Git
import LeanExport.Basic
import LeanBlame.Attr
import LeanBlame.Core.Records
import LeanBlame.Core.Walk
import LeanBlame.Lean.Source

namespace LeanBlame.Export

open Lean

/-- A declaration tagged `@[trusted]`, with its id and its docstring. -/
structure Tag where
  name : Name
  id : Option String
  informal : String

/-- The informal text of a docstring, as docs/design/03 hashes it: ASCII whitespace trimmed, line
endings normalized, no Unicode normalization (Lean core has none). -/
def normalizeInformal (s : String) : String := strTrim s.crlfToLf

/-- Library names: `--lib` flags, else the default `lean_lib` targets of `lakefile.toml`. -/
def libraryNames (root : System.FilePath) (requested : Array String) : IO (Array String) := do
  unless requested.isEmpty do return requested
  let path := root / "lakefile.toml"
  unless ← path.pathExists do
    fail "cannot find the library: no lakefile.toml here (for lakefile.lean, pass --lib NAME)"
  let .ok t ← parseToml (← IO.FS.readFile path) path.toString pure | fail s!"{path}: not valid TOML"
  let libs : Array String := match t.find? `lean_lib with
    | some (.array _ vs) => vs.filterMap fun
      | .table _ lt => match lt.find? `name with
        | some (.string _ n) => some n
        | _ => none
      | _ => none
    | _ => #[]
  let defaults : Array String := match t.find? `defaultTargets with
    | some (.array _ vs) => vs.filterMap fun
      | .string _ n => some n
      | _ => none
    | _ => #[]
  let chosen := if defaults.isEmpty then libs else libs.filter defaults.contains
  if chosen.isEmpty then fail s!"{path} declares no default lean_lib; pass --lib NAME"
  return chosen

/-- The modules of each library, from Lake (`lake query --json LIB:modules`). -/
def libraryModules (root : System.FilePath) (libs : Array String) : IO (Array Name) := do
  let out ← IO.Process.run
    { cmd := "lake", args := #["query", "--json"] ++ libs.map (· ++ ":modules"), cwd := root }
  let mut mods := #[]
  for line in out.lines do
    if line.trimAscii.isEmpty then continue
    match Json.parse line.copy with
    | .ok (.arr xs) =>
      for x in xs do
        if let .str s := x then
          mods := mods.push s.toName
    | _ => fail s!"unexpected output from `lake query`: {line}"
  if mods.isEmpty then fail "`lake query` reported no modules"
  return dedup mods

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

/-- Commits of git dependencies, from `lake-manifest.json`. Path dependencies have none. -/
def manifestDeps (root : System.FilePath) : IO (Array (String × String)) := do
  let some m ← Lake.Manifest.load? (root / "lake-manifest.json") | return #[]
  return m.packages.filterMap fun p => match p.src with
    | .git (rev := rev) .. => some (p.name.toString (escape := false), rev)
    | .path .. => none

/-- The module defining `n`. (`env.header.moduleNames` would copy the module list on every call.) -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.modules[idx.toNat]!.module
  | none => env.mainModule

/-- The `@[trusted]` declarations, own and imported, with their ids and docstrings; and the problems. -/
def trustedTags (env : Environment) : IO (Array Tag × Array String) := do
  let mut tags := #[]
  let mut errors := #[]
  for (n, id) in (trustedDecls env).qsort (·.1.cmp ·.1 == .lt) do
    let some doc ← findSimpleDocString? env n
      | errors := errors.push s!"{n}: tagged declarations need a docstring (the informal text)"; continue
    let informal := normalizeInformal doc
    if informal.isEmpty then
      errors := errors.push s!"{n}: tagged declarations need a non-empty docstring"; continue
    tags := tags.push { name := n, id, informal }
  return (tags, errors)

/-- The boundary list's declarations, sorted by name, with their constants: the tagged ones, and the
constructors and projections of tagged inductives and structures that are not tagged themselves, with
their own docstring or else the parent's text. A constructor or projection of a tagged inductive or
structure names it as `parent`, tagged or not. `module`, `kind` and `role` come from `env`; the
statement is filled in by `withStatements`. Also the problems. -/
def expand (env : Environment) (tags : Array Tag) : IO (Array (Name × BoundaryDecl) × Array String) := do
  let decl (n : Name) (ci : ConstantInfo) (informal : String) (id parent : Option String) :
      Name × BoundaryDecl :=
    (n, { name := n.toString, id, parent, module := (moduleOf env n).toString, kind := Source.kindOf ci,
          role := Source.roleOf ci, informal, statement := default })
  let tagged : NameSet := tags.foldl (·.insert ·.name) {}
  let members (n : Name) : Array Name := match env.find? n with
    | some (.inductInfo iv) =>
      iv.ctors.toArray ++ (((getStructureInfo? env n).map (·.fieldInfo.map (·.projFn))).getD #[])
    | _ => #[]
  let parentOf : NameMap Name := tags.foldl (init := {}) fun m t =>
    (members t.name).foldl (init := m) fun m c => m.insert c t.name
  let mut out := #[]
  let mut errors := #[]
  for t in tags do
    let some ci := env.find? t.name
      | errors := errors.push s!"{t.name}: tagged but not in the environment"; continue
    if ci.isUnsafe then
      errors := errors.push s!"{t.name}: `unsafe` declarations cannot be tagged"; continue
    if ci matches .recInfo _ then
      errors := errors.push s!"{t.name}: recursors cannot be tagged"; continue
    out := out.push (decl t.name ci t.informal t.id ((parentOf.find? t.name).map (·.toString)))
    for m in members t.name do
      if tagged.contains m then continue
      let some mi := env.find? m | errors := errors.push s!"{m}: member of {t.name} not found"; continue
      let informal := (((← findSimpleDocString? env m).map normalizeInformal).filter (· != "")).getD t.informal
      out := out.push (decl m mi informal none (some t.name.toString))
  -- An id names one declaration: a copied `@[trusted "id"]` is caught here.
  let mut owner : Std.HashMap String Name := {}
  for t in tags do
    let some id := t.id | continue
    if let some other := owner[id]? then
      errors := errors.push s!"{other} and {t.name} have the same id {id}; remove it from one of them and run `leanblame id`"
    owner := owner.insert id t.name
  return (out.qsort (·.2.name < ·.2.name), errors)

/-- The Lean script that prints the statements (docs/design/14-schemas.md §1) of the constants named
in `names`, one per line, as JSON into `out`. It runs in the library with `lake env lean`, so the
library's notations and other environment extensions are loaded as in an editor; this process
cannot load them, since the library imports `LeanBlame.Attr`, which is linked into it. Its
definitions live in their own namespace so that no library name shadows them. The
signature is pretty-printed with every constant reference tagged (`Widget.tagCodeInfos`, the way
doc-gen4 renders signatures) and flattened to segments; a reference prints with its surrounding
spaces (` + ` for `HAdd.hAdd`), which stay outside its segment. Should the printer fail on a
constant, its raw type stands in. -/
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
  Json.mkObj <| (const.toList.map fun c => ("const", Json.str c.toString)) ++ [("text", Json.str text)]

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
      let trail := chars.reverse.takeWhile Char.isWhitespace
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

/-- `pp.tagAppFns`: the head of an application gets its own tag, so it becomes a segment. -/
def statement (c : Name) : MetaM Json := do
  let raw : MetaM Json := do return Json.arr #[segment s!"{c} : {(← getConstInfo c).type}"]
  let pretty (o : Options) := o.setBool `pp.tagAppFns true
  let plain (o : Options) := pretty o |>.setBool `pp.notation false |>.setBool `pp.fieldNotation false
  let under (f : Options → Options) (x : MetaM Json) : MetaM Json :=
    withTheReader Core.Context (fun ctx => { ctx with options := f ctx.options }) x
  return Json.mkObj [("pretty", ← under pretty (try segments c catch _ => raw)),
    ("plain", ← under plain (try segments c catch _ => raw))]

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
  let j ← IO.ofExcept (Json.parse text)
  declarations.mapM fun (n, d) => do
    let some sj := (j.getObjVal? n.toString).toOption | fail s!"no statement printed for {n}"
    match Statement.fromJson? sj with
    | .ok st => pure (n, { d with statement := st })
    | .error e => fail s!"{n}: {e}"

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

/-- A constant name that reads back from its printed form, as boundary lists name constants. (Roots
are restricted to these names as when `leanexport` ran as a command, so exports are unchanged.) -/
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
  mods : Array Name
  deps : Array (String × String)
  env : Environment
  /-- Where the sources are (`LEAN_SRC_PATH` of `lake env`). -/
  srcPath : System.SearchPath

/-- Build the library in `root` (with the mathlib cache when it depends on mathlib) and import its
modules. -/
def load (root : System.FilePath) (libsGiven : Array String) : IO Loaded := do
  let deps ← manifestDeps root
  -- docs/design/04: build using the mathlib cache, when the library depends on mathlib.
  if deps.any (·.1 == "mathlib") then
    IO.eprintln "leanblame: lake exe cache get"
    try runToStderr "lake" #["exe", "cache", "get"] root "`lake exe cache get`"
    catch e => IO.eprintln s!"warning: could not fetch the mathlib cache: {e}"
  IO.eprintln "leanblame: lake build"
  -- The modules are imported from the build directory. With Lake's artifact cache on, a build may
  -- leave them only in the cache unless Lake is asked to restore them.
  runToStderr "lake" #["build"] root "`lake build`" (env := #[("LAKE_RESTORE_ARTIFACTS", some "true")])
  let libs ← libraryNames root libsGiven
  let mods ← libraryModules root libs
  let vars := (← IO.Process.run { cmd := "lake", args := #["env", "printenv"], cwd := root }).lines.toArray
  let var (k : String) := vars.findSome? fun l => (l.dropPrefix? (k ++ "=")).map (·.copy)
  let some leanPath := var "LEAN_PATH" | fail "`lake env printenv` did not report LEAN_PATH"
  initSearchPath (← match var "LEAN_SYSROOT" with | some r => pure (System.FilePath.mk r) | none => findSysroot)
    (System.SearchPath.parse leanPath)
  IO.eprintln s!"leanblame: importing {mods.size} modules of {", ".intercalate libs.toList}"
  let env ← importModules (mods.map fun m => { module := m }) {} (loadExts := false)
  let srcPath := System.SearchPath.parse ((var "LEAN_SRC_PATH").getD "")
  return { libs, mods, deps, env, srcPath }

structure Result where
  exportHash : String
  boundary : String
  boundaryList : BoundaryList
  /-- Constants hashed into the claims. -/
  hashed : Nat

/-- Run the export in library root `root`; `backend` hashes it. -/
def run (backend : Core.Backend) (root : System.FilePath) (libsGiven : Array String) : IO Result := do
  let rev ← gitHead root
  let ledger ← Ledger.load root
  let { libs, mods, deps, env, .. } ← load root libsGiven
  -- The boundary list. Checked after the build, which may update `lake-manifest.json`.
  let commit ← commitIfClean root rev
  let toolchain := "v" ++ Lean.versionString
  let library := ", ".intercalate libs.toList
  let (tags, errors) ← trustedTags env
  let (declarations, errors') ← expand env tags
  -- Every `@[trusted]` of this library has an id; imported libraries are theirs to fix.
  let own : NameSet := mods.foldl (·.insert ·) {}
  let noId := (tags.filter fun t => t.id.isNone && own.contains (moduleOf env t.name)).map
    (s!"{·.name}: tagged without an id; run `leanblame id`")
  let problems := errors ++ errors' ++ noId
  unless problems.isEmpty do
    fail ("export failed:\n" ++ "\n".intercalate (problems.toList.map ("  " ++ ·)))
  IO.eprintln "leanblame: printing statements"
  let declarations ← withStatements root mods declarations
  let boundaryList : BoundaryList := { library, commit, toolchain, deps, declarations := declarations.map (·.2) }
  let boundaryText := jsonText boundaryList
  -- The constants to export: the library's own (non-internal) constants and the boundary list.
  let mut roots : Array Name := #[]
  let mut own : Array (Name × ConstantInfo) := #[]
  for m in mods do
    let some idx := env.getModuleIdx? m | continue
    for n in env.header.moduleData[idx.toNat]!.constNames do
      let some ci := env.constants.map₁[n]? | continue
      -- A name in several modules belongs to the first, as in `moduleOf`.
      unless env.getModuleIdxFor? n == some idx do continue
      own := own.push (n, ci)
      if !n.isInternal && roundTrips n then
        roots := roots.push n
  -- The library's taggable constants, for `status`'s untagged-dependency warning.
  let owned ← (own.filterMapM fun (n, ci) => return if ← taggable n ci then some n.toString else none).toIO'
    { fileName := "", fileMap := default } { env }
  for (n, d) in declarations do
    unless roundTrips n do fail s!"{d.name}: this name does not read back from its printed form"
    roots := roots.push n
  roots := (roots.qsort (fun a b => a.cmp b == .lt)).eraseReps
  -- Run the toolchain's exporter on `env`, hashing the bytes as they are written.
  let tmp ← Store.tmpPath root "export"
  IO.eprintln s!"leanblame: leanexport ({roots.size} roots)"
  let hex ← dumpToFile env roots tmp
  let boundary ← Store.putString root .boundaries boundaryText
  -- The graph: every claim hash, computed now, as the other commands only read it; a stored graph
  -- of the same export and boundary list has already passed.
  let hashed ← match ← Graph.load? root (mkHash hex) boundaryList with
    | some h => pure h
    | none =>
      let h ← try Walk.hashExport backend tmp boundaryList
        catch e => IO.FS.removeFile tmp; fail s!"cannot hash the export: {e}"
      Graph.save root (mkHash hex) h
      pure h
  let exportHash ← Store.putFile root .exports tmp hex
  let ownedHash ← Store.putString root .owned ("\n".intercalate (owned.qsort (· < ·)).toList ++ "\n")
  Store.writeCurrent root
    { exportHash, boundary, modules := mods.map toString, owned := ownedHash }
  -- Sweep. Exports and boundary lists stay while the current pointer or a record names them, graphs
  -- with their export; evidence while its claim is current; a proof while evidence or a record
  -- names it.
  let mut exports : Std.HashSet String := ({} : Std.HashSet String).insert hex
  let mut boundaries : Std.HashSet String := ({} : Std.HashSet String).insert (hashHex boundary)
  let mut proofs : Std.HashSet String := {}
  for (_, r) in ledger.byId do
    if let .approve a := r.record then
      exports := exports.insert (hashHex a.exportHash)
      boundaries := boundaries.insert (hashHex a.boundary)
      if let some e := a.evidence then proofs := proofs.insert (hashHex e)
  let evidence : Std.HashSet String := hashed.boundary.declarations.foldl (init := {}) fun s d =>
    s.insert ((Store.evidencePath root d.name hashed.nodes[d.name]!.claim).fileName.getD "")
  let mut removed := (← Store.sweep root .exports exports) + (← Store.sweep root .boundaries boundaries)
  removed := removed + (← Store.sweep root .owned (({} : Std.HashSet String).insert (hashHex ownedHash)))
  removed := removed + (← Store.sweepDir (Store.evidenceDir root) evidence)
  removed := removed + (← Store.sweep root .proofs (proofs.union (← Store.evidenceProofs root)))
  Graph.sweep root exports
  if removed > 0 then IO.eprintln s!"leanblame: removed {removed} objects nothing names any more"
  return { exportHash, boundary, boundaryList, hashed := hashed.nodes.size }

end LeanBlame.Export
