/-
`leanblame export [--boundary FILE] [--lib NAME]...` (docs/04-architecture.md).

Builds the library with `lake build`, imports its modules, and makes the
boundary list: the declarations tagged `@[trusted]` (own and imported) or
listed in `--boundary FILE`, plus the members of tagged structures and
inductives, with `module`, `kind` and the provenance fields from the library
itself. Runs the toolchain's `leanexport` on the library's constants and the
boundary list, and writes both files into the object store. Prints the two
hashes.
-/
import Lean
import Lake.Load.Manifest
import Lake.Toml
import Lake.Util.Git
import LeanBlame.Attr
import LeanBlame.Cli.Schema
import LeanBlame.Cli.Store
import LeanBlame.Cli.Walk

namespace LeanBlame.Export

open Lean

/-- The informal text of a docstring. docs/03 asks for Unicode normalization, which Lean core
does not have: ASCII whitespace is trimmed and line endings are normalized. -/
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
  for line in strLines out do
    if strTrim line == "" then continue
    match Json.parse line with
    | .ok (.arr xs) =>
      for x in xs do
        if let .str s := x then
          mods := mods.push s.toName
    | _ => fail s!"unexpected output from `lake query`: {line}"
  if mods.isEmpty then fail "`lake query` reported no modules"
  return dedup mods

/-- The library's commit, with a warning when the work tree is dirty. -/
def gitCommit (root : System.FilePath) : IO String := do
  let repo : Lake.GitRepo := root
  let some rev ← repo.getHeadRevision?
    | IO.eprintln "warning: not a git repository with commits; commit recorded as \"unknown\""
      return "unknown"
  if ← repo.hasDiff then
    IO.eprintln "warning: uncommitted changes; the recorded commit does not contain them"
  return rev

/-- Commits of git dependencies, from `lake-manifest.json`. Path dependencies have none. -/
def manifestDeps (root : System.FilePath) : IO (Array (String × String)) := do
  let some m ← Lake.Manifest.load? (root / "lake-manifest.json") | return #[]
  return m.packages.filterMap fun p => match p.src with
    | .git (rev := rev) .. => some (p.name.toString (escape := false), rev)
    | .path .. => none

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- A declaration put on the boundary, by `@[trusted]` or by a boundary-list file. -/
structure Tag where
  name : Name
  informal : String
  informalSource : String

/-- The `@[trusted]` declarations, own and imported, with their docstrings; and the problems. -/
def trustedTags (env : Environment) : IO (Array Tag × Array String) := do
  let mut tags := #[]
  let mut errors := #[]
  for n in (trustedDecls env).qsort (·.cmp · == .lt) do
    let some doc ← findSimpleDocString? env n
      | errors := errors.push s!"{n}: tagged declarations need a docstring (the informal text)"; continue
    let informal := normalizeInformal doc
    if informal.isEmpty then
      errors := errors.push s!"{n}: tagged declarations need a non-empty docstring"; continue
    tags := tags.push { name := n, informal, informalSource := "docstring" }
  return (tags, errors)

/-- The declarations of a boundary-list file, whose `module` and `kind` must agree with `env`; and
the problems. -/
def fileTags (env : Environment) (b : BoundaryList) : Array Tag × Array String := Id.run do
  let mut tags := #[]
  let mut errors := #[]
  for d in b.declarations do
    let some n := Syntax.decodeNameLit ("`" ++ d.name)
      | errors := errors.push s!"{d.name}: not a constant name"; continue
    let some ci := env.find? n | errors := errors.push s!"{d.name}: not in the environment"; continue
    if Walk.kindOf ci != d.kind then
      errors := errors.push s!"{d.name}: kind is {Walk.kindOf ci}, the list says {d.kind}"
    else if (moduleOf env n).toString != d.module then
      errors := errors.push s!"{d.name}: module is {moduleOf env n}, the list says {d.module}"
    else
      tags := tags.push { name := n, informal := d.informal, informalSource := d.informalSource }
  return (tags, errors)

/-- The boundary list's declarations, sorted by name: the tagged ones, and the constructors and
projections of tagged inductives and structures that are not tagged themselves, with their own
docstring or else the parent's text. `module` and `kind` come from `env`. Also the problems. -/
def expand (env : Environment) (tags : Array Tag) : IO (Array BoundaryDecl × Array String) := do
  let decl (n : Name) (ci : ConstantInfo) (informal informalSource : String) : BoundaryDecl :=
    { name := n.toString, module := (moduleOf env n).toString, kind := Walk.kindOf ci, informal,
      informalSource }
  let tagged : NameSet := tags.foldl (·.insert ·.name) {}
  let mut out := #[]
  let mut errors := #[]
  let mut members : Array (Name × Tag) := #[]
  for t in tags do
    let some ci := env.find? t.name
      | errors := errors.push s!"{t.name}: tagged but not in the environment"; continue
    if ci.isUnsafe then
      errors := errors.push s!"{t.name}: `unsafe` declarations cannot be tagged"; continue
    if ci matches .recInfo _ then
      errors := errors.push s!"{t.name}: recursors cannot be tagged"; continue
    out := out.push (decl t.name ci t.informal t.informalSource)
    if let .inductInfo iv := ci then
      let projs := ((getStructureInfo? env t.name).map (·.fieldInfo.map (·.projFn))).getD #[]
      for m in iv.ctors.toArray ++ projs do
        unless tagged.contains m do members := members.push (m, t)
  for (m, parent) in members do
    let some ci := env.find? m | errors := errors.push s!"{m}: member of {parent.name} not found"; continue
    out := out.push <| match (← findSimpleDocString? env m).map normalizeInformal with
      | some doc => if doc.isEmpty then decl m ci parent.informal parent.informalSource
        else decl m ci doc "docstring"
      | none => decl m ci parent.informal parent.informalSource
  return (out.qsort (·.name < ·.name), errors)

/-- Whether a user could tag `n`, that is, Lean did not generate it (docs/03): not a compiler
auxiliary, recursor or recursor derivative, `noConfusion`, matcher, equation lemma or other
reserved name, nor anything Lean's own `isAutoDeclOrPrivate_Internal` counts as generated
(`T.brecOn.go`, `T.ctorIdx`, …). Constructors are tagged with their type. -/
def taggable (n : Name) (ci : ConstantInfo) : CoreM Bool := do
  let env ← getEnv
  if n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n || isRecCore env n ||
      Meta.isMatcherCore env n || ci.isCtor || isReservedName env n then
    return false
  return !(← isAutoDeclOrPrivate_Internal n)

/-- A constant name `leanexport` can read back from its command line. -/
def roundTrips (n : Name) : Bool :=
  Syntax.decodeNameLit ("`" ++ n.toString) == some n

structure Result where
  exportHash : String
  boundary : String
  boundaryList : BoundaryList
  /-- Constants hashed into the claims. -/
  hashed : Nat

/-- Run the export in library root `root`. -/
def run (root : System.FilePath) (boundaryFile? : Option System.FilePath) (libsGiven : Array String) :
    IO Result := do
  -- docs/04: build using the mathlib cache, when the library depends on mathlib.
  if (← manifestDeps root).any (·.1 == "mathlib") then
    IO.eprintln "leanblame: lake exe cache get"
    try runInto "lake" #["exe", "cache", "get"] root #[] (← IO.getStderr) "`lake exe cache get`"
    catch e => IO.eprintln s!"warning: could not fetch the mathlib cache: {e}"
  IO.eprintln "leanblame: lake build"
  runInto "lake" #["build"] root #[] (← IO.getStderr) "`lake build`"
  let libs ← libraryNames root libsGiven
  let mods ← libraryModules root libs
  let leanPath := strTrim (← IO.Process.run
    { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"], cwd := root })
  let sp : SearchPath := (leanPath.splitOn ":").filter (· != "") |>.map System.FilePath.mk
  let sysroot ← findSysroot
  initSearchPath sysroot sp
  IO.eprintln s!"leanblame: importing {mods.size} modules of {", ".intercalate libs.toList}"
  let env ← importModules (mods.map fun m => { module := m }) {} (loadExts := false)
  let modSet : NameSet := mods.foldl (·.insert ·) {}
  -- The boundary list.
  let commit ← gitCommit root
  let deps ← manifestDeps root
  let toolchain := "v" ++ Lean.versionString
  let library := ", ".intercalate libs.toList
  let (tags, errors) ← match boundaryFile? with
    | some f => match BoundaryList.parse (← IO.FS.readFile f) with
      | .ok b => pure (fileTags env b)
      | .error e => fail s!"{f}: {e}"
    | none => trustedTags env
  let (declarations, errors') ← expand env tags
  unless (errors ++ errors').isEmpty do
    fail ("export failed:\n" ++ "\n".intercalate ((errors ++ errors').toList.map ("  " ++ ·)))
  let boundaryList : BoundaryList := { library, commit, toolchain, deps, declarations }
  let boundaryText := jsonText boundaryList
  -- The constants to export: the library's own (non-internal) constants and the boundary list.
  let mut roots : Array Name := #[]
  let mut own : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if modSet.contains env.header.moduleNames[idx.toNat]! then
        own := own.push (n, ci)
        if !n.isInternal && roundTrips n then
          roots := roots.push n
  -- The library's taggable constants, for `status`'s untagged-dependency warning.
  let owned ← (own.filterMapM fun (n, ci) => return if ← taggable n ci then some n.toString else none).toIO'
    { fileName := "", fileMap := default } { env }
  for d in boundaryList.declarations do
    let some n := Syntax.decodeNameLit ("`" ++ d.name) | fail s!"{d.name}: not a constant name"
    unless roundTrips n do fail s!"{d.name}: this name cannot be passed to leanexport"
    unless roots.contains n do roots := roots.push n
  roots := roots.qsort (fun a b => a.cmp b == .lt)
  -- Run the toolchain's exporter.
  let exporter := sysroot / "bin" / ("leanexport" ++ (if System.Platform.isWindows then ".exe" else ""))
  let tmp ← Store.tmpPath root "export"
  IO.eprintln s!"leanblame: leanexport ({roots.size} roots)"
  IO.FS.withFile tmp .write fun h =>
    runInto exporter.toString (mods.map toString ++ #["--"] ++ roots.map toString) root
      #[("LEAN_PATH", some leanPath)] (.ofHandle h) "leanexport"
  -- Compute every claim hash now, so that problems surface at export time.
  let exported ← LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk tmp .read))
  let hashed ← try Walk.hashExport exported boundaryList
    catch e => IO.FS.removeFile tmp; fail s!"cannot hash the export: {e}"
  let exportHash ← Store.putFile root tmp
  let boundary ← Store.putString root boundaryText
  let ownedHash ← Store.putString root ("\n".intercalate (owned.qsort (· < ·)).toList ++ "\n")
  Store.writeCurrent root
    { exportHash, boundary, modules := mods.map toString, owned := ownedHash } commit
  return { exportHash, boundary, boundaryList, hashed := hashed.nodes.size }

end LeanBlame.Export
