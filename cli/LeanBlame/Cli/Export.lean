/-
`leanblame export [--boundary FILE] [--lib NAME]...` (docs/04-architecture.md).

Builds the library with `lake build`, imports its modules, collects the
boundary list from `@[trusted]` (own and imported, with structure expansion)
or reads it from `--boundary`, runs the toolchain's `leanexport` on the
library's constants and the boundary list, and writes both files into the
object store. Prints the two hashes.
-/
import Lean
import Lake.Toml
import LeanBlame.Attr
import LeanBlame.Cli.Schema
import LeanBlame.Cli.Store
import LeanBlame.Cli.Walk

namespace LeanBlame.Export

open Lean

/-- The export kind of a constant, as the boundary list and the hash name it. -/
def constKind : ConstantInfo → String
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .recInfo _ => "rec"

/-- Unicode-normalization is not available in Lean core; we trim ASCII whitespace
and normalize line endings. See the report on approximations. -/
def normalizeInformal (s : String) : String :=
  strTrim ((s.splitOn "\r\n").foldl (init := "") fun acc part =>
    if acc.isEmpty then part else acc ++ "\n" ++ part)

/-- Library names: `--lib` flags, else the default `lean_lib` targets of `lakefile.toml`. -/
def libraryNames (root : System.FilePath) (requested : Array String) : IO (Array String) := do
  unless requested.isEmpty do return requested
  let path := root / "lakefile.toml"
  unless ← path.pathExists do
    fail "cannot find the library: no lakefile.toml here (for lakefile.lean, pass --lib NAME)"
  let ictx := Lean.Parser.mkInputContext (← IO.FS.readFile path) path.toString
  let t ← match ← (Lake.Toml.loadToml ictx).toBaseIO with
    | .ok t => pure t
    | .error _ => fail s!"{path}: not valid TOML"
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
  let out ← runCapture "lake" (#["query", "--json"] ++ libs.map (· ++ ":modules")) root
  let mut mods := #[]
  for line in strLines out do
    if strTrim line == "" then continue
    match Json.parse line with
    | .ok (.arr xs) =>
      for x in xs do
        if let .str s := x then
          let n := s.toName
          unless mods.contains n do mods := mods.push n
    | _ => fail s!"unexpected output from `lake query`: {line}"
  if mods.isEmpty then fail "`lake query` reported no modules"
  return mods

/-- The library's commit, with a warning when the work tree is dirty. -/
def gitCommit (root : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"], cwd := root }
  if out.exitCode != 0 then
    IO.eprintln "warning: not a git repository with commits; commit recorded as \"unknown\""
    return "unknown"
  let status ← IO.Process.output { cmd := "git", args := #["status", "--porcelain", "--untracked-files=no"], cwd := root }
  if strTrim status.stdout != "" then
    IO.eprintln "warning: uncommitted changes; the recorded commit does not contain them"
  return strTrim out.stdout

/-- Commits of git dependencies, from `lake-manifest.json`. Path dependencies have none. -/
def manifestDeps (root : System.FilePath) : IO (Array (String × String)) := do
  let some text ← readFileIfExists (root / "lake-manifest.json") | return #[]
  let .ok j := Json.parse text | return #[]
  let .ok pkgs := j.getObjValAs? (Array Json) "packages" | return #[]
  return pkgs.filterMap fun p => do
    let .ok "git" := p.getObjValAs? String "type" | none
    let .ok name := p.getObjValAs? String "name" | none
    let .ok rev := p.getObjValAs? String "rev" | none
    return (name, rev)

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- The boundary list from `@[trusted]`, own and imported, with structure expansion. -/
def collectTrusted (env : Environment) : IO (Array BoundaryDecl) := do
  let tagged := (LeanBlame.trustedDecls env).qsort (fun a b => a.cmp b == .lt)
  let mut out : Array BoundaryDecl := #[]
  let mut seen : NameSet := {}
  let mut errors : Array String := #[]
  -- Explicit tags first: each needs its own docstring.
  let mut expansions : Array (Name × Name) := #[]  -- (member, tagged parent)
  for n in tagged do
    let some ci := env.find? n | errors := errors.push s!"{n}: tagged but not in the environment"; continue
    if ci.isUnsafe then
      errors := errors.push s!"{n}: `unsafe` declarations cannot be tagged"; continue
    if ci matches .recInfo _ then
      errors := errors.push s!"{n}: recursors cannot be tagged"; continue
    let some doc ← findSimpleDocString? env n
      | errors := errors.push s!"{n}: tagged declarations need a docstring (the informal text)"; continue
    let informal := normalizeInformal doc
    if informal.isEmpty then
      errors := errors.push s!"{n}: tagged declarations need a non-empty docstring"; continue
    out := out.push { name := n.toString, module := (moduleOf env n).toString, kind := constKind ci,
                      informal, informalSource := "docstring" }
    seen := seen.insert n
    if let .inductInfo iv := ci then
      for c in iv.ctors do expansions := expansions.push (c, n)
      if let some si := getStructureInfo? env n then
        for f in si.fieldInfo do expansions := expansions.push (f.projFn, n)
  -- Members of tagged structures and inductives: own docstring, else the parent's.
  for (m, parent) in expansions do
    if seen.contains m then continue
    let some ci := env.find? m | errors := errors.push s!"{m}: member of {parent} not found"; continue
    let doc := (← findSimpleDocString? env m).map normalizeInformal |>.filter (!·.isEmpty)
    let parentDoc := (out.find? (·.name == parent.toString)).map (·.informal)
    let some informal := doc <|> parentDoc | continue
    out := out.push { name := m.toString, module := (moduleOf env m).toString, kind := constKind ci,
                      informal, informalSource := "docstring" }
    seen := seen.insert m
  unless errors.isEmpty do
    fail ("export failed:\n" ++ "\n".intercalate (errors.toList.map ("  " ++ ·)))
  return out.qsort (fun a b => a.name < b.name)

/-- Check an adapter's boundary list against the environment. -/
def checkBoundary (env : Environment) (b : BoundaryList) : IO Unit := do
  let mut errors : Array String := #[]
  for d in b.declarations do
    let some n := Syntax.decodeNameLit ("`" ++ d.name)
      | errors := errors.push s!"{d.name}: not a constant name"; continue
    match env.find? n with
    | none => errors := errors.push s!"{d.name}: not in the environment"
    | some ci =>
      if ci.isUnsafe then errors := errors.push s!"{d.name}: `unsafe` declarations cannot be tagged"
      else if constKind ci != d.kind then
        errors := errors.push s!"{d.name}: kind is {constKind ci}, the list says {d.kind}"
  unless errors.isEmpty do
    fail ("boundary list does not match the library:\n" ++ "\n".intercalate (errors.toList.map ("  " ++ ·)))

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
  IO.eprintln "leanblame: lake build"
  runToStderr "lake" #["build"] root
  let libs ← libraryNames root libsGiven
  let mods ← libraryModules root libs
  let leanPath := strTrim (← runCapture "lake" #["env", "printenv", "LEAN_PATH"] root)
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
  let (boundaryText, boundaryList) ← match boundaryFile? with
    | some f =>
      let text ← IO.FS.readFile f
      let b ← match BoundaryList.parse text with
        | .ok b => pure b
        | .error e => fail s!"{f}: {e}"
      checkBoundary env b
      pure (text, b)
    | none =>
      let decls ← collectTrusted env
      let b : BoundaryList := { library, commit, toolchain, deps, declarations := decls }
      pure (b.toOJson.renderFile, b)
  -- The constants to export: the library's own (non-internal) constants and the boundary list.
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if n.isInternal then continue
    if let some idx := env.getModuleIdxFor? n then
      if modSet.contains env.header.moduleNames[idx.toNat]! && roundTrips n then
        roots := roots.push n
  for d in boundaryList.declarations do
    let some n := Syntax.decodeNameLit ("`" ++ d.name) | fail s!"{d.name}: not a constant name"
    unless roundTrips n do fail s!"{d.name}: this name cannot be passed to leanexport"
    unless roots.contains n do roots := roots.push n
  roots := roots.qsort (fun a b => a.cmp b == .lt)
  -- Run the toolchain's exporter.
  let exporter := sysroot / "bin" / ("leanexport" ++ (if System.Platform.isWindows then ".exe" else ""))
  let tmp ← Store.tmpPath root "export"
  IO.eprintln s!"leanblame: leanexport ({roots.size} roots)"
  runToFile exporter.toString (mods.map toString ++ #["--"] ++ roots.map toString) tmp root
    (env := #[("LEAN_PATH", some leanPath)])
  -- Compute every claim hash now, so that problems surface at export time.
  let exported ← LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk tmp .read))
  let hashed ← match Walk.hashExport exported boundaryList with
    | .ok h => pure h
    | .error e => IO.FS.removeFile tmp; fail s!"cannot hash the export: {e}"
  let exportHash ← Store.putFile root tmp
  let boundary ← Store.putString root boundaryText
  Store.writeCurrent root { exportHash, boundary } commit
  return { exportHash, boundary, boundaryList, hashed := hashed.nodes.size }

end LeanBlame.Export
