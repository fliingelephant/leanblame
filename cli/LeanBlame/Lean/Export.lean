/-
`leanblame export` (README.md, Commands), for the libraries and the blueprint manifest that
`leanblame.toml` names.

Builds the libraries with `lake build`, imports their modules, and makes the boundary list: the
declarations tagged `@[trusted "id"]` (own and imported), or named by the blueprint
manifest `boundary` names, plus the members of tagged structures and inductives, with `id`, `parent`,
`module`, `kind`, `role` and the printed statement. Exports the boundary list's declarations and
what they use, proofs included, with the toolchain's `leanexport` writer (in-process), and writes
both files into the object store, with their graph: the export hashed through the backend
(docs/decisions.md, "Storage"). Makes the piece graph the challenges of the tagged
declarations are cut from (`Pieces`). Then points `.leanblame/current` at them, with
the commit, toolchain and dependencies they were made from. Prints the two hashes.

The library is imported once, with the environment extensions of everything it imports, as an
editor or doc-gen4 loads it; every output comes from that one environment.
-/
import Lean
import Lake.Config.InstallPath
import Lake.Config.Module
import Lake.Load.Manifest
import Lake.Load.Package
import Lake.Load.Workspace
import Lake.Util.Git
import LeanExport.Basic
import LeanBlame.Attr
import LeanBlame.Core.Records
import LeanBlame.Core.Walk
import LeanBlame.Lean.Blueprint
import LeanBlame.Lean.Pieces
import LeanBlame.Lean.Source
import LeanBlame.Lean.Statements

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

/-- Lake as the toolchain of `lean` holds it. -/
def lakeEnv : IO Lake.Env := do
  let (elan?, some lean, _) ← Lake.findInstall? | fail "cannot find Lean: no `lean` on PATH"
  match ← (Lake.Env.compute (.ofLean lean) lean elan?).toBaseIO with
  | .ok e => pure e
  | .error e => fail s!"Lake: {e}"

/-- The package in `root`, as Lake loads its `lakefile.toml` or `lakefile.lean`. -/
def lakePackage (root : System.FilePath) : IO Lake.Package := do
  let (pkg?, log) ← (Lake.loadPackage { lakeEnv := ← lakeEnv, wsDir := root }).run?
  let some pkg := pkg? | fail s!"Lake cannot load the package:\n{log}"
  return pkg

/-- Lean's own modules and those of the packages `trusted` names (`none`: `mathlib`, when the
workspace in `root` has it) and of the packages they require, among `mods`: their declarations enter
claims by their statement alone. A module no package of the workspace holds is Lean's own. -/
def trustedModules (root : System.FilePath) (trusted? : Option (Array String)) (mods : Array Name) :
    IO NameSet := do
  let (ws?, log) ← (Lake.loadWorkspace { lakeEnv := ← lakeEnv, wsDir := root }).run?
  let some ws := ws? | fail s!"Lake cannot load the workspace:\n{log}"
  let named := trusted?.getD (if (ws.findPackageByName? `mathlib).isSome then #["mathlib"] else #[])
  let starts ← named.mapM fun p => match ws.findPackageByName? p.toName with
    | some pkg => pure pkg.wsIdx
    | none => fail s!"{Config.fileName}: `trusted` names {p}, which is not a package of the workspace"
  let pkgs := Id.run <| reach starts fun i => pure ws.packages[i]!.depIdxs
  return mods.foldl (init := {}) fun s m => match ws.findModule? m with
    | some mod => if pkgs.contains mod.pkg.wsIdx then s.insert m else s
    | none => s.insert m

/-- The libraries to export: the `libraries` of `leanblame.toml`, else the package's default `lean_lib` targets, else
all its `lean_lib`s. -/
def libraries (pkg : Lake.Package) (requested : Array String) : IO (Array Lake.LeanLib) := do
  if requested.isEmpty then
    let defaults := pkg.leanLibs.filter (pkg.defaultTargets.contains ·.name)
    let libs := if defaults.isEmpty then pkg.leanLibs else defaults
    if libs.isEmpty then fail "the package declares no lean_lib"
    return libs
  requested.mapM fun n => match pkg.findLeanLib? n.toName with
    | some l => pure l
    | none => fail s!"the package declares no lean_lib {n}"

/-- The Lean options Lake builds the modules of `lib` with, as `lean` reads them
(`Lean.Language.Lean.reparseOptions`, after the imports declare them): its `leanOptions`, then the
`-D` options of its Lean arguments in Lake's order, weak ones first, so that a strong one wins. -/
def libraryOptions (lib : Lake.LeanLib) : IO Options := do
  let opts ← (lib.weakLeanArgs ++ lib.leanArgs).foldlM (init := lib.leanOptions.toOptions) fun opts a => do
    let some kv := a.dropPrefix? "-D" | return opts
    let k :: v@(_ :: _) := kv.copy.splitOn "=" | fail s!"{lib.name}: Lean argument {a}"
    return opts.insert k.toName (.ofString ("=".intercalate v))
  Lean.Language.Lean.reparseOptions opts

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
def manifestDeps (root : System.FilePath) : IO (Array (String × String) × Array Pieces.Require) := do
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

/-- The `@[trusted]` declarations, tagged in any module, own or imported, with their ids and
docstrings (empty for none); and the problems. Two modules that do not import each other can tag one declaration;
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
    let informal := ((← findSimpleDocString? env n).map normalizeInformal).getD ""
    tags := tags.push { name := n, id, informal }
  return (tags, errors)

/-- The tags of a verso-blueprint manifest (`boundary` in `leanblame.toml`), and the problems. A label is the id
of the first declaration it names; the label's other declarations name that one as their parent. -/
def blueprintTags (f : System.FilePath) : IO (Array Tag × Array String) := do
  let accepted := "`boundary` names a verso-blueprint blueprint-manifest.json"
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

/-- What `n` is, in the words of Lean's documentation (doc-gen4): `def`, `theorem`, `axiom`,
`opaque`, `instance`, `inductive`, `structure`, `class`, `constructor`, and `field` for a structure's
projection. Not hashed: the hash takes the kernel's kind (`Source.kindOf`). -/
def kindWord (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  if env.isProjectionFn n then "field" else
  match ci with
  | .inductInfo _ =>
    if isClass env n then "class" else if isStructure env n then "structure" else "inductive"
  | .ctorInfo _ => "constructor"
  | .defnInfo _ | .thmInfo _ => if Meta.isInstanceCore env n then "instance" else Source.kindOf ci
  | _ => Source.kindOf ci

/-- Where `n` stands in the source: its module's place in the import order (after every module it
imports), then the line and column where it starts. -/
def sourcePlace (env : Environment) (n : Name) : Option (Nat × Nat × Nat) := do
  let idx ← env.getModuleIdxFor? n
  let r ← Pieces.declRange? env n
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
  let mut entries : Array (Tag × ConstantInfo) := #[]
  let mut errors := #[]
  for t in tags do
    let some ci := env.find? t.name
      | errors := errors.push s!"{t.name}: tagged but not in the environment"; continue
    if ci.isUnsafe then
      errors := errors.push s!"{t.name}: `unsafe` declarations cannot be tagged"; continue
    if ci matches .recInfo _ then
      errors := errors.push s!"{t.name}: recursors cannot be tagged"; continue
    entries := entries.push ({ t with parent := t.parent <|> parentOf.find? t.name }, ci)
    for m in members t.name do
      if tagged.contains m then continue
      let some mi := env.find? m | errors := errors.push s!"{m}: member of {t.name} not found"; continue
      let informal := (((← findSimpleDocString? env m).map normalizeInformal).filter (· != "")).getD t.informal
      entries := entries.push ({ name := m, id := none, parent := some t.name, informal }, mi)
  let byName : NameMap Tag := entries.foldl (init := {}) fun m (e, _) => m.insert e.name e
  let rec root (fuel : Nat) (p : Name) : Name :=
    match fuel, byName.find? p with
    | fuel + 1, some { id := none, parent := some q, .. } => root fuel q
    | _, _ => p
  let mut out := #[]
  -- An id names one declaration: a copied `@[trusted "id"]` is caught here.
  let mut owner : Std.HashMap String Name := {}
  for (e, ci) in entries do
    let parent := e.parent.map (root entries.size)
    let id? := e.id <|> parent.bind fun p =>
      (byName.find? p).bind (·.id) |>.map (s!"{·}/{relativeName p e.name}")
    let some id := id?
      | errors := errors.push s!"{e.name}: tagged without an id; run `leanblame id` in the library that tags it"
        continue
    if let some other := owner[id]? then
      errors := errors.push s!"{other} and {e.name} have the same id {id}; remove it from one of them and run `leanblame id`"
    owner := owner.insert id e.name
    let some module := moduleOf? env e.name | fail s!"{e.name} is in no imported module"
    let some place := sourcePlace env e.name <|> parent.bind (sourcePlace env)
      | errors := errors.push s!"{e.name}: Lean has no source position for it"; continue
    let d : BoundaryDecl := {
      name := e.name.toString, id, parent := parent.map (·.toString), module := module.toString
      kind := kindWord env e.name ci, role := Source.roleOf ci, informal := e.informal, statement := default }
    out := out.push (place, e.name, d)
  let before (a b : (Nat × Nat × Nat) × Name × BoundaryDecl) : Bool :=
    let ((m, l, c), (m', l', c')) := (a.1, b.1)
    if m != m' then m < m' else if l != l' then l < l' else if c != c' then c < c'
    else a.2.2.name < b.2.2.name
  return ((out.qsort before).map (·.2), errors)

/-- `declarations` with their statements (`Statements`). -/
def withStatements (env : Environment) (declarations : Array (Name × BoundaryDecl)) :
    IO (Array (Name × BoundaryDecl)) := do
  let printed ← Statements.print env (declarations.map (·.1))
  return declarations.zipWith (fun (n, d) st => (n, { d with statement := st })) printed

/-- Whether a user could tag `n`, that is, Lean did not generate it (trust-model.md): not a compiler
auxiliary, recursor or recursor derivative, `noConfusion`, matcher, equation lemma or other
reserved name, nor anything Lean's own `isAutoDeclOrPrivate_Internal` counts as generated
(`T.brecOn.go`, `T.ctorIdx`, …). Constructors are tagged with their type. -/
def taggable (n : Name) (ci : ConstantInfo) : CoreM Bool := do
  let env ← getEnv
  if n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n || isRecCore env n ||
      Meta.isMatcherCore env n || ci.isCtor || isReservedName env n then
    return false
  return !(← isAutoDeclOrPrivate_Internal n)

/-- The taggable constants the modules `mods` declare, in their order; a name in several modules
belongs to the first, as in `moduleOf`. -/
def taggableIn (env : Environment) (mods : Array Name) : IO (Array Name) := do
  let mut own : Array (Name × ConstantInfo) := #[]
  for m in mods do
    let some data := moduleData? env m | fail s!"module {m} was not imported"
    for n in data.constNames do
      unless moduleOf? env n == some m do continue
      let some ci := env.constants.map₁[n]? | fail s!"{n} of module {m} is not in the environment"
      own := own.push (n, ci)
  (own.filterMapM fun (n, ci) => return if ← taggable n ci then some n else none).toIO'
    { fileName := "", fileMap := default } { env }

/-- Run the toolchain's exporter on `env` from `roots`, as `leanexport` writes it, leaving out the
constants in `skip`, which stay names where used: into the file `path?`, if any. Returns the
SHA-256 (hex) of the bytes, computed as they are written. -/
def dump (env : Environment) (roots : Array Name) (skip : NameHashSet := {})
    (path? : Option System.FilePath := none) : IO String := do
  let sha ← IO.mkRef ({} : Sha256.State)
  let go (out : ByteArray → IO Unit) : IO Unit :=
    let write (b : ByteArray) : IO Unit := do out b; sha.modify (·.update b)
    IO.withStdout { flush := pure (), read := fun _ => pure .empty, write, getLine := pure ""
                    putStr := (write ·.toUTF8), isTty := pure false } <|
      LeanExport.M.run env do
        LeanExport.initState env
        modify fun st => { st with visitedConstants := skip }
        LeanExport.dumpMetadata
        for c in roots do
          modify fun st => { st with noMDataExprs := {} }
          LeanExport.dumpConstant c
  match path? with
  | some path => IO.FS.withFile path .write fun h => go h.write
  | none => go fun _ => pure ()
  return Sha256.toHex (← sha.get).finish

/-- The constants of `env` in the modules `mods`. -/
def constantsIn (env : Environment) (mods : NameSet) : NameHashSet :=
  env.constants.fold (init := {}) fun s n _ => if (moduleOf? env n).any mods.contains then s.insert n else s

/-- The constants an export starts from: the tagged declarations, in `Name` order. -/
def rootsOf (names : Array Name) : Array Name :=
  names.qsort (·.cmp · == .lt)

/-- Lean's sysroot, `LEAN_PATH` and `LEAN_SRC_PATH`, as `lake env` has them in `root`. -/
def lakeEnvPaths (root : System.FilePath) : IO (System.FilePath × SearchPath × SearchPath) := do
  let vars := (← IO.Process.run { cmd := "lake", args := #["env", "printenv"], cwd := root }).lines.toArray
  let var (k : String) : IO String := do
    let some v := vars.findSome? fun l => (l.dropPrefix? (k ++ "=")).map (·.copy)
      | fail s!"`lake env printenv` did not report {k}"
    return v
  return (⟨← var "LEAN_SYSROOT"⟩, .parse (← var "LEAN_PATH"), .parse (← var "LEAN_SRC_PATH"))

/-- A built library with its modules imported. -/
structure Loaded where
  /-- The name of the Lake package. -/
  package : String
  mods : Array Name
  /-- The Lean options of each module, as Lake builds it. -/
  options : NameMap Options
  deps : Array (String × String)
  requires : Array Pieces.Require
  env : Environment
  /-- Where the sources are (`LEAN_SRC_PATH` of `lake env`). -/
  srcPath : System.SearchPath
  /-- Where the modules were imported from (`LEAN_SYSROOT` and `LEAN_PATH` of `lake env`). -/
  sysroot : System.FilePath
  leanPath : System.SearchPath

/-- Build the libraries of `root` (with the mathlib cache when they depend on mathlib) and import
their modules; with `loadExts`, running their initializers and loading the environment extensions of
everything they import (`main` allows initializers), which printing statements needs. -/
def load (root : System.FilePath) (libsGiven : Array String) (loadExts := true) : IO Loaded := do
  let pkg ← lakePackage root
  let libraries ← libraries pkg libsGiven
  let libs := libraries.map (·.name.toString (escape := false))
  -- Build using the mathlib cache, when `lake-manifest.json` names mathlib.
  if (← Lake.Manifest.load? (root / "lake-manifest.json")).any (·.packages.any (·.name == `mathlib)) then
    IO.eprintln "leanblame: lake exe cache get"
    runToStderr "lake" #["exe", "cache", "get"] root "`lake exe cache get`"
  IO.eprintln s!"leanblame: lake build {" ".intercalate libs.toList}"
  -- The modules are imported from the build directory. With Lake's artifact cache on, a build may
  -- leave them only in the cache unless Lake is asked to restore them.
  runToStderr "lake" (#["build"] ++ libs) root "`lake build`" (env := #[("LAKE_RESTORE_ARTIFACTS", some "true")])
  let (deps, requires) ← manifestDeps root
  let roots := (← libraries.flatMapM (·.getModuleArray)).map (·.name)
  let (sysroot, leanPath, srcPath) ← lakeEnvPaths root
  initSearchPath sysroot leanPath
  IO.eprintln s!"leanblame: importing {", ".intercalate libs.toList}"
  let env ← importModules (roots.map fun m => { module := m }) {} (loadExts := loadExts)
  -- The libraries' modules, in import order, as Lake has them: the imported ones local to a library
  -- (a module of several belongs to the first), with its Lean options.
  let libOptions ← libraries.mapM fun l => return (l, ← libraryOptions l)
  let mut mods := #[]
  let mut options : NameMap Options := {}
  for m in env.header.moduleNames do
    if let some (_, o) := libOptions.find? (·.1.isLocalModule m) then
      mods := mods.push m
      options := options.insert m o
  return { package := pkg.prettyName, mods, options, deps, requires, env, srcPath, sysroot, leanPath }

structure Result where
  exportHash : String
  boundary : String
  boundaryList : BoundaryList
  /-- Constants hashed into the claims. -/
  hashed : Nat

/-- Run the export in library root `root`; `backend` hashes it. -/
def run (backend : Core.Backend) (root : System.FilePath) (boundaryFile? : Option System.FilePath)
    (libsGiven : Array String) (trusted? : Option (Array String)) : IO Result := do
  let rev ← gitHead root
  let ledger ← Ledger.load root
  let { package, mods, options, deps, requires, env, srcPath, sysroot, leanPath } ← load root libsGiven
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
  let declarations ← withStatements env declarations
  let boundaryList : BoundaryList := { library := package, declarations := declarations.map (·.2) }
  -- The library's taggable constants, for `status`'s untagged declarations of this library.
  let owned := (← taggableIn env mods).map (·.toString)
  IO.eprintln "leanblame: piece graph"
  -- A challenge states the kernel's theorems, proofs `sorry`; a structure states its projections.
  let states (n : Name) (d : BoundaryDecl) :=
    d.role == .proved && !env.isProjectionFn n && (env.getAuxParentProjectionInfo? n).isNone
  let theorems := declarations.filterMap fun (n, d) => if states n d then some n else none
  let others := declarations.filterMap fun (n, d) => if states n d then none else some n
  let graph ← Pieces.make env mods srcPath (fun m => (options.find? m).getD {}) theorems others requires toolchain
  for (n, d) in declarations do
    unless roundTrips n do fail s!"{d.name}: this name does not read back from its printed form"
  -- The constants to export: the boundary list's declarations; the exporter adds what they use.
  let roots := rootsOf (declarations.map (·.1))
  let trustedMods ← trustedModules root trusted? env.header.moduleNames
  -- The constants alone, as an export has them: the library imported again, without the environment
  -- extensions `Meta` would consult, from the paths `load` used (loading Lake's workspace resets
  -- them); `env` is not kept from here on.
  initSearchPath sysroot leanPath
  let bare ← importModules (mods.map ({ module := · })) {} (loadExts := false)
  -- The export is hashed as the toolchain's exporter writes it; the store keeps the constants of it
  -- that are not trusted.
  IO.eprintln s!"leanblame: leanexport ({roots.size} roots)"
  let exportHash := mkHash (← dump bare roots)
  let tmp ← Store.tmpPath root "export"
  discard <| dump bare roots (constantsIn bare trustedMods) (some tmp)
  let boundary ← Store.putString root .boundaries (jsonText boundaryList)
  -- The graph: every claim hash, computed now by this LeanBlame, as the other commands only read it.
  let trusted : Std.HashSet String := trustedMods.foldl (init := {}) fun s m => s.insert m.toString
  let hashed ← try
      Walk.hashExport backend (← Source.ofEnv bare roots) boundaryList (trusted.contains ·.module) exportHash boundary
    catch e => IO.FS.removeFile tmp; fail s!"cannot hash the export: {e}"
  Graph.save root hashed
  -- Each root with the axioms a solution may use for it, from the claim graph.
  let permitted := Walk.permittedAxioms hashed (boundaryList.declarations.map (·.name))
  let withAxioms (p : Pieces.Piece) : Pieces.Piece := match p.root with
    | some n => { p with axioms := permitted.getD n #[] }
    | none => p
  let pieces ← Store.putString root .pieces (jsonText ({ pieces := graph.pieces.map withAxioms } : Pieces.Graph))
  discard <| Store.putFile root .exports tmp (hashHex exportHash)
  let ownedHash ← Store.putString root .owned ("\n".intercalate (owned.qsort (· < ·)).toList ++ "\n")
  Store.writeCurrent root
    { exportHash, boundary, owned := ownedHash, modules := mods.map toString, pieces, commit, toolchain, deps }
  -- Sweep. Exports and boundary lists stay while the current pointer or a record names them, graphs
  -- with their export; the piece graph while the current pointer names it; evidence while its claim is
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
  removed := removed + (← Store.sweep root .pieces (({} : Std.HashSet String).insert (hashHex pieces)))
  removed := removed + (← Store.sweepDir (Store.evidenceDir root) evidence)
  removed := removed + (← Store.sweep root .proofs (proofs.union (← Store.evidenceProofs root)))
  Graph.sweep root exports
  if removed > 0 then IO.eprintln s!"leanblame: removed {removed} objects nothing names any more"
  return { exportHash, boundary, boundaryList, hashed := hashed.nodes.size }

/-- Fails unless the library's Lean and dependencies are the last export's (`cur`). -/
def sameDeps (root : System.FilePath) (cur : Store.Current) : IO Unit := do
  let toolchain := "v" ++ Lean.versionString
  let (deps, _) ← manifestDeps root
  let differs := (if toolchain == cur.toolchain then #[] else #[s!"Lean {toolchain}, the export's {cur.toolchain}"]) ++
    (deps ++ cur.deps).filterMap fun (p, _) =>
      let now := (deps.find? (·.1 == p)).map (·.2)
      let was := (cur.deps.find? (·.1 == p)).map (·.2)
      if now == was then none else some s!"{p} at {now.getD "none"}, the export's at {was.getD "none"}"
  unless differs.isEmpty do
    fail ("the library's dependencies are not the last export's; export again:\n" ++
      "\n".intercalate ((dedup differs).toList.map ("  " ++ ·)))

/-- The constants the last export (`cur`) starts from. -/
def rootsOfCurrent (root : System.FilePath) (cur : Store.Current) : IO (Array Name) := do
  let names ← (← Store.readBoundary root cur.boundary).declarations.mapM fun d => match nameOf? d.name with
    | some n => pure n
    | none => fail s!"{d.name}: this name does not read back from its printed form"
  return rootsOf names

/-- The library's build, imported without environment extensions as `run` imports it to hash, for a
command that needs the last export (`cur`) whole: the build must be that export, so the same Lean,
the same dependencies, and the constants the store keeps of the export. -/
def lastBuild (root : System.FilePath) (cur : Store.Current) : IO Environment := do
  let cfg ← Config.load root
  let l ← load root cfg.libraries (loadExts := false)
  sameDeps root cur
  let roots ← rootsOfCurrent root cur
  let trustedMods ← trustedModules root cfg.trusted l.env.header.moduleNames
  let kept ← IO.FS.readBinFile (← Store.objectFile root .exports cur.exportHash)
  unless (← dump l.env roots (constantsIn l.env trustedMods)) == Sha256.hexOfBytes kept do
    fail "the library's build is not the last export; export again"
  return l.env

/-- Whether `leanchecker` replays the last export (`cur`), written again from the library's build to a
temporary file: the build must give that export. -/
def replays (root : System.FilePath) (cur : Store.Current) : IO Bool := do
  let l ← load root (← Config.load root).libraries (loadExts := false)
  let roots ← rootsOfCurrent root cur
  let tmp ← Store.tmpPath root "export"
  try
    unless mkHash (← dump l.env roots (path? := some tmp)) == cur.exportHash do
      fail "the library's build is not the last export; export again"
    Source.kernelAccepts tmp
  finally
    if ← tmp.pathExists then IO.FS.removeFile tmp

/-- Lean as the core's backend. The standard axioms are the three every Lean library may rest on
(docs/decisions.md, "Releases"). -/
def backend : Core.Backend where
  kernelAccepts := replays
  checker := "leanchecker"
  standard := #[``propext, ``Classical.choice, ``Quot.sound].map (·.toString)
  incomplete := #[``sorryAx].map (·.toString)

end LeanBlame.Export
