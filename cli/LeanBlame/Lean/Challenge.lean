/-
`leanblame challenge [THEOREM|ID...] --out DIR` and `leanblame challenge --check DIR`
(docs/design/04-architecture.md, "Challenges").

A challenge is what a comparator checks a solution against, joined from the pieces of the last
export: `ChallengeDeps.lean` imports what the library's modules import from outside it and holds
every piece without a statement, module after module, which is what the tagged declarations need and
the same for every challenge of the library; `Challenge.lean` holds the statements of the named
tagged theorems, proofs `sorry`, among the scope commands of their modules; `lakefile.toml` has what
the library's lakefile requires; `lean-toolchain` the library's toolchain. What stops a challenge
(`Store.ChallengeProblem`, found by `export`) stops `challenge`, not `export`.

`--check` builds the challenge with `lean` against the library's build, as a comparator builds it,
in the store's temporary space, imports it and hashes its own declarations in memory as `export`
hashes the library (`Source.declsIn`, `Walk.hashNodes`); what it imports from outside the library is
the library's build, whose hashes the last export has. Each tagged declaration it holds must have the
claim it has in the last export, or else be definitionally equal to the library's: the kernel decides,
as `equiv` decides between two exports (`Equiv.prove`), against the library's versions of what
differs, read from the compiled files of the modules that declare them. Lean may write a challenge's
terms differently from the library's (in one file, a `match` can share the helper Lean made for
another module's); a solution of the challenge then still proves the library's theorem. A private
name holds the module it was written in; the challenge's private constants are named as the
library's: by their user names, or by the module a name written with its module
(`Pieces.withModule`) gives.
-/
import LeanBlame.Core.Status
import LeanBlame.Lean.Equiv
import LeanBlame.Lean.Export
import LeanBlame.Lean.Pieces
import LeanBlame.Lean.Source

namespace LeanBlame.Challenge

open Lean

/-- LeanBlame's own package: a challenge drops `@[trusted]` and imports nothing of LeanBlame. -/
def leanblamePackage : String := "leanblame"

/-- What the modules with pieces import from outside the library, through the library's modules they
import. -/
def importsOf (modules : Array OwnModule) : Array String := Id.run do
  let byName : Std.HashMap String OwnModule := modules.foldl (fun m o => m.insert o.name o) {}
  let mut out := #[]
  let mut seen : Std.HashSet String := {}
  let mut todo := (modules.filter (·.pieces.isSome)).map (·.name)
  while h : todo.size > 0 do
    let m := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    for i in (byName[m]?.map (·.imports)).getD #[] do
      if byName.contains i then todo := todo.push i
      else if !out.contains i then out := out.push i
  return out.qsort (· < ·)

/-- A TOML string. -/
def tomlString (s : String) : String := (Json.str s).compress

/-- The challenge's `lakefile.toml`: what the library's lakefile requires (by git; LeanBlame left
out), and the libraries `ChallengeDeps` and, with statements, `Challenge`. Each module's part of the
challenge sets the Lean options Lake builds that module with. -/
def lakefile (needs : Array Require) (stated : Bool) : IO String := do
  let reqs ← (needs.filter (·.name != leanblamePackage)).toList.mapM fun r => do
    let some git := r.git | fail s!"{r.name} is required by path; a challenge requires it by git"
    return "\n".intercalate (["[[require]]", s!"name = {tomlString r.name}", s!"git = {tomlString git}"] ++
      (r.rev.map (s!"rev = {tomlString ·}")).toList ++ (r.subDir.map (s!"subDir = {tomlString ·}")).toList)
  let libs := ["ChallengeDeps"] ++ (if stated then ["Challenge"] else [])
  return "\n\n".intercalate (["name = \"challenge\""] ++ reqs ++
    libs.map (s!"[[lean_lib]]\nname = \"{·}\"")) ++ "\n"

/-- Write the challenge of the tagged theorems `names` (names or ids; none: `ChallengeDeps.lean`
alone) into the new directory `out`. -/
def write (root out : System.FilePath) (names : Array String) : IO Unit := do
  if ← out.pathExists then fail s!"{out} exists; a challenge goes into a new directory"
  let cur ← Store.readCurrent root
  let boundary ← Status.loadBoundary root cur.boundary
  let theorems ← names.mapM fun x => do
    let some d := boundary.declarations.find? fun d => d.name == x || d.id == x
      | fail s!"{x} is not on the boundary list of the last export"
    unless d.role == .proved do fail s!"{d.name} is not a theorem: a challenge states theorems"
    return d.name
  let stops := cur.challengeProblems.filter (·.name.all theorems.contains)
  unless stops.isEmpty do
    fail ("this challenge cannot be made:\n" ++ "\n".intercalate (stops.toList.map fun p =>
      s!"  {p.name.getD "every challenge"}: {p.problem}"))
  let modules ← cur.modules.filterMapM fun m => m.pieces.mapM (Pieces.read root ·)
  let isNamed (p : Pieces.Piece) := p.statement.any (theorems.contains ·.name)
  for t in theorems do
    unless modules.any (·.pieces.any (·.statement.any (·.name == t))) do
      fail s!"{t} is a theorem of another library: its challenge is that library's"
  let deps := modules.flatMap fun m => (m.pieces.filter (·.statement.isNone)).map (·.text)
  let stated := modules.filter (·.pieces.any isNamed) |>.flatMap fun m =>
    m.pieces.filterMap fun p => match p.statement with
      | some st => if theorems.contains st.name then some st.text else none
      | none => if p.scope then some p.text else none
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "ChallengeDeps.lean") <|
    String.join ((importsOf cur.modules).toList.map (s!"import {·}\n")) ++ "\n" ++ "\n\n".intercalate deps.toList ++ "\n"
  unless theorems.isEmpty do
    IO.FS.writeFile (out / "Challenge.lean") ("import ChallengeDeps\n\n" ++ "\n\n".intercalate stated.toList ++ "\n")
  IO.FS.writeFile (out / "lakefile.toml") (← lakefile cur.requires !theorems.isEmpty)
  IO.FS.writeFile (out / "lean-toolchain") s!"leanprover/lean4:{cur.toolchain}\n"

/-- Build the challenge in `dir` against the library's build and compare the claims of the tagged
declarations it holds with the last export's; where they differ, the kernel decides whether the
challenge's declaration is definitionally equal to the library's. Returns how many it compared, and
how many of them the kernel decided. Any other difference, or a tagged declaration of the library
other than a theorem that the challenge lacks, is an error. -/
def check (root dir : System.FilePath) : IO (Nat × Nat) := do
  let cur ← Store.readCurrent root
  let lib ← Status.currentGraph root cur
  let (sysroot, leanPath, _) ← Export.lakeEnvPaths root
  let mods := #[`ChallengeDeps] ++ (if ← (dir / "Challenge.lean").pathExists then #[`Challenge] else #[])
  -- The library's private constants, by user name, for the challenge's.
  let libPrivate : Std.HashMap Name Name := lib.nodes.fold (init := {}) fun acc s _ =>
    match Pieces.nameOf? s with
    | some n => if isPrivateName n then acc.insert (privateToUserName n) n else acc
    | none => acc
  let libModules : NameSet := cur.modules.foldl (·.insert ·.name.toName) {}
  let challengePrivate := mods.map (mkPrivateNameCore · .anonymous)
  let rename (n : Name) : Name :=
    if !(privatePrefix? n).any challengePrivate.contains then n else
    match Pieces.unclash? libModules (privateToUserName n) with
    | some (m, u) => mkPrivateNameCore m u
    | none => (libPrivate[privateToUserName n]?).getD n
  -- Built and imported in the store's temporary space; `dir` stays as it is.
  let tmp ← Store.tmpPath root "challenge"
  try
    let build := tmp / "build"
    IO.FS.createDirAll build
    let path := System.SearchPath.toString (build :: leanPath)
    for m in mods do
      let out ← IO.Process.output { cmd := (sysroot / "bin" / "lean").toString, cwd := dir
                                    args := #[s!"{m}.lean", "-o", (build / s!"{m}.olean").toString]
                                    env := #[("LEAN_PATH", some path)] }
      unless out.exitCode == 0 do fail s!"{dir / s!"{m}.lean"} does not build:\n{out.stdout}{out.stderr}"
    initSearchPath sysroot (build :: leanPath)
    -- Without environment extensions, as an export rebuilds its constants (`Source.declsIn`).
    let env ← importModules (mods.map ({ module := · })) {} (loadExts := false)
    let present := lib.boundary.declarations.filter fun d => (Pieces.nameOf? d.name).any env.contains
    let boundary := { lib.boundary with declarations := present }
    -- What the challenge imports from outside the library is the library's own build: those
    -- declarations keep the library's hashes, and only the challenge's own are hashed.
    let outside (s : String) := (lib.nodes[s]?).filter (!libModules.contains ·.decl.module.toName)
    let decl ← Source.declsIn env (present.filterMap (Pieces.nameOf? ·.name))
      (fun n => IO.ofExcept (Export.moduleOf env n)) rename
    let h : Core.Hashed := { lib with nodes := ← Walk.hashNodes decl boundary outside, boundary, axioms := {} }
    let claim (g : Core.Hashed) (s : String) := g.nodes[s]?.map (·.claim)
    let differ := present.filter fun d => claim lib d.name != claim h d.name
    -- Where claims differ, the kernel decides, in the challenge's environment, against the library's
    -- versions of what differs, read from the compiled files of the modules that declare them.
    let changed : Std.HashSet String := .ofArray <| differ.flatMap fun d =>
      ((Walk.closureOf lib d.name).2.push d.name).filter fun s => claim lib s != claim h s
    let mut consts : Std.HashMap Name ConstantInfo := {}
    let mut pos : Std.HashMap Name Nat := {}
    for m in dedup (changed.toArray.filterMap (lib.nodes[·]?.map (·.decl.module.toName))) do
      for ci in ← Load.moduleConstants m do
        pos := pos.insert ci.name pos.size
        if changed.contains ci.name.toString then consts := consts.insert ci.name ci
    -- The challenge's names of the library's private constants.
    let own := mods.flatMap fun m =>
      ((env.getModuleIdx? m).bind (env.header.moduleData[·.toNat]?)).map (·.constNames) |>.getD #[]
    let toNew : Std.HashMap Name Name := own.foldl (init := {}) fun acc c => if rename c == c then acc else acc.insert (rename c) c
    let proven ← Equiv.prove env.toKernelEnv
      { old := lib, new := h, oldConst? := (consts[·]?), newConst? := fun n => env.find? (toNew.getD n n)
        toNew := fun n => toNew.getD n n, oldPos := (pos.getD · 0) } (differ.filterMap (Pieces.nameOf? ·.name))
    let mut problems := #[]
    for d in differ do
      unless proven.targets.any (·.toString == d.name) do
        problems := problems.push <| match Walk.compare lib h d.name d.name with
          | .ok cmp => s!"{d.name} {Status.changeText (cmp.changes d.name)}"
          | .error e => s!"{d.name}: {e}"
    for d in lib.boundary.declarations do
      if d.role != .proved && libModules.contains d.module.toName && !present.any (·.name == d.name) then
        problems := problems.push s!"{d.name} missing"
    unless problems.isEmpty do
      let kernel := proven.notes.flatMap fun (line, detail) => #[line] ++ detail.map ("  " ++ ·)
      fail ("the challenge does not mean what the library means:\n" ++ "\n".intercalate (problems.toList.map ("  " ++ ·)) ++
        (if kernel.isEmpty then "" else "\nthe kernel:\n" ++ "\n".intercalate (kernel.toList.map ("  " ++ ·))))
    return (present.size, differ.size)
  finally IO.FS.removeDirAll tmp

end LeanBlame.Challenge
