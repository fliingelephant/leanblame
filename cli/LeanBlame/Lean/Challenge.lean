/-
`leanblame challenge [THEOREM|ID...] --out DIR` and `leanblame challenge --check DIR`
(docs/design/04-architecture.md, "Challenges").

A challenge is what a comparator checks a solution against, joined from the pieces of the last
export: `ChallengeDeps.lean` imports what the library's modules import from outside it and holds
every piece without a statement, module after module, which is what the tagged declarations need and
the same for every challenge of the library; `Challenge.lean` holds the statements of the named
tagged theorems, proofs `sorry`, among the scope commands of their modules; `lakefile.toml` has the
library's Lean options and what its lakefile requires; `lean-toolchain` the library's toolchain.

`--check` builds the challenge with `lean` against the library's build, as a comparator builds it,
in the store's temporary space, and hashes it as `export` hashes the library (`Walk.hashExport`):
each tagged declaration it holds must have the claim it has in the last export, so the challenge
means what the signers signed. A private name holds the module it was written in; the challenge's
private constants are named as the library's, by their user names.
-/
import LeanBlame.Core.Status
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

/-- The challenge's `lakefile.toml`: the library's Lean options and what its lakefile requires (by
git; LeanBlame left out), and the libraries `ChallengeDeps` and, with statements, `Challenge`. -/
def lakefile (options : Json) (needs : Array Require) (stated : Bool) : IO String := do
  let .obj kvs := options | fail "the Lean options of the last export are not an object"
  let opts := kvs.toList.map fun (k, v) => s!"{k} = {v.compress}"
  let reqs ← (needs.filter (·.name != leanblamePackage)).toList.mapM fun r => do
    let some git := r.git | fail s!"{r.name} is required by path; a challenge requires it by git"
    return "\n".intercalate (["[[require]]", s!"name = {tomlString r.name}", s!"git = {tomlString git}"] ++
      (r.rev.map (s!"rev = {tomlString ·}")).toList ++ (r.subDir.map (s!"subDir = {tomlString ·}")).toList)
  let libs := ["ChallengeDeps"] ++ (if stated then ["Challenge"] else [])
  return "\n\n".intercalate (["name = \"challenge\"", "\n".intercalate ("[leanOptions]" :: opts)] ++ reqs ++
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
  IO.FS.writeFile (out / "lakefile.toml") (← lakefile cur.leanOptions cur.requires !theorems.isEmpty)
  IO.FS.writeFile (out / "lean-toolchain") s!"leanprover/lean4:{cur.toolchain}\n"

/-- `-D` arguments of `lean` for Lean options as Lake's `leanOptions` writes them. -/
def optionArgs (options : Json) : IO (Array String) := do
  let .obj kvs := options | fail "the Lean options of the last export are not an object"
  return kvs.toArray.map fun (k, v) => s!"-D{k}={match v with | .str s => s | v => v.compress}"

/-- Build the challenge in `dir` against the library's build and compare the claims of the tagged
declarations it holds with the last export's. Returns how many it compared; a difference, or a
tagged declaration of the library other than a theorem that it lacks, is an error. -/
def check (backend : Core.Backend) (root dir : System.FilePath) : IO Nat := do
  let cur ← Store.readCurrent root
  let lib ← Status.currentGraph root cur
  let (sysroot, leanPath, _) ← Export.lakeEnvPaths root
  let mods := #[`ChallengeDeps] ++ (if ← (dir / "Challenge.lean").pathExists then #[`Challenge] else #[])
  let args ← optionArgs cur.leanOptions
  -- The library's private constants, by user name, for the challenge's.
  let libPrivate : Std.HashMap Name Name := lib.nodes.fold (init := {}) fun acc s _ =>
    match Pieces.nameOf? s with
    | some n => if isPrivateName n then acc.insert (privateToUserName n) n else acc
    | none => acc
  let challengePrivate := mods.map (mkPrivateNameCore · .anonymous)
  let rename (n : Name) : Name :=
    if (privatePrefix? n).any challengePrivate.contains then (libPrivate[privateToUserName n]?).getD n else n
  -- Built and exported in the store's temporary space; `dir` stays as it is.
  let tmp ← Store.tmpPath root "challenge"
  let (present, h) ← try
      let build := tmp / "build"
      IO.FS.createDirAll build
      let path := System.SearchPath.toString (build :: leanPath)
      for m in mods do
        let out ← IO.Process.output { cmd := (sysroot / "bin" / "lean").toString, cwd := dir
                                      args := args ++ #[s!"{m}.lean", "-o", (build / s!"{m}.olean").toString]
                                      env := #[("LEAN_PATH", some path)] }
        unless out.exitCode == 0 do fail s!"{dir / s!"{m}.lean"} does not build:\n{out.stdout}{out.stderr}"
      initSearchPath sysroot (build :: leanPath)
      let env ← importModules (mods.map ({ module := · })) {} (loadExts := false)
      let present := lib.boundary.declarations.filter fun d => (Pieces.nameOf? d.name).any env.contains
      let exported := tmp / "export"
      discard <| Export.dumpToFile env (present.filterMap (Pieces.nameOf? ·.name)) exported
      let src ← Source.ofExport (← Source.parseFile exported) (fun n => IO.ofExcept (Export.moduleOf env n)) rename
      pure (present, ← Walk.hashExport backend src { lib.boundary with declarations := present } "" "")
    finally IO.FS.removeDirAll tmp
  let mut problems := #[]
  for d in present do
    let (some n, some c) := (lib.nodes[d.name]?, h.nodes[d.name]?) | continue
    if n.claim != c.claim then
      problems := problems.push <| match Walk.compare lib h d.name d.name with
        | .ok cmp => s!"{d.name} {Status.changeText (cmp.changes d.name)}"
        | .error e => s!"{d.name}: {e}"
  let libModules := cur.modules.map (·.name)
  for d in lib.boundary.declarations do
    if d.role != .proved && libModules.contains d.module && !present.any (·.name == d.name) then
      problems := problems.push s!"{d.name} missing"
  unless problems.isEmpty do
    fail ("the challenge does not mean what the library means:\n" ++ "\n".intercalate (problems.toList.map ("  " ++ ·)))
  return present.size

end LeanBlame.Challenge
