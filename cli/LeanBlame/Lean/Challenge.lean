/-
`leanblame challenge THEOREM|ID... --out DIR`, `leanblame challenge --graph` and
`leanblame challenge --check DIR` (docs/decisions.md, "Challenges").

A challenge is what a comparator checks a solution against, cut from the piece graph of the last
export (`Pieces.Graph.cut`): `Challenge.lean` states the named tagged theorems, proofs `sorry`, among
the scope commands of their modules; `ChallengeDeps.lean` holds what they need, and imports what that
needs from outside the library; `lakefile.toml` has what the library's lakefile requires;
`lean-toolchain` the library's toolchain. What stops a challenge is in the graph: it stops
`challenge`, not `export`. `--graph` prints the graph, for a service that cuts challenges itself.

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

/-- Write the challenge of the tagged theorems `names` (names or ids) into the new directory `out`. -/
def write (root out : System.FilePath) (names : Array String) : IO Unit := do
  if names.isEmpty then fail "a challenge states theorems: name at least one"
  if ← out.pathExists then fail s!"{out} exists; a challenge goes into a new directory"
  let cur ← Store.readCurrent root
  let boundary ← Status.loadBoundary root cur.boundary
  let theorems ← names.mapM fun x => do
    let some d := boundary.declarations.find? fun d => d.name == x || d.id == x
      | fail s!"{x} is not on the boundary list of the last export"
    unless d.kind == "theorem" do fail s!"{d.name} ({d.kind}) is not a theorem: a challenge states theorems"
    return d.name
  match (← Pieces.read root cur.pieces).cut (dedup theorems) with
  | .error problems =>
    fail ("this challenge cannot be made:\n" ++ "\n".intercalate (problems.toList.map ("  " ++ ·)))
  | .ok files =>
    IO.FS.createDirAll out
    for (f, text) in files do IO.FS.writeFile (out / f) text

/-- The piece graph of the last export (docs/schemas.md §6). -/
def graph (root : System.FilePath) : IO Pieces.Graph := do
  Pieces.read root (← Store.readCurrent root).pieces

/-- Build the challenge in `dir` against the library's build and compare the claims of the tagged
declarations it holds with the last export's; where they differ, the kernel decides whether the
challenge's declaration is definitionally equal to the library's. Returns how many it compared, and
how many of them the kernel decided. Any other difference is an error. -/
def check (root dir : System.FilePath) : IO (Nat × Nat) := do
  let cur ← Store.readCurrent root
  let lib ← Status.currentGraph root cur
  let (sysroot, leanPath, _) ← Export.lakeEnvPaths root
  let mods := #[`ChallengeDeps, `Challenge]
  -- The library's private constants, by user name, for the challenge's.
  let libPrivate : Std.HashMap Name Name := lib.nodes.fold (init := {}) fun acc s _ =>
    match Pieces.nameOf? s with
    | some n => if isPrivateName n then acc.insert (privateToUserName n) n else acc
    | none => acc
  let libModules : NameSet := cur.modules.foldl (·.insert ·.toName) {}
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
    unless problems.isEmpty do
      let kernel := proven.notes.flatMap fun (line, detail) => #[line] ++ detail.map ("  " ++ ·)
      fail ("the challenge does not mean what the library means:\n" ++ "\n".intercalate (problems.toList.map ("  " ++ ·)) ++
        (if kernel.isEmpty then "" else "\nthe kernel:\n" ++ "\n".intercalate (kernel.toList.map ("  " ++ ·))))
    return (present.size, differ.size)
  finally IO.FS.removeDirAll tmp

end LeanBlame.Challenge
