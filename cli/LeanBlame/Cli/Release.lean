/-
`leanblame release --tag TAG [--out FILE]` (docs/07-releases-and-eval.md, docs/14-schemas.md §3).

Two gates and a report, on the current export:
1. signoff: every tagged declaration is `valid`;
2. kernel: `leanchecker --silent --from-export` replays the export, as `lake check` runs it;
3. axioms: no tagged theorem rests on an axiom that is neither standard nor a tagged, signed
   axiom (from `status`; open theorems are counted, not failed).
Then the manifest goes to the object store, and to FILE with `--out`.
-/
import LeanBlame.Cli.Status

namespace LeanBlame.Release

open Lean

def run (root : System.FilePath) (tag : String) (out? : Option System.FilePath) : IO UInt32 := do
  let cfg ← Config.load root
  let (all, bad) ← loadAllRecords root cfg
  for (p, _) in bad do
    IO.eprintln s!"warning: {p} is not a valid record and was ignored (see `leanblame validate`)"
  let r ← Status.compute root cfg (Ledger.build cfg all) none (causes := false) (warn := false)
  let decls := r.report.declarations
  -- 1. Signoff gate.
  let invalid := decls.filter (·.2.state != "valid")
  unless invalid.isEmpty do
    for (n, d) in invalid do IO.eprintln (Status.textLine n d)
    IO.eprintln s!"release: {invalid.size} of {decls.size} tagged declarations are not valid"
    return 1
  -- 2. Kernel gate.
  let cur ← Store.readCurrent root
  let exportPath := Store.objectPath root cur.exportHash
  unless ← exportPath.pathExists do fail s!"export {cur.exportHash} is not in the store"
  let leanchecker := (← findSysroot) / "bin" / "leanchecker"
  let checker ← IO.Process.spawn { cmd := leanchecker.toString, stdin := .null, stdout := .null
                                   args := #["--silent", "--from-export", exportPath.toString] }
  unless (← checker.wait) == 0 do
    IO.eprintln "release: kernel rejected the export"
    return 1
  -- 3. Axiom gate.
  unless r.unpermitted.isEmpty do
    for (t, a) in r.unpermitted do
      IO.eprintln s!"release: theorem {t} rests on axiom {a}, which is neither standard nor tagged and signed"
    return 1
  -- 4. The manifest.
  let b ← Status.loadBoundary root cur.boundary
  let manifest : ReleaseManifest := {
    library := b.library, tag, commit := b.commit, toolchain := b.toolchain, deps := b.deps
    exportHash := cur.exportHash, boundary := cur.boundary, records := r.validRecords
    theorems := (decls.filter (·.2.kind == "theorem")).map fun (n, d) => (n, d.proof) }
  let text := jsonText manifest
  let hash ← Store.putString root text
  if let some out := out? then writeFileMkdirs out text
  IO.println s!"release {hash} {Store.objectPath root hash}"
  return 0

end LeanBlame.Release
