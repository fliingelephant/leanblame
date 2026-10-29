/-
`leanblame release --tag TAG [--out FILE]` (docs/decisions.md, "Releases"; docs/schemas.md §3).

Two gates and a report, on the current export:
1. signoff: every tagged declaration is `valid`;
2. kernel: the proof assistant's checker replays the export (`Core.Backend.kernelAccepts`; Lean:
   `leanchecker --silent --from-export`, as `lake check` runs it);
3. axioms: no tagged theorem rests on an axiom that is neither standard nor a tagged, signed
   axiom (from `status`; open theorems are counted, not failed).
Then the manifest goes to the object store, and to FILE with `--out`. Its theorems are the tagged
declarations with role `proved` (trust-model.md).
-/
import LeanBlame.Core.Status

namespace LeanBlame.Release

def run (backend : Core.Backend) (root : System.FilePath) (tag : String)
    (out? : Option System.FilePath) : IO UInt32 := do
  let r ← Status.compute root (← Ledger.load root)
  let decls := r.report.declarations
  -- 1. Signoff gate.
  let invalid := decls.filter (·.state != .valid)
  unless invalid.isEmpty do
    for d in invalid do IO.eprintln (Status.textLine d)
    IO.eprintln s!"release: {invalid.size} of {decls.size} tagged declarations are not valid"
    return 1
  -- 2. Kernel gate.
  unless ← backend.kernelAccepts (Store.objectPath root .exports r.cur.exportHash) do
    IO.eprintln "release: kernel rejected the export"
    return 1
  -- 3. Axiom gate.
  let unpermitted := decls.flatMap fun d => d.proof.unpermitted.map (d.decl.name, ·)
  unless unpermitted.isEmpty do
    for (t, a) in unpermitted do
      IO.eprintln s!"release: theorem {t} rests on axiom {a}, which is neither standard nor tagged and signed"
    return 1
  -- 4. The manifest, which names the commit.
  let cur := r.cur
  let some commit := cur.commit
    | fail "release: the current export has uncommitted changes; commit them and export again"
  let manifest : ReleaseManifest := {
    library := r.new.boundary.library, tag, commit, toolchain := cur.toolchain, deps := cur.deps
    exportHash := cur.exportHash, boundary := cur.boundary, records := r.validRecords
    checker := r.new.checker
    theorems := (decls.filter (·.decl.role == .proved)).map fun d => (d.decl.name, d.proof) }
  let text := jsonText manifest
  let hash ← Store.putString root .manifests text
  if let some out := out? then writeFileMkdirs out text
  IO.println s!"release {hash} {Store.objectPath root .manifests hash}"
  return 0

end LeanBlame.Release
