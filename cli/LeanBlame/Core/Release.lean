/-
`leanblame release --tag TAG [--out FILE]` (docs/design/07-releases-and-eval.md, docs/design/14-schemas.md §3).

Two gates and a report, on the current export:
1. signoff: every tagged declaration is `valid`;
2. kernel: the proof assistant's checker replays the export (`Core.Backend.kernelAccepts`; Lean:
   `leanchecker --silent --from-export`, as `lake check` runs it);
3. axioms: no tagged theorem rests on an axiom that is neither standard nor a tagged, signed
   axiom (from `status`; open theorems are counted, not failed).
Then the manifest goes to the object store, and to FILE with `--out`. Its theorems are the tagged
declarations with role `proved` (docs/design/15-generic-core.md).
-/
import LeanBlame.Core.Status

namespace LeanBlame.Release

def run (backend : Core.Backend) (root : System.FilePath) (tag : String)
    (out? : Option System.FilePath) : IO UInt32 := do
  let r ← Status.compute root (← Ledger.load root) (causes := false) (warn := false)
  let decls := r.report.declarations
  -- 1. Signoff gate.
  let invalid := decls.filter (·.2.state != .valid)
  unless invalid.isEmpty do
    for (n, d) in invalid do IO.eprintln (Status.textLine n d)
    IO.eprintln s!"release: {invalid.size} of {decls.size} tagged declarations are not valid"
    return 1
  -- 2. Kernel gate.
  unless ← backend.kernelAccepts (Store.objectPath root .exports r.cur.exportHash) do
    IO.eprintln "release: kernel rejected the export"
    return 1
  -- 3. Axiom gate.
  unless r.unpermitted.isEmpty do
    for (t, a) in r.unpermitted do
      IO.eprintln s!"release: theorem {t} rests on axiom {a}, which is neither standard nor tagged and signed"
    return 1
  -- 4. The manifest.
  let b := r.new.boundary
  let manifest : ReleaseManifest := {
    library := b.library, tag, commit := b.commit, toolchain := b.toolchain, deps := b.deps
    exportHash := r.cur.exportHash, boundary := r.cur.boundary, records := r.validRecords
    checker := r.new.checker
    theorems := (decls.filter (·.2.role == .proved)).map fun (n, d) => (n, d.proof) }
  let text := jsonText manifest
  let hash ← Store.putString root .manifests text
  if let some out := out? then writeFileMkdirs out text
  IO.println s!"release {hash} {Store.objectPath root .manifests hash}"
  return 0

end LeanBlame.Release
