# 9. Performance

## Where time goes

Measured by an agent on an M2 Pro, Lean 4.30, six small analysis proofs.
Approximate.

| Step | Per check |
|------|-----------|
| `import Mathlib` | 3.8 s if files are cached in RAM, 25 s from disk; 5.4 GB memory, shared between processes |
| Elaborate the submitted proof | ~1 s |
| Export the dependency closure | 5–12 s; 50–250 MB |
| Parse the export | 1–6 s |
| Official kernel replay of the closure | 3–25 s |
| nanoda / con-ron / con-leche, 4 threads | 1.3–4.2 / 1.4–4.4 / 2.5–8.7 s |
| Replay of only the new constants (prototype) | 12–19 ms |

The closure is 13k–43k mathlib constants. Exporting, parsing and replaying it is
60–90% of a 25–65 s check. The submitted proof itself is about 1 s. The AXLE
paper reports a comparator median of 95.7 s end to end, with 62 of 1000 runs
hitting a 600 s timeout.

## Reuse what exists

- **Prebuilt base.** `lake exe cache get`; Lake's artifact cache.
- **Saved exports.** The current export is reused by every `status` run.
- **Per-check overlay.** Comparator Live's pattern: prebuilt project mounted
  read-only, each check writes to its own layer.
- **Parallel checkers.** Run the external checkers concurrently. con-ron and
  nanoda were 6–15× faster than the official kernel in the agent's runs.

## Fast checkers are filters, not gates

AXLE's `verify_proof` takes about 1 s because it skips build, export and kernel
replay. It trusts that everything in its loaded environment was kernel-checked.
Its own appendix shows it accepting a proof of `False` added with checking
turned off. Kimina, the Lean REPL and Pantograph with saved environments share
this weakness.

Use them to reject bad proofs early. Never accept on them. The kernel, through
`lake check` and `lake comparator`, stays the gate.

## Delta replay (later, if volume demands)

Verify the base (mathlib plus library at pinned commits) once with the kernel.
Per submission, replay only the new constants. Prototype: 12–19 ms instead of
3–25 s.

Why it is sound: the kernel checks a declaration against only the declarations
it uses. Checking those again changes nothing. Lean already relies on this:
imported files are never re-checked. `leanchecker` without `--fresh` does
per-module delta replay today.

Requirements: base stored read-only and hash-pinned; kernel version pinned in
the base record; re-verify the base once when the kernel changes.

Decision: start with full replay. Add delta replay only if throughput forces it.
