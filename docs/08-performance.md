# 8. Performance

## Where time goes

Measurements by an agent on an M2 Pro with Lean 4.30, lean4export format
3.1.0, the checkers bundled with v4.35, on six small analysis and inequality
proofs. Whole-mathlib figures are from the Lean kernel arena
(arena.lean-lang.org, Lean 4.34.1, 5.8 GB export). Treat all numbers as
approximate.

| Step | Per check | Whole mathlib |
|------|-----------|---------------|
| `import Mathlib` | 3.8 s warm, 25 s cold; ~5.4 GB RSS, memory-mapped and shared | — |
| Elaborate the solution | ~1 s | — |
| Export the closure | 5–12 s; 50–250 MB | ~25 MB/s |
| Parse the export | 1–6 s | 140 s |
| Official kernel replay | 3–25 s | 2,685 s, ~10 GB |
| nanoda / con-ron / con-leche, 4 threads | 1.3–4.2 / 1.4–4.4 / 2.5–8.7 s | 359 / 176 / 526 s |
| Delta replay of new constants only (prototype) | 12–19 ms | — |

Closure work (export, parse, replay) is 60–90% of a 25–65 s check. The
submission's own elaboration is about 1 s. The AXLE paper reports a comparator
median of 95.7 s end to end, with 6.2% of runs hitting a 600 s timeout.

The dependency closure for a statement is 13k–43k mathlib constants, proofs
included. That is where the time goes, not in the submitted proof.

## Reuse what exists

- **Prebuilt base.** `lake exe cache get` for mathlib; Lake's artifact cache
  for other packages (lean-eval's `fetch_dependency_caches.sh` is a worked
  example).
- **Saved trusted side.** `--challenge-from-export`, keyed by toolchain,
  dependency commits and challenge hash. The signed module is built and
  exported once per release.
- **Per-check overlay.** Comparator Live mounts the prebuilt project read-only
  and gives each check its own writable layer (bubblewrap + overlayfs).
- **Parallel checkers.** Lake runs the checkers one after another; run them
  concurrently. con-ron and nanoda were 6–15× faster than the official kernel
  in the agent's runs. comparator issue #95 proposes parallel replay.

## Fast checkers are filters, not gates

AXLE's `verify_proof` (about 1 s) elaborates in a warm process with mathlib
loaded and does no build, export or replay. It trusts the elaborated
environment, and its own appendix shows it accepting a proof of `False`
installed with `addDeclCore (doCheck := false)`. Same class: Kimina server,
Lean REPL with saved environments, Pantograph with restored environments.

Use them to reject bad proofs early. Never accept on them. Comparator stays
the gate.

## Delta replay (later, if volume demands)

Idea: verify the base (mathlib plus library at pinned commits) once with the
kernel. Per submission, replay only the constants that are new. Prototype
kernel time: 12–19 ms instead of 3–25 s.

Why it is sound: checking a declaration depends only on the declarations it
uses. The kernel's verdict is the same whether those were checked a second ago
or a year ago. This is the weakening property of the type theory, and it is
also exactly how `import` already works: Lean never re-checks imported files.
`leanchecker` without `--fresh` already does per-module delta replay.

Requirements:

- The base is stored read-only and hash-pinned. If an attacker can swap base
  files, delta replay is unsound.
- The kernel version is pinned in the base record. A kernel soundness fix means
  the base is re-verified once with the new kernel, and a new base record is
  written.
- Comparator still compares statements against the Challenge as today.

Decision: start with full replay. Slow, but zero new trust assumptions. Add
delta replay only if throughput forces it.
