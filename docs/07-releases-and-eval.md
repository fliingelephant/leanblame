# 7. Releases and evaluation

## Stable and dev

- **`main`**: grows every day. New declarations land here.
- **Release tag `R`**: a frozen snapshot. Fully signed and kernel-checked.

Development never stops for a release.

## A release is a fully signed, fully checked snapshot

`release` does two things and fails if either fails:

1. **Signoff gate.** Every tagged declaration is `valid`.
2. **Proof gate.** `lake check --paranoid` with the library's permitted axioms.
   Each theorem is recorded as **proven** (axioms listed) or **open** (`sorry`).
   A theorem whose informal text claims a result but is open fails the release.

Manifest contents: toolchain, dependency commits, library commit, export hash,
boundary list, the records that cover every tagged declaration, the
proven/open table.

**Patch releases** (`R.1`, `R.2`): fixes to existing declarations, dependency
bumps whose changes passed `equiv` and were re-approved, withdrawals. No new
declarations.

**Downstream** pins a release. Mathlib tags one commit per Lean release but has
no version scheme of its own; a LeanBlame release is what gives users
something stable to cite.

## Evaluation on fresh results

Question: how good is the library at expressing new results in its field?

1. Freeze release `R`.
2. For six months, every new paper in scope is a test item. Formalize its main
   result using `R` only.
3. Record, per item:

   | Metric | Why |
   |--------|-----|
   | New declarations needed | Zero is perfect. The missing ones are the to-add list. |
   | Size of what the reviewer must read | Smaller means better abstractions. |
   | Closure size | Number of constants under the statement. `status` reports it. |
   | Review minutes | Actual human time to sign. The real objective. |
   | Later withdrawals | Did the library prevent mis-formalization? |
   | Signoff survival | How many signoffs stayed valid across upstream bumps. |

4. After six months, the declarations added to `main` are the answer to "what
   was missing." Tag `R+1`.

Fresh papers cannot have influenced `R`. The test is rolling and never runs
out.
