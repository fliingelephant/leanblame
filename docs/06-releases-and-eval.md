# 6. Releases and evaluation

## Stable and dev

- **`main`**: grows every day, like mathlib. New definitions land here.
- **Release tag `R`**: a frozen snapshot. Fully signed.

Development never stops for a release. The tag is a photograph of `main`.

## A release is a fully signed snapshot

Contents of a release manifest:

- Lean toolchain version
- dependency commits (mathlib, physlib, …) from `lake-manifest.json`
- library commit
- export file and its hash
- the list of records that cover every constant in every trusted module

Cut a release when everything is signed, not on a calendar.

**Patch releases** (`R.1`, `R.2`): fixes to existing definitions, dependency
bumps whose changes passed `equiv` and were re-approved, withdrawals. No new definitions.

**Downstream** pins a release, exactly as projects pin a mathlib commit today.
Mathlib itself has no releases; a LeanBlame release is what gives users
something stable to cite.

## Evaluation on fresh results

Question: how good is the library at expressing new results in its field?

Design:

1. Freeze release `R`.
2. For six months, every new paper in scope is a test item. Formalize its main
   result using `R` only. Do not touch `main` for this.
3. Record, per item:

   | Metric | Why |
   |--------|-----|
   | New definitions needed | Zero is perfect. The missing ones are the to-add list. |
   | Size of the Challenge file | What the human must read. Smaller means better abstractions. |
   | Closure size | Number of constants under the statement. Comparator computes it. |
   | Review minutes | Actual human time to sign. The real objective. |
   | Later withdrawals | Did the library prevent mis-formalization? |
   | Signoff survival | How many signoffs stayed valid across upstream bumps. |

4. After six months, the definitions added to `main` in the meantime are the
   answer to "what was missing". Tag `R+1`.

Fresh papers cannot have influenced `R`, because `R` predates them. The test is
rolling: each paper is measured against the most recent release that preceded
it. The test set never runs out.
