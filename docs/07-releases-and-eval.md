# 7. Releases and evaluation

## Stable and dev

- **`main`**: grows every day.
- **Release tag**, e.g. `2027.04`, patches `2027.04.1`: a frozen snapshot,
  fully signed and kernel-checked.

Development never stops for a release.

## What `release` does

Two gates, then a report.

1. **Signoff gate.** Every tagged declaration is `valid`. Fails otherwise.
2. **Kernel gate.** `leanchecker --from-export` replays the whole export. Fails
   on a kernel error.
3. **Axiom report.** From the export, per theorem, the axioms it rests on:
   - only the three standard axioms: **proven**;
   - includes `sorryAx`: **open**;
   - includes a tagged, signed `axiom`: **proven relative to** it, listed;
   - anything else: **fail**. The three standard axioms plus tagged, signed
     axioms are the whole permitted set. No config.

`release` never fails on open theorems. It reports how many are proven and
how many are open, by name. A reader who wants only proven results filters the
manifest. Whether a declaration claims a theorem or a conjecture is in its
informal text, which its signer signed.

Manifest fields in [14-schemas.md](14-schemas.md). The axiom report is bound
to the export hash it was computed on; `export` computes it, `release` replays
the kernel. `status` shows it per theorem and warns about an axiom that is
neither standard nor tagged and signed.

**Patch releases**: fixes to existing declarations, dependency bumps whose
changes were re-approved. A withdrawal makes a release impossible until the
declaration is approved again or removed.

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
   | Closure size, proofs excluded | `status` reports it. |
   | Review minutes | Actual human time to sign. The real objective. |
   | Later withdrawals | Did the library prevent mis-formalization? |
   | Signoff survival | How many signoffs stayed valid across upstream bumps. |

4. After six months, the declarations added to `main` are the answer to "what
   was missing." Tag `R+1`.

Fresh papers cannot have influenced `R`. The test is rolling and never runs
out.
