# 6. Versioning, changes, and blame

## The problem

A signoff was made at mathlib commit A. The library moves to commit B. Does the
signoff still hold?

Sources from two mathlib versions cannot be built together. Kernel terms can.
That distinction drives everything below.

## The check: `status`

```
leanblame export      # at commit B
leanblame status      # recompute claim hashes, look them up in records
```

Per tagged declaration X:

- **Hash matches a live record:** valid.
- **Hash differs:** outdated, with causes (`own-text`, `own-body`,
  `dep-spec`, `cut-moved`, `untagged`; see [03-trust-model.md](03-trust-model.md)),
  each naming the constants that changed under X since its last live approval.
- **A tagged dependency is not valid:** blocked by it.

Every `status` run writes a log to the object store, so a wrong "still valid"
can be traced.

## Proofs never count

A theorem's value is its proof. Proof subterms inside definition bodies are
erased before hashing too. Mathlib rewrites proofs constantly; none of that
moves a hash. For scale: the statement-level closure of one real-number
inequality, proofs excluded, was about 3,400 constants; with proofs, 13k–43k.

## `equiv`

Runs only for declarations whose sole cause is `untagged`. Any other cause
needs a human to read.

1. Fetch the old export and boundary list named in the record.
2. Compare old and new closures by hash. Constants with equal hash are
   **shared**: they are the same kernel term. Changed constants and everything
   between them and X are **duplicated** under `Old.`, with references renamed.
   Constants used only in proofs are not hashed; they are shared when the new
   export states them the same way.
3. State the goal by kind. Def with unchanged type: `Old.X = X`. Theorem:
   `type(Old.X) ↔ type(X)`. Def whose type itself changed, or a structure:
   no goal; a human reads.
4. The kernel decides, mechanically: no build, no tactics. At the frontier of
   change, each changed definition C gets `Old.C = C`, and the kernel is asked
   whether the two are definitionally equal: one kernel call per changed
   definition. Everything above follows by congruence; X's own goal is one more
   call. The accepted proofs go to the object store as an export, which
   `leanchecker` replays. Not definitionally equal: a human reads, shown the
   old and new definitions.
5. `status` shows the proof as X's `evidence`. The reviewer approves the new
   hash with one click; the record carries the proof hash as `evidence`.

Mechanism: `equiv` reads the old and the new export. It adds the duplicated
constants to the new export's environment, the kernel checking each, then the
goals with their proofs (`Eq.refl`; for `↔`, the identity both ways). The
accepted theorems and what they use are written as an export, which
`leanchecker --from-export` replays, as `release` replays the library: the
evidence is a file anyone can check again. Nothing is built or elaborated and
no `.olean` is written.

Never copy old *source* into the new build. It would elaborate against the new
mathlib, make `old = new` true by `rfl`, and prove nothing.

Renames succeed in one line. Changed structures go to a human.

The same machinery serves authoring: a new declaration provably equal to a
signed one can be replaced by it, skipping review.

## Rules for "still valid"

1. Claim hash unchanged: **valid**.
2. Only proofs changed anywhere: **valid**.
3. Only the body of a tagged dependency changed: **valid**, **blocked** until
   that dependency's signer re-approves.
4. Changed by `untagged` only, and `equiv` proved the meaning equal:
   **valid after the reviewer approves the new hash**.
5. Anything else: **outdated** until a human re-approves.

## Blame

Blame follows records. Each record says what one person approved at one hash.
Nothing is retroactive.

**Bob changes the body of `Hamiltonian`.** Alice's hash holds the spec, not
the body. It does not move. Her theorem is blocked until Bob re-signs, then
valid. Bob's page shows him everything that depends on `Hamiltonian`.

**Bob changes its type, kind or informal text.** Alice's hash moves, cause
`dep-spec`. She re-signs, shown the diff.

**A and B changed independently, both fine alone. Later, module C uses both
and is wrong.** C's signer owns C.

**A and B are incompatible, so no C can use both.** C's author writes an
adapter (new tagged content, signed by C's signer) or proposes a change
upstream.

## Policy: the later signer owns compatibility

Whoever signs second had the chance to see what was already signed. A signer
is responsible for compatibility of their declarations with the library's
conventions module as it stood at signing time.

## The conventions module

A normal tagged module, named in `leanblame.toml`. Conventions are
**declarations**: a def `hbar : ℝ := 1`, a sign choice inside a body, a
docstring stating boundary conditions. Other declarations reference them, so a
convention's spec is part of their claim hash. Changing a convention's text
re-signs everyone who uses it, which is correct.

Notation and macros are not conventions. They never reach the kernel, so they
cannot be hashed or signed. The sign server shows types with notation off, so
the reviewer sees what the kernel sees.

## Revert and withdraw

- **Revert a declaration.** `git revert` the source. The old claim hash comes
  back if nothing else under it moved, and the old record covers it.
- **Withdraw a signoff.** New record with `action = "withdraw"`, by the same
  signer. The declaration drops to `outdated` or `unsigned` with flag
  `withdrawn`; everything that depends on it shows `blocked-by`.
