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
- **Hash differs:** outdated. `status --base A.export` names the dependencies
  that changed. Run `equiv`.
- **A tagged dependency is not valid:** blocked by it. Nothing for X's signer
  to do.

## Proofs never count

A theorem's value is its proof. Mathlib rewrites proofs constantly. Proofs
cannot change what anything means, so the claim hash skips them. One
agent-measured closure of a real-number inequality held about 3,275 theorems;
none of their proofs can trigger a re-sign.

## `equiv`

For an outdated declaration X whose untagged dependencies changed:

1. Read X's old closure from the old export named in the record.
2. Add those constants to the current environment as kernel terms under the
   namespace `Old.`, renaming references accordingly. Tagged dependencies are
   shared, not duplicated.
3. Ask an agent to prove `Old.X = X` (or `Old.X ↔ X` for propositions).
4. Check the proof with `lake comparator`. Store it in the object store.
5. Mark X **equiv-proven**. The reviewer approves the new hash with one click;
   the record carries the proof hash as `evidence`.

Never copy the old *source* into the new build. It would elaborate against the
new mathlib, make `old = new` true by `rfl`, and prove nothing.

Limits: for structures and type classes "equal" is often the wrong notion.
Those go to a human. Renames and field reorders succeed in one line.

The same machinery serves authoring: a new declaration provably equal to a
signed one can be replaced by it, skipping review.

## Rules for "still valid"

1. Claim hash unchanged: **valid**.
2. Only proofs changed anywhere: **valid**.
3. Only the body of a tagged dependency changed: **valid**, **blocked** until
   that dependency's signer re-approves.
4. Changed, and `equiv` proved the meaning equal: **valid after the reviewer
   approves the new hash**.
5. Anything else: **outdated** until re-approved.

Every `status` run is logged.

## Blame

Blame follows records. Each record says what one person approved at one hash.
Nothing is retroactive.

**Bob changes the body of `Hamiltonian`.** Alice's theorem holds
`Hamiltonian`'s spec, not its body. Her hash does not move. Her theorem is
blocked until Bob re-signs, then valid. Bob's page shows him everything that
depends on `Hamiltonian` before he signs.

**Bob changes its type or informal text.** Alice's hash moves. She re-signs,
shown the diff.

**A and B changed independently, both fine alone. Later, module C uses both and
is wrong.** C's signer owns C. C's record stores the hashes it was approved
against.

**A and B are incompatible, so no C can use both.** C's author writes an
adapter (new tagged content, signed by C's signer) or proposes a change to A or
B upstream, which goes through their signoff.

## Policy: the later signer owns compatibility

Whoever signs second had the chance to see what was already signed. A signer
is responsible for compatibility of their declarations with the library's
conventions module as it stood at signing time.

## The conventions module

A normal tagged module, named in `leanblame.toml`. Its declarations and
notations carry informal text stating units, sign conventions, normalizations,
boundary conditions. Other declarations reference them, so a convention's spec
is part of their claim hash. Changing a convention's text re-signs everyone who
uses it, which is correct.

## Revert and withdraw

- **Revert a declaration.** `git revert` the source. The old claim hash comes
  back if nothing else under it moved, and the old record covers it.
- **Withdraw a signoff.** New record with `action = "withdraw"`. The
  declaration drops to `outdated` or `unsigned` with flag `withdrawn`;
  everything that depends on it shows `blocked-by`.
