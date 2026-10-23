# 5. Versioning, changes, and blame

## The problem

A signoff was made at mathlib commit A. The library moves to commit B. Does the
signoff still hold?

Two mathlib versions cannot coexist in one build. So the question is never
"use the old definition"; it is always "does the attestation survive the
upgrade".

## The check: `status --base`

```
leanblame export            # at commit A  -> A.export
leanblame export            # at commit B  -> B.export
leanblame status --base A.export
```

`status` runs comparator with `--challenge-from-export A.export
--solution-from-export B.export` and the `@[trusted]` constants as targets.
Comparator walks the dependency closure and either passes or names the first
constant that differs.

- **Pass:** the signoff carries to B. Nothing to do.
- **Fail on constant X:** X is **outdated**. Run `equiv`.

No separate hash tool is needed. Comparator is the hash tool.

## Caveat: proof bodies count as changes

Comparator compares the value of every constant in the closure, and for a
theorem the value is its proof. Mathlib rewrites proofs constantly. Routine
proof golfing therefore shows up as "changed" even though no meaning changed.
An agent survey found a statement-only closure for one real-number inequality
pulled in about 3,275 theorems.

Fix: a **statements-only mode** for comparator that compares theorem types but
skips theorem values, while still comparing definition values. Small patch to
`Compare.lean` in our pinned fork of the archived standalone comparator. Until
it is in, expect noise and expect `equiv` to resolve most of it trivially.

## `equiv`

For changed constant X:

1. Take X's old source from git at commit A, with whatever it needs.
2. Add it to the build at B under a fresh name.
3. Give an agent the goal `old_X = new_X` (or `old_X <-> new_X` for
   propositions).
4. Run comparator on the agent's proof.

Outcomes:

- **Proven.** The constant becomes **equiv-proven**. The reviewer sees this
  label and approves the new hash with one click. The agent informs; the human
  decides.
- **Not proven.** The reviewer reads new X.

Limits. For structures and type classes, "equal" is often the wrong notion; an
isomorphism is needed and agents will often fail. Those cases go to a human,
which is the right outcome. Most mathlib changes to definitions are renames
and field reorders, which `equiv` proves mechanically.

The same machinery serves authoring: if a new definition is provably equal to
an already-signed one, reuse the signed one and skip review.

## Rules for "still valid"

Write them down, as Gerrit's `copyCondition` and nuclear change screening
(10 CFR 50.59) do. Default rules:

1. Export hash of the signed constants' closure unchanged: **valid**.
2. Only theorem proof bodies changed (statements-only mode): **valid**.
3. Changed, and `equiv` proved equivalence: **valid after the reviewer approves
   the new hash**.
4. Anything else: **outdated** until re-approved.

Log every screening decision, so a wrong "still valid" can be traced.

## Concurrent changes and blame

Blame follows records. Each record says exactly what one person approved at
one hash. Nothing is retroactive.

**Alice signed B. Bob then changed A, which B imports.** B's closure hash
changes. Alice's record is still true for the old hash. The new B is unsigned
until someone approves it. Whoever approves the new hash owns it. If Alice
re-approves trusting Bob's signoff on A, that is her call and her record.

**A and B changed independently, both fine alone. Later, module C uses both and
is wrong.** C's signer owns C. C's record stores the hashes of A and B it was
approved against. C's statement must mean what C claims, with A and B as they
are. That is the ordinary boundary check.

**A and B are incompatible, so no C can use both.** C's author either writes an
adapter (a definition plus proof relating A's and B's conventions; new trusted
content, signed by C's signer) or proposes a change to A or B upstream, which
goes through their normal signoff.

**Who is blamed for the incompatibility itself?** By default nobody: both A and
B mean what they say. If you want an owner, adopt the rule below.

## Policy: the later signer owns compatibility

Whoever signs second had the chance to see what was already signed. Rule: a
signer is responsible for compatibility of their declarations with the
library's shared conventions file as it stood at signing time.

This is only fair if conventions live in one shared, signed file so the later
signer can check mechanically. Without that file, the rule asks them to read
the whole library, which is not reasonable.

## Revert and withdraw

- **Revert a definition.** Plain `git revert` of the source. The old export
  hash comes back, and the old signoff already covers it. Zero re-review.
- **Withdraw a signoff.** New record with `action = "withdraw"` pointing at
  the old record. Every constant whose closure includes that hash shows as
  unsigned. `status` computes this from the dependency chain.
