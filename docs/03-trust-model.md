# 3. Trust model

This is the heart of LeanBlame. Everything else serves it.

## The rule, three lines

- You sign your own declaration fully: type, body, informal text.
- For **tagged** declarations you use, you sign only their name, type, informal text. Not the body.
- For **untagged** declarations you use, you sign all of it, recursively, until you reach a tagged one.

"Tagged" means: on the boundary list. `@[trusted]` puts a declaration there;
so can a blueprint adapter. "Informal text" is the docstring, or the blueprint
node text the boundary list points at. Theorem proofs are never part of any
hash.

## Why these three lines

A signoff is a conditional claim: "X means what its docstring says, given
that the declarations X uses mean what *their* docstrings say."

To use Bob's `Hamiltonian`, Alice read its name, type and docstring. That is
the spec. She never opened the body. Bob owns the body. So Alice's hash
covers the spec and not the body.

Mathlib's `Finset.sum` has no signer in our system. Nobody else is
accountable for it, so Alice is. Her hash covers all of it.

A theorem's proof cannot change what anything means. The kernel checks
proofs. Hashes skip them.

## The cut is the tag, not the record

Tagged but not yet signed still cuts. Alice's theorem then shows
"blocked by Hamiltonian, unsigned." Her own signoff is unaffected.

Any library that publishes a boundary list becomes "signed stuff" for its
users automatically. "Untagged" is not a fixed list of libraries. Mathlib is
untagged today because it publishes none.

A `structure` expands to its generated constants: the type, `mk`, the
projections, `rec`, `noConfusion`. Tagging the structure tags them all. Their
spec is their types plus the structure's informal text.

`status` warns when a tagged declaration uses an untagged declaration from the
same library. Usually that declaration should be tagged too, so it gets its own
signer instead of being re-owned by everyone who uses it.

## What happens on change

| Change | Who acts |
|--------|----------|
| Bob edits the body of `Hamiltonian`, spec unchanged | Bob re-signs. Alice's hash did not move. Her theorem is blocked until Bob signs, then valid. No click from Alice. |
| Bob edits its type or docstring | Bob re-signs. Alice's hash moved. She re-signs too, shown the diff. |
| Mathlib changes a definition under Alice | Alice's hash moved. `equiv` rebuilds the old meaning from the old export and tries to prove it equal to the new one. Alice clicks, or reads. See [06-versioning.md](06-versioning.md). |
| Mathlib rewrites a proof | Nothing. Proofs are not hashed. |
| Bob withdraws his signoff | Alice's theorem is blocked until someone re-approves `Hamiltonian` at its current hash. Alice's record still stands. |

## Validity

Per tagged constant X, `status` computes:

- **own state**: `valid` if a live approve record carries X's current hash;
  `outdated` if live records exist but none match; `unsigned` if none exist.
  A record is live if no withdraw record points at it.
- **flags**: `equiv-proven` (an `old = new` proof exists for the outdated
  hash), `withdrawn` (a record existed and was withdrawn), `blocked-by [Y…]`
  (tagged dependencies whose own state is not `valid`, recursively).

A library release requires every tagged constant `valid`. That implies no
blocks.

Validity is relative to a trust policy: which records repositories you
accept. The hashes are not. Hashes depend only on the code.

## The hash, precisely

For a constant `c`, computed from the parsed export plus the boundary list:

```
own(c)   = H(kind, name, type, body-unless-theorem, informal-text)
spec(c)  = H(name, type, informal-text)
claim(c) = H(own(c), sorted over direct dependencies d of c:
               tagged(d)   -> ("spec", spec(d))
               untagged(d) -> ("full", claim(d)))
```

Constants are referenced by name, never by export index. Terms are printed
canonically from the parsed export. Dependencies are sorted by name. Renaming
a dependency changes the hash; `equiv` proves such cases in one line.

A record stores `claim(c)` for each constant it covers, plus the library
commit, toolchain and dependency commits for reproducibility.

## Blame

- **Alice** owns: her declaration's text and docstring, her reading of her
  dependencies' specs, and every untagged declaration under hers.
- **Bob** owns: his body matching his spec. When he re-signs after a body
  change, the page shows him everything that depends on `Hamiltonian`.
- **A spec change** is owned by Bob (new spec) and by every user who
  re-signs against it.

No meaning change passes without a named person re-signing something. The
one thing hashing cannot catch is an original signoff that was wrong. That is
what withdrawals and disputes are for.

## Rejected alternatives

- **Full-closure hash.** Alice's hash includes Bob's body. Bob fixes a typo
  in the body, twenty downstream signers re-click. Contradicts "trust the
  signer, don't re-read."
- **Names only for tagged dependencies.** Bob rewrites his docstring to mean
  something else. Alice is never told. Hole.
- **Trust people, no hashes.** Nobody is told anything changed.

## Known costs

- The informal text is the spec. Vague text is a vague claim. Tagged
  declarations must have some.
- A wording-only edit of that text cascades re-signs. The page makes that a
  one-click diff.
- Mathlib definition refactors cascade. `equiv` catches most. Fewer upstream
  dependencies means fewer cascades.
