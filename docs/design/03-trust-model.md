# 3. Trust model

Every other file depends on this one.

## The rule, three lines

- You sign your own declaration fully: type, body, informal text.
- For **tagged** declarations you use, you sign only their name, kind, type, informal text. Not the body.
- For **untagged** declarations you use, you sign all of it, recursively, until you reach a tagged one.

"Tagged" means: on the boundary list. `@[trusted "id"]` puts a declaration
there; so can a blueprint. "Informal text" is the docstring, or the blueprint's
statement text. Theorem proofs are never part of any hash.

## Why these three lines

A signoff is a conditional claim: "X means what its informal text says, given
that the declarations X uses mean what *their* informal text says."

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
users automatically. `export` collects tags from imported libraries too.
"Untagged" is not a fixed list of libraries. Mathlib is untagged today because
it publishes none.

## What is tagged when you tag a structure

Tagging an `inductive` or `structure` tags the type, its constructors and its
projections. Everything else Lean generates for it (`rec`, `casesOn`,
`noConfusion`, `injEq`, `sizeOf`, …) is derived from those and stays untagged.
Compiler auxiliaries (`match_n`, `proof_n`, `_unary`, …) are never tagged and
never trigger the warning below.

`status` warns when a tagged declaration uses an untagged declaration from the
same library. Usually that declaration should be tagged too, so it gets its own
signer instead of being re-owned by everyone who uses it.

`unsafe` declarations cannot be tagged; they never reach the kernel. For
`opaque` and `partial` the body is hidden from the kernel, so the hash covers
kind, type and informal text only.

## What happens on change

| Change | Who acts |
|--------|----------|
| Bob edits the body of `Hamiltonian`, spec unchanged | Bob re-signs. Alice's hash did not move. Her theorem is blocked until Bob signs, then valid. No click from Alice. |
| Bob edits its type, kind or informal text | Bob re-signs. Alice's hash moved. She re-signs too, shown the diff. |
| Mathlib changes a definition under Alice | Alice's hash moved. `equiv` rebuilds the old meaning and tries to prove it equal to the new one. Alice clicks, or reads. |
| Mathlib rewrites a proof | Nothing. Proofs are not hashed. |
| Someone removes the tag from a declaration Alice uses | Alice's hash moved: she now owns a body she never read. She reads it. `equiv` is not offered. |
| Bob withdraws his signoff | Alice's theorem is blocked until `Hamiltonian` is approved again. Alice's record still stands. |

## Why a hash moved

`status` charges every hash change to one or more causes, by comparing the
parts of the hash:

| Cause | What moved | Machine help |
|-------|------------|--------------|
| `own-text` | your informal text | none, read it |
| `own-body` | your type or body | none, read it |
| `dep-spec` | name, kind, type or text of a tagged dependency | the diff is shown |
| `cut-moved` | a dependency gained or lost its tag | none, read it |
| `untagged` | something untagged underneath changed | `equiv` may prove meaning unchanged |

`equiv` runs only when `untagged` is the sole cause; a successful proof shows
as X's `evidence`. `diff` makes the same comparison between two points the
caller picks, and shows the old and the new text.

## Validity

Per tagged declaration X, `status` computes:

- **state**: `valid` if at least `required_signers` distinct signers have live
  approve records carrying X's current hash (`init` sets one); `outdated` if
  live approve records list X but not enough of them carry the current hash;
  `unsigned` if none lists X. Records name X by its id, so a renamed X is
  `outdated` (the name is hashed), not `unsigned`.
- **blocked_by**: tagged dependencies whose state is not `valid`, recursively.
- **evidence**: the `equiv` proof that X's current hash means what its last
  live approval meant, if there is one.

"Live" is defined in [05-records.md](05-records.md), with who may do what.

A release requires every tagged declaration `valid`, which implies no blocks.

Validity is relative to a trust policy: which records repositories the library
accepts, which records it excludes, who may sign, how many signers it needs.
Hashes are not. Hashes depend only on the code.

## The hash, precisely

Rule: hash everything that changes meaning, nothing else.

Every declaration has a **role**, which says what its body is to a signer:

| Role | The body | Lean kinds |
|------|----------|------------|
| `assumed` | none; the statement is taken as true | `axiom` |
| `defined` | is the meaning; the signer reads it | `def`, `opaque`, `inductive`, `ctor`, `quot`, `rec` |
| `proved` | is a proof; the kernel checks it, nobody reads it | `theorem` |

The **kind** the hash takes is the kernel's, as in the table. It is hashed as
text and never interpreted; the rules below read the role. A definition the
export marks partial would be labelled `partial def`; Lean 4.35 exports them as
`opaque`. The boundary list names each declaration in the documentation's words
instead (`structure`, `field`, `instance`, …); those words are not hashed, as
they add nothing the kernel's kind and the type do not already fix.

**In:** kind, role, name, ordered universe parameters, type, the body of a
`defined` declaration when the kernel sees it, informal text (tagged
declarations only; ASCII whitespace trimmed, line endings normalized, no
Unicode normalization). Type and body enter with every proof subterm erased.

**Out:** theorem proofs, proof subterms anywhere (in types as in bodies),
binder names, argument implicitness, kernel height hints, recursor rules.
None of these change meaning; all of them churn on toolchain bumps. Proofs
in particular: Lean treats all proofs of one proposition as equal (proof
irrelevance) and hides them when it displays a term, so a signer never read
them. The kernel does not see the body of `opaque` and `partial`
definitions, and `quot` and `rec` have none to read.

```
own(c)   = H("leanblame.own.2",   kind, role, name, uparams, type, body?, informal?)
spec(c)  = H("leanblame.spec.2",  kind, role, name, uparams, type, informal)
claim(c) = H("leanblame.claim.2", own(c), sorted over direct dependencies d of c:
               tagged(d)   -> ("spec", spec(d))
               untagged(d) -> ("full", claim(d)))
```

`H` is SHA-256 over the tag and the fields, each as `<byte length>:<bytes>`.
`name` is the printed name. `type` and `body` are hashes of the canonical
terms, proofs erased. `body?` and `informal?` are `+<len>:<bytes>` when
present (a hashed body; the informal text of a tagged declaration), else `-`.

Terms are printed canonically from the parsed export with de Bruijn indices;
constants by name, never by export index; universe parameters by position. A
repeated subterm is printed once and referred to afterwards, so printing is
linear in the size of the term as a graph (a term can be exponentially larger
as a tree). Dependencies of a `proved` declaration are those of its type only.

Cycles: an inductive type and its constructors reference each other, and
mutual definitions do too. Such a group is hashed as one unit; each member's
hash is the group hash plus its name. Owns are sorted by member name; the
external entries are those of `claim`, for dependencies outside the group.

```
group     = H("leanblame.group.2",  count, member owns, external entries)
member(c) = H("leanblame.member.2", group, name)
```

A record stores, for each declaration it covers, its id, its name and
`claim(c)`, plus the export hash, the boundary-list hash, the library commit,
toolchain and dependency commits.

## Blame

- **Alice** owns: her declaration's text and informal text, her reading of her
  dependencies' specs, and every untagged declaration under hers.
- **Bob** owns: his body matching his spec. When he re-signs after a body
  change, the page shows him everything that depends on `Hamiltonian`.
- **A spec change** is owned by Bob (new spec) and by every user who
  re-signs against it.
- **Who wrote the code** is a separate trail: the git author. An agent may
  write anything. Only a human signs.

No meaning change passes without a named person re-signing something. The one
thing hashing cannot catch is an original signoff that was wrong. That is what
withdrawals are for.

## Rejected alternatives

- **Full-closure hash.** Alice's hash includes Bob's body. Bob fixes a typo
  in the body, twenty downstream signers re-click.
- **Names only for tagged dependencies.** Bob rewrites his docstring to mean
  something else. Alice is never told.
- **Trust people, no hashes.** Nobody is told anything changed.

## Known costs

- The informal text is the spec. Vague text is a vague claim. Tagged
  declarations without informal text are an error.
- A wording-only edit of that text cascades re-signs. The page makes that a
  one-click diff.
- Mathlib definition refactors cascade. `equiv` catches the definitional
  ones. Fewer upstream dependencies means fewer cascades.
