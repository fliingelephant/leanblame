# Trust model

The Lean kernel checks proofs. LeanBlame records which human approved which
declarations, at which kernel-level hash, and when. Trust flows through
people like `git blame`: you sign your own declaration fully, you sign only
the name, type and informal text of signed declarations you use, and you sign
everything of unsigned ones. When upstream changes, `status` says what moved
and why. If only unsigned code underneath changed, `equiv` asks the kernel
whether the meaning is the same, and a human approves the new hash with one
click. Records are never deleted. Two parts: a Lean CLI and signoff records
in git. A service, such as OpenVouch, shows them and writes records after a
login.

## The shift

AI agents are now strong at well-defined, verifiable tasks. In Lean,
"verifiable" means the kernel accepts the proof. Producing proofs and checking
proofs are both becoming cheap.

What does not become cheap: deciding whether a formal statement means what the
human intended. The kernel cannot check that. A proof of the wrong statement is
worthless, and the kernel accepts it happily.

## Where humans are needed

Exactly at the boundary between informal intent and formal text:

- **Definitions.** Does `IsingHamiltonian` have the right sign and coupling?
- **Theorem statements.** Is this really the claim from the paper?
- **Conventions.** Natural units? Fourier normalization? Boundary conditions?
- **Axioms.** Only the standard three? No `sorry`?
- **Imports.** Which library versions give these symbols their meaning?
- **Checker configuration.** Which declarations are the targets?

Nothing else. Humans never read proof bodies. That is the kernel's job.

## Responsibility

An agent cannot be blamed. Only people and institutions can. So every
trusted claim needs a named human, and an institution behind the human.

This is the same reason a licensed engineer stamps a drawing, an audit partner
signs an opinion, and a Linux kernel patch carries `Reviewed-by:`.

## Why now

Lean's `comparator` (Lean FRO, 2025; in core as `lake comparator` since
v4.35.0) already separates the trusted statement file from the untrusted proof
file. It names the exact object a human must read. LeanBlame adds the human
record on top: who read it, when, at which hash.

## What LeanBlame is not

- **Not a prover.** Agents and humans prove. The kernel checks.
- **Not a judge of value.** Whether a result is interesting is out of scope.

## Words

### Trusted boundary

The declarations a human must read for a result to mean anything:
definitions, structures, axioms, theorem statements, instances, conventions
written as declarations, plus the imports that fix their meaning. Notation is
surface syntax and is not on the boundary.

### Boundary list

A plain file naming the declarations on the trusted boundary, each with its
informal text. `export` makes it from the `@[trusted "id"]` attribute, with the
docstring as text, or from a verso-blueprint, with the blueprint's statement as
text. Everything on the list is "tagged." A constructor or projection of a
tagged structure is on it too and names the structure as its parent.

### Id

A random UUID in the source, written by `leanblame id` into the tag: `@[trusted
"id"]` on the declaration, or `attribute [trusted "id"] Name` after the fact, in
any module, also for a declaration of a library one does not own. It
stays when the declaration is renamed or edited, so records name declarations
by it and a sign-off follows a rename. Cite a declaration by its id:
`id@record`, the record fixing the commit. It is never hashed: writing an id
changes no claim. A member of a tagged structure has the structure's id and its
name: `3f2b…/x`. From a blueprint, a label is the id of the first declaration it
names; the others get the label and their names. A tag without an id, or two
declarations with one id, stop `export`.

### Claim hash

From the export and the boundary list, LeanBlame computes one **claim hash**
per tagged declaration. It covers the declaration's own type, body and
informal text; the name, type and informal text of every tagged declaration it
uses; and everything untagged underneath. Theorem proofs are skipped. It is a
hash of **meaning**, not of source text.

### Signoff

A record saying: this person, on this date, approves these declarations at
these claim hashes. It does not say the proof is correct (kernel's job) or that
the result matters (nobody's job here).

### Trust through people (`git blame`)

If your module uses a tagged declaration someone already signed, you read its
name, type and informal text, not its body. You trust the body through its
signer. Their name is on it. Each body is read once, by a named person.
Everyone else reuses that reading.

### Append-only

Records are never edited or deleted. A mistake is corrected by adding a new
record that points at the old one.

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

## Who may do what

| Over | Who | Can |
|------|-----|-----|
| **a record** | its signer, only | approve, withdraw, approve again |
| **a library** | its maintainers, via git | tag declarations, choose which records directories count, exclude an approve record by hash, cut releases, edit the conventions module |
| **identity** | the login provider; the institution hosting the records | say who a signer is; host and back their records |

A record is one person's statement. Nobody edits it, not even a maintainer.
A maintainer who thinks a record is wrong **excludes** it in `leanblame.toml`
and opens an issue. That is a dispute. Git blame on the config shows which
maintainer excluded what.

Who wrote the declaration is a separate trail: the git commit author. Agents
may write declarations. Only humans sign.

## Records

The declaration, each with its own claim hash. A record names each declaration
by its id, with its name and claim hash at that export, so an approval follows
the declaration through a rename. A record lists expanded constants explicitly:
tagging a structure produces entries for the type, its constructors and its
projections, whose ids are the structure's id and their names (`3f2b…/x`). One
record may cover one declaration or a whole module. Default: one record per
module.

Exact fields, with examples: [docs/schemas.md](docs/schemas.md) §2.

### Withdraw rules

- `refers_to` must point at an approve record, never at a withdraw.
- A withdraw counts only if its `signer` equals the approve record's signer.
  `validate` rejects others.
- A withdraw may list `constants`, ids of declarations in that record, at least
  one; left out, it withdraws every declaration in the record.
- To undo a withdrawal, approve again. There is no withdraw of a withdraw.

### Several records for one declaration

An approve record is **live** for a declaration if no counting withdraw (rules
above) covers that declaration in it, `exclude` does not list it, and its signer
is allowed by `leanblame.toml`. This is the one definition; validity is built on
it (Validity, below). Every record stays visible
in `blame` and in the `history` of `status --json`, each approval with its
standing: `current` (live, at the current claim), `superseded` (live, an older
claim), `withdrawn`, `excluded` or `not-allowed`.

A withdraw that breaks the rules above, an `exclude` entry that names no approve
record, a record in two records directories, and a file in a records directory
that is not a record are problems. `validate` lists them; the other commands
stop.

### Storage

- One file per record in a records directory (`records/` by default).
  Filename = sha256 of the file bytes as they were written.
- Terminal `sign` writes `local:` records. Ids backed by a login come from a
  service that logs the signer in and writes the
  record (OpenVouch; not built yet).
- `validate` gates every record, wherever the adopter runs it: schema, authority rules, and no
  modification or deletion of an existing record.
- Records are trusted because a service wrote them after a login and `validate`
  rejects edits to existing records before they are pushed. The party you trust
  is whoever holds that service's push credential, normally the hosting
  institution. Name it in the library's README.
- Cryptographic signatures: not now. If forgery becomes a concern, Sigstore keyless
  signing: the reviewer signs with a university email in a browser; the signature
  is logged in Rekor. Public Sigstore accepts Google and Microsoft email logins;
  whether university Microsoft accounts work is unconfirmed.
- Linking one person's accounts across login providers: later, if needed.

A library lists its records directories in `leanblame.toml` (local
directories; remote repositories later) and excludes individual approve records
by hash. Every key of `leanblame.toml` is required; `init` writes them all. A
withdrawal cannot be excluded: a signer's word about their own record stands,
and nobody can be made to vouch for what they took back.

One signer suffices with `required_signers = 1`, which `init` writes; several records for
the same hash accumulate. `action` is the only type field.

## What a signoff means: the memo

Shown above the approve button:

> I have read these declarations: their text and their informal description.
> I believe they mean what that description says.
> For tagged declarations they use, I have read the name, type and description, and I rely on their named signers for the rest.
> Everything untagged underneath is mine.
> I have not checked proofs. The kernel does that.
> I own the meaning of these declarations, not their importance.
> If one is later shown not to mean what it says, this record stays and a withdrawal is added next to it.
> I have checked my declarations against the shared conventions module as it stands today.

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

"Live" is defined under Records, above.

A release requires every tagged declaration `valid`, which implies no blocks.

Validity is relative to a trust policy: which records directories the library
counts, which records it excludes, who may sign, how many signers it needs.
Hashes are not. Hashes depend only on the code.

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

## `equiv`

A signoff was made at mathlib commit A. The library moves to commit B. Does the
signoff still hold?

Sources from two mathlib versions cannot be built together. Kernel terms can.
That distinction drives everything below.

Runs only for declarations whose sole cause is `untagged`. Any other cause
needs a human to read.

1. Fetch the old export and boundary list named in the record.
2. Compare old and new closures by hash. Constants with equal hash are
   **shared**: they are the same kernel term. Changed constants and everything
   between them and X are **duplicated** under `Old.`, with references renamed.
   Constants used only in proofs are not hashed; they are shared when the new
   export states them the same way.
3. State the goal by kind, as `∀ P, P old → P new` (whatever holds for the old
   holds for the new), proved by `fun P h => h`; it names no constant, so every
   export can state it. Def: `Old.X` and `X`, stated at X's type, so the kernel
   accepts it only if the types are definitionally equal too. Theorem:
   `type(Old.X)` and `type(X)`. A structure or another inductive: no goal; a
   human reads.
4. The kernel decides, mechanically: no build, no tactics. At the frontier of
   change, each changed definition C gets its goal, and the kernel is asked
   whether `Old.C` and `C` are definitionally equal: one kernel call per changed
   definition. Everything above follows by congruence; X's own goal is one more
   call. The accepted proofs go to the object store as an export, which
   `leanchecker` replays. Not definitionally equal: a human reads, shown the
   old and new definitions.
5. `status` shows the proof as X's `evidence`. The reviewer approves the new
   hash with one click; X's entry in the record carries the proof hash as
   `evidence`.

`challenge --check` runs steps 2 to 4 too, with the library as the old version
and the challenge, built against it, as the new one; it stores no proof.

Mechanism: `equiv` reads the old and the new export. It adds the duplicated
constants to the new export's environment, the kernel checking each, then the
goals with their proofs (`fun P h => h`). The accepted theorems and what they
use are written as an export, which `leanchecker --from-export` replays, as
`release` replays the library: the evidence is a file anyone can check again.
Nothing is built or elaborated and no `.olean` is written.

Never copy old *source* into the new build. It would elaborate against the new
mathlib, make `old = new` true by `rfl`, and prove nothing.

Renames succeed in one line. Changed structures go to a human.

The same machinery serves authoring: a new declaration provably equal to a
signed one can be replaced by it, skipping review.

## Blame

- **Alice** owns: her declaration's text and informal text, her reading of her
  dependencies' specs, and every untagged declaration under hers.
- **Bob** owns: his body matching his spec. When he re-signs after a body
  change, the page shows him everything that depends on `Hamiltonian`.
- **A spec change** is owned by Bob (new spec) and by every user who
  re-signs against it.

No meaning change passes without a named person re-signing something. The one
thing hashing cannot catch is an original signoff that was wrong. That is what
withdrawals are for.

Blame follows records. Each record says what one person approved at one hash.
Nothing is retroactive.

**A and B changed independently, both fine alone. Later, module C uses both
and is wrong.** C's signer owns C.

**A and B are incompatible, so no C can use both.** C's author writes an
adapter (new tagged content, signed by C's signer) or proposes a change
upstream.

### The later signer owns compatibility

Whoever signs second had the chance to see what was already signed. A signer
is responsible for compatibility of their declarations with the library's
conventions module as it stood at signing time.

### The conventions module

A normal tagged module of the library. Conventions are **declarations**: a def `hbar : ℝ := 1`, a sign choice inside a body, a
docstring stating boundary conditions. Other declarations reference them, so a
convention's spec is part of their claim hash. Changing a convention's text
re-signs everyone who uses it, which is correct.

Notation and macros are not conventions. They never reach the kernel, so they
cannot be hashed or signed. A statement prints with them, as the library's
documentation shows it; each constant in it is named, so a reader can follow it
to what the kernel sees.

## Revert and withdraw

- **Revert a declaration.** `git revert` the source. The old claim hash comes
  back if nothing else under it moved, and the old record covers it.
- **Withdraw a signoff.** New record with `action = "withdraw"`, by the same
  signer. The declaration drops to `outdated` or `unsigned`; everything that
  depends on it is blocked by it.

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
definitions, and `quot` and `rec` have none to read. For scale: the statement-level
closure of one real-number inequality, proofs excluded, was about 3,400 constants;
with proofs, 13k–43k.

```
own(c)   = H("leanblame.own",   kind, role, name, uparams, type, body?, informal?)
spec(c)  = H("leanblame.spec",  kind, role, name, uparams, type, informal)
claim(c) = H("leanblame.claim", own(c), sorted over direct dependencies d of c:
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
group     = H("leanblame.group",  count, member owns, external entries)
member(c) = H("leanblame.member", group, name)
```

A record stores, for each declaration it covers, its id, its name and
`claim(c)`, plus the export hash, the boundary-list hash, the library commit,
toolchain and dependency commits.

## Rejected alternatives

- **Full-closure hash.** Alice's hash includes Bob's body. Bob fixes a typo
  in the body, twenty downstream signers re-click.
- **Names only for tagged dependencies.** Bob rewrites his docstring to mean
  something else. Alice is never told.
- **Trust people, no hashes.** Nobody is told anything changed.
- **Lean's kinds and safety as fixed lists in the hash.** The rules read the role
  instead, so they hold for any proof assistant.

## Known costs

- The informal text is the spec. Vague text is a vague claim. Tagged
  declarations without informal text are an error.
- A wording-only edit of that text cascades re-signs. The page makes that a
  one-click diff.
- Mathlib definition refactors cascade. `equiv` catches the definitional
  ones. Fewer upstream dependencies means fewer cascades.
