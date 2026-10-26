# 2. Concepts

Eight terms. Everything else is built from these. The trust model itself is
[03-trust-model.md](03-trust-model.md).

## Trusted boundary

The declarations a human must read for a result to mean anything:
definitions, structures, axioms, theorem statements, instances, conventions
written as declarations, plus the imports that fix their meaning. Notation is
surface syntax and is not on the boundary.

## Boundary list

A plain file naming the declarations on the trusted boundary, each with its
informal text. `export` makes it from the `@[trusted "id"]` attribute, with the
docstring as text, or from a verso-blueprint, with the blueprint's statement as
text. Everything on the list is "tagged." A constructor or projection of a
tagged structure is on it too and names the structure as its parent.

## Id

A random UUID in the source, `@[trusted "id"]`, written by `leanblame id`. It
stays when the declaration is renamed or edited, so records name declarations
by it and a sign-off follows a rename. Cite a declaration by its id:
`id@record`, the record fixing the commit. It is never hashed: writing an id
changes no claim. A member of a tagged structure has the structure's id and its
name: `3f2b…/x`. From a blueprint, a label is the id of the first declaration it
names; the others get the label and their names. A tag without an id, or two
declarations with one id, stop `export`.

## Export, checker, comparator

Lean's toolchain ships `leanexport`, which writes every constant of an
environment (types, values, universe levels) to one text file, and
`leanchecker`, which replays such a file through the Lean kernel. LeanBlame
hashes from the export and gates releases and `equiv` proofs with the checker.

`lake comparator` (Lean FRO, in core since v4.35.0) builds on the same two
tools: it compares an untrusted solution against a trusted statement file,
walking the dependency closure of each target theorem. LeanBlame copies its
closure walk and changes it (cut at tagged declarations, skip proofs, collect
every mismatch). Comparator itself is not run: what it cannot check, the Lean
reference manual says explicitly, is that the trusted file means what you
intended, and that is the one thing LeanBlame records.

## Claim hash

From the export and the boundary list, LeanBlame computes one **claim hash**
per tagged declaration. It covers the declaration's own type, body and
informal text; the name, type and informal text of every tagged declaration it
uses; and everything untagged underneath. Theorem proofs are skipped. It is a
hash of **meaning**, not of source text.

## Signoff

A record saying: this person, on this date, approves these declarations at
these claim hashes. It does not say the proof is correct (kernel's job) or that
the result matters (nobody's job here).

## Trust through people (`git blame`)

If your module uses a tagged declaration someone already signed, you read its
name, type and informal text, not its body. You trust the body through its
signer. Their name is on it. Each body is read once, by a named person.
Everyone else reuses that reading.

## Append-only

Records are never edited or deleted. A mistake is corrected by adding a new
record that points at the old one.
