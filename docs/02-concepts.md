# 2. Concepts

Seven terms. Everything else is built from these. The trust model itself is
[03-trust-model.md](03-trust-model.md).

## Trusted boundary

The declarations a human must read for a result to mean anything:
definitions, structures, axioms, theorem statements, instances, conventions
written as declarations, plus the imports that fix their meaning. Notation is
surface syntax and is not on the boundary.

## Boundary list

A plain file naming the declarations on the trusted boundary, each with its
informal text (usually the docstring). The `@[trusted]` attribute generates it.
A blueprint adapter can generate it from a blueprint's node-to-declaration
mapping. Everything on the list is "tagged."

## Comparator

`lake comparator` (Lean FRO, in core since v4.35.0) takes a trusted
**Challenge** module (statements, usually ending in `sorry`) and an untrusted
**Solution** module. It:

1. builds both inside a Linux sandbox;
2. exports both with the toolchain's `leanexport`;
3. checks each target theorem's statement is identical in Challenge and
   Solution;
4. walks the full dependency closure of those statements and requires every
   constant to match, type and value, stopping at the first mismatch;
5. checks the proofs use only the permitted axioms;
6. replays the proofs in the Lean kernel and, optionally, external checkers.

Config file `comparator.json`: `theorem_names`, `definition_names`,
`permitted_axioms`. Definition "holes" are compared by type only. Core also
accepts `--challenge-from-export` and `--solution-from-export`.

What comparator cannot check: that the Challenge means what you intended. The
Lean reference manual says this explicitly.

LeanBlame uses comparator for one job: checking the `old = new` proofs
produced by `equiv`. The library's own proofs are replayed by `leanchecker`.
Hashing is LeanBlame's own walk.

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
