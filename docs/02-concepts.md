# 2. Concepts

Six terms. Everything else is built from these.

## Trusted boundary

The declarations a human must read for a result to mean anything:
definitions, structures, axioms, theorem statements, instances, notation and
conventions, plus the imports and checker configuration that fix their meaning.

In comparator terms: the Challenge module plus `config.json`.

## Comparator

`lake comparator` takes a trusted **Challenge** module (statements, usually
ending in `sorry`) and an untrusted **Solution** module. It:

1. builds both inside a sandbox (landrun or bubblewrap);
2. runs `lean4export` on each, producing a kernel-level dump of every constant;
3. checks that each target theorem's statement is identical in Challenge and
   Solution;
4. walks the full dependency closure of those statements and requires every
   constant to match, type and value (`Comparator/Compare.lean`,
   `Compare.loop`);
5. checks the proofs use only permitted axioms;
6. replays the proofs in the Lean kernel and, optionally, external checkers
   such as nanoda.

It accepts `--challenge-from-export` and `--solution-from-export`, so two
pre-exported environments can be compared without rebuilding
(`tests/lake/tests/comparator-from-export` in leanprover/lean4).

For definition "holes" (declarations the solver must fill), comparator checks
name, type, universe levels and safety, **not** the value. So signed
definitions must never be listed as holes. List the statements that use them;
the definitions then enter the closure and are compared fully.

What comparator cannot check: that the Challenge means what you intended. The
Lean reference manual says this explicitly.

## Export hash

`lean4export` writes the kernel's view of the environment: every constant with
its type and value. A hash over the export is a hash of **meaning**, not of
source text. Source text can stay identical while meaning changes, for example
when an imported definition moves. The export catches that.

## Signoff

A record saying: this person, on this date, read this set of constants at this
export hash and approves. That is all it says. It does not say the proof is
correct (kernel's job) or that the result matters (nobody's job here).

## Trust through people (`git blame`)

If your module imports a definition someone already signed, you do not re-read
it. You trust it through them. Their name is on it. Each constant is read
carefully once, by a named person, and reused many times. This is how review
scales.

## Append-only

Records are never edited or deleted. A mistake is corrected by adding a new
record that points at the old one. History stays.
