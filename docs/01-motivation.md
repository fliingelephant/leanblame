# 1. Motivation

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
- **Not AI review.** Agents can run endless checks on a statement. None of
  them replaces a human reading the boundary. LeanBlame records the human
  reading. Agent output may be shown next to the statement as information,
  never as a decision.
