# LeanBlame

Infrastructure for curated, reviewer-signed formalization libraries in Lean 4.

Machines check proofs. Named humans sign off on the trusted boundary:
definitions, theorem statements, conventions, axioms, imports, and checker
configuration. Every signoff is a permanent record bound to a kernel-level
hash, so it survives or fails library upgrades in a checkable way.

LeanBlame is field-independent. The first library built on it is OpenPhysics.

Documentation: [docs/README.md](docs/README.md)

Status: design stage, 2026-10-23.
