# LeanBlame

Infrastructure for reviewer-signed formalization libraries in Lean 4.

Machines check proofs. Named humans sign off on the trusted boundary:
definitions, theorem statements, conventions, axioms. Every signoff is a
permanent record bound to a kernel-level hash. Trust flows through people: you
sign your own declaration fully, only the spec of signed declarations you use,
and everything of unsigned ones.

LeanBlame is field-independent. The first library built on it is OpenPhysics.

Documentation: [docs/README.md](docs/README.md)

Status: the CLI (eight commands) is implemented and tested; the web part is not started. 2026-10-24.
