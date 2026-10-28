# 10. Prior art

Read on 2026-10-23 unless marked otherwise.

## Lean ecosystem

| Project | Has | Lacks for us |
|---------|-----|--------------|
| **comparator** / `lake comparator` (Lean FRO) | Trusted/untrusted split, closure comparison, axiom check, kernel and external replay, compare from exports | Any notion of a person; stops at first mismatch; compares proofs |
| **comparator-live** | Web UI for comparator; trusted challenges identified by `sha256(text.trimRight() + "\n")` | Signer identity; hashes text, not meaning |
| **lean-eval** | `@[eval_problem]`; one TOML per problem with `submitter`, `status`, `statement_revision`; append-only revision history with a sha256 digest | It is a benchmark; the "signer" is the submitter |
| **lean-eval-submissions** | Append-only results per GitHub login, exact commit binding | GitHub-only identity |
| **verso-blueprint** (Lean FRO) | Prose, Lean declarations and dependency graph in one document; `@[blueprint]`; `blueprint-manifest.json` with labels, statuses, ownership; custom clients documented (the repo notes the manifest is not yet a stable interface) | Signoff, hash binding. A natural consumer of `status --json`. |
| **LeanArchitect** (Hanwen Zhu) | `@[blueprint]` generating blueprint nodes from Lean declarations, for the Python leanblueprint; used by PNT+ and infinity-cosmos | Review, hashes. Precedent for `@[trusted]`. |
| **leaff** (alexjbest) | Diff of two Lean environments: all added, removed, renamed, changed declarations | Closure walk, hash binding |
| **doc-gen4** | Per-declaration HTML with docstrings for any Lake package | Nothing |
| **Mathlib review** | Reviewer plus maintainer merge is an implicit attestation | Record is only GitHub history |
| **formal-conjectures** (Google DeepMind) | Registry of formal statements of open conjectures; version bump when a misformalization is fixed | Named signer per statement, hash binding |
| **hex** libraries (Lean FRO) | Mathlib-free executable definitions plus separate `-theory` correspondence packages | Not review; the slim-dependency pattern reduces cascades |

## Other proof assistants

- **Isabelle Archive of Formal Proofs.** Organized like a journal. Anonymous
  referees chosen by named editors. Rules: no `sorry`, `back`, `sledgehammer`
  or `smt_oracle`; must build. Named maintainer per entry: "If accepted, you
  must agree to maintain your archive entry or nominate someone else." Kept
  building against each Isabelle release; old versions stay available. Public
  maintainer for buildability, anonymous reviewer for content: the opposite of
  LeanBlame on the review side.
- **Formal Abstracts** (Thomas Hales, ~2018). Registry of formal statements
  from papers. Stalled. From memory, not verified.

## Other fields

| System | Unit of signoff | Change handling | Blame |
|--------|-----------------|-----------------|-------|
| **cargo-vet** | One crate version, or a delta `a -> b`, per criterion | Trusted if a chain of audits reaches this version | Reputational; audits imported from other orgs by URL and locked; exclusions |
| **Gerrit**, **Linux kernel** | Patch vote; `Reviewed-by` | Votes survive only listed change kinds; else "outdated" | `Reviewed-by` disclaims warranty |
| **OWNERS** files | Directory change | Owners keep deps current | Two named owners per dependency |
| **Sigstore**, **Go sumdb**, **Certificate Transparency** | Signature over a digest | Append-only Merkle log | Monitors |
| **Professional Engineer seal** | One drawing sheet | Reviser seals changed sheets and explains; old seals stay | Personal license |
| **FAA DER**, **NRC 10 CFR 50.59** | Compliance finding; design change | Change-impact analysis scopes re-verification | Designation revocable |
| **PCAOB Form AP**, **SOX 302** | Audit report | Refiling | Partner id never reused |
| **IETF** | RFC | Never changes; `Updates`/`Obsoletes` | Reputational |
| **Crossmark**, **Zenodo**, **Registered Reports** | Article version; protocol | Typed update links; one DOI per version; protocol accepted before results | Public retractions |

What LeanBlame adds: a named human bound to a kernel-level claim hash. The
hash cuts at signed dependencies. It is tracked across upstream versions.
Agents help; the human decides. Reviewers do not need GitHub.
