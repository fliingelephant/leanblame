# 9. Prior art

What exists, what each one has, and what it lacks for our purpose. Read on
2026-10-23 unless marked otherwise.

## Lean ecosystem

| Project | Has | Lacks |
|---------|-----|-------|
| **comparator** / `lake comparator` (Lean FRO) | Trusted/untrusted split, closure comparison, axiom check, kernel + external replay, compare-from-export | Any notion of a person |
| **comparator-live** | Web UI for comparator; "trusted challenges" identified by `sha256(text)`; users can locally trust more | Signer identity; hashes text, not export |
| **lean-eval** | Trusted statements tagged `@[eval_problem]`; one TOML manifest per problem with `submitter`, `status`, `statement_revision`; append-only revision history with a sha256 digest of the trusted statement | It is a benchmark; the "signer" is the submitter, not an independent reviewer |
| **lean-eval-submissions** | Append-only results per GitHub login, bound to exact commit, GitHub App verifies commit access | GitHub-only identity |
| **verso-blueprint** (Lean FRO) | Three layers: provenance, informal text, formal declarations; `@[blueprint]` attribute; dependency graph; progress tracking; public `blueprint-manifest.json` with labels, statuses, ownership; custom clients documented | Signoff, hash binding. We use it as the page's base. |
| **LeanArchitect** (Hanwen Zhu) | `@[blueprint]` attribute generating blueprint nodes from Lean declarations, for the Python leanblueprint; used by PNT+ and infinity-cosmos | Review, hashes. Precedent for `@[trusted]` only. |
| **leaff** (alexjbest) | Diff of two Lean environments: added, removed, type-changed declarations | One declaration at a time; no closure; superseded for us by comparator-from-export |
| **Mathlib review** | Reviewer + maintainer merge is an implicit attestation | Record is only GitHub history; no stated criteria; not portable |
| **formal-conjectures** (Google DeepMind) | Registry of formal statements of open conjectures, PR review, version bump when a misformalization is fixed | Named signer per statement, hash binding |
| **hex** libraries (Lean FRO) | Pattern: mathlib-free executable definitions in one package, mathlib correspondence proofs in a separate `-theory` package | Not about review; but the slim-definitions pattern reduces how often signoffs are invalidated |
| **Reservoir**, `lake-manifest.json` | Package index; exact commit pinning for every dependency | — |

## Other proof assistants

- **Isabelle Archive of Formal Proofs.** Organized like a journal. Submissions
  are refereed by anonymous referees chosen by ten named editors. Technical
  rules: no `sorry`, no `smt_oracle`, must build. Each entry has a named
  maintainer: "If accepted, you must agree to maintain your archive entry or
  nominate someone else." Entries are kept building against each Isabelle
  release; old versions stay available. So: public maintainer for
  buildability, anonymous reviewer for content. The opposite of LeanBlame on
  the review side.
- **Formal Abstracts** (Thomas Hales, ~2018). A registry of formal statements
  of theorems from papers. Stalled. From memory, not verified.

## Other fields (agent survey, 2026-10-23)

| System | Unit of signoff | Version / change handling | Blame |
|--------|-----------------|---------------------------|-------|
| **cargo-vet** (Mozilla) | One crate version, or a delta `a -> b`, per named criterion | Trusted iff full and delta audits form a path from an empty root; `violation` overrides | Reputational; audits imported from other orgs by URL and locked |
| **Gerrit** labels, **Linux kernel** trailers | Patch-set vote; `Reviewed-by` / `Acked-by` | `copyCondition` keeps votes only across listed change kinds; others become "outdated" | `Reviewed-by` disclaims warranty; `Fixes:` names the bad commit |
| **OWNERS** files (Google, Chromium) | Directory change; new dependency | Owners must keep deps current | Two named owners per dependency |
| **Sigstore**, **Go sumdb**, **Certificate Transparency** | Signature or hash over a digest | Append-only Merkle log | Monitors; strength equals the identity provider |
| **Professional Engineer seal** | One drawing sheet | Reviser seals revised sheets and explains the revision; earlier seals stay | Personal license, lawsuits |
| **FAA DER**, **NRC 10 CFR 50.59** | Compliance finding; design change | Change-impact analysis scopes re-verification; regulator reviews only changes meeting listed criteria | Designation is revocable |
| **PCAOB Form AP**, **SOX 302** | Audit report | Refiling | Partner ID never reused; non-delegable certification |
| **IETF** | RFC | RFCs never change; `Updates` / `Obsoletes` links; errata cannot change what was agreed | Reputational |
| **Crossmark**, **Zenodo**, **Registered Reports** | Article or dataset version; protocol | Typed update links (retraction, correction, new version); one DOI per version; protocol accepted before results exist | Retraction records are public |

Most transferable, in order:

1. cargo-vet's full-plus-delta audit graph and import-by-URL trust policy.
2. Gerrit / 50.59: written rules for when a signoff survives, log every screening.
3. PE seal: re-sign only what changed, explain the change, old seals stay.
4. Kernel `Reviewed-by`: a bounded written meaning for the signature.
5. IETF / Crossmark: never delete, typed corrections pointing at the old entry.
6. PCAOB partner ID: person-within-institution identifier, never reused.

## What LeanBlame adds

A named human bound to a kernel-level export hash, tracked across upstream
versions, with machine-assisted but human-decided carry-over, usable by
reviewers without GitHub accounts. No existing system has that combination.
