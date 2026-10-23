# 11. Roadmap

## Exists, reuse as is

- `lean4export`.
- mathlib `lake exe cache get`; Lake artifact cache.
- OpenID Connect providers: OpenReview, ORCID, GitHub.

## Fork and pin

- `leanprover/comparator` (archived standalone). Patch: statements-only mode.
- `leanprover/comparator-live`. Patch: signer records on trusted challenges.
- `leanprover/verso-blueprint`. Patch: per-node signoff overlay.
- `leanprover/lean-eval`. Copy the `@[eval_problem]` attribute and config
  generator into `cli`.

## Build, in order

| # | Item | Size |
|---|------|------|
| 1 | Record schema and validator | small |
| 2 | `cli`: `@[trusted]`, `export`, `status` (incl. `--base`, `--json`) | medium |
| 3 | `cli`: `blame`, `sign`, `release` | small |
| 4 | `web` page as verso-blueprint client | medium |
| 5 | `web` sign server with `local` provider, then `openreview`, `orcid`, `github` | medium |
| 6 | `cli`: `equiv` with agent prompt | medium |
| 7 | OpenPhysics: first `@[trusted]` modules, conventions file, memo text | content |

## Later, if needed

- Delta replay with pinned kernel version.
- One records repo per institution; trust-import config with exclusions.
- Account linking across providers.
- Sigstore keyless signatures.
- Delta records ("old -> new is fine").
- Upstream the forks.

## Evaluation plan

Six-month rolling evaluation on fresh papers, see
[06-releases-and-eval.md](06-releases-and-eval.md). Start the clock at the
first fully signed release.
