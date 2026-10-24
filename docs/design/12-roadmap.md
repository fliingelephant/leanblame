# 12. Roadmap

## Used as is

`leanexport` and its parser, `leanchecker`, Lake's TOML reader and git
helpers, mathlib cache, doc-gen4, OpenID Connect and OAuth libraries, git.

## Copied

comparator's closure walk (`Compare.lean`, Apache-2.0).

## Build, in order

Done in `cli/`: 1 to 5, 8, 9, and the `local:` and `--withdraw` parts of 7.
Next: 6, the rest of 7, 10.

| # | Item | Size |
|---|------|------|
| 1 | `@[trusted]` in a Lake-free target; `init`; the four schemas in [14-schemas.md](14-schemas.md) | small |
| 2 | `validate`: schema, authority rules, no edits to existing records | small |
| 3 | `export` and claim hash: canonical printing, proof erasure, group hashes, structure expansion, spec cut | medium |
| 4 | `status` (states, causes, blocked-by, `--json`) and `blame` | medium |
| 5 | `release`: `leanchecker` replay, axiom report, manifest | small |
| 6 | Web page: doc-gen4 plus overlay | small |
| 7 | Sign server: `local`, then `openreview`, `orcid`, `github`; `sign --withdraw` | medium |
| 8 | `equiv`: shared/duplicated `Old.` reconstruction, goal by kind, `leanchecker` replay, object store | medium |
| 9 | Blueprint adapter and manual list adapter → boundary list | small |
| 10 | OpenPhysics: first tagged modules, conventions module, memo text | content |

## Later, if needed

- Delta replay with pinned kernel version.
- Records repos per institution with trust imports and exclusions.
- Account linking across providers.
- Sigstore keyless signatures.
- Delta records.
- A frontend, `Backend` and `Source`, for another proof assistant.

## Evaluation

Six-month rolling evaluation on fresh papers, see
[07-releases-and-eval.md](07-releases-and-eval.md). Clock starts at the first
fully signed release.
