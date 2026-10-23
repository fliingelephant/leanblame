# 12. Roadmap

## Used as is

`leanexport` and its parser, `lake check --paranoid`, `lake comparator`,
mathlib cache, doc-gen4, OpenID Connect and OAuth libraries, git.

## Copied

comparator's closure walk (`Compare.lean`, Apache-2.0). lean-eval's
`@[eval_problem]` attribute code, renamed `@[trusted]`.

## Build, in order

| # | Item | Size |
|---|------|------|
| 1 | `@[trusted]` in a Lake-free target; validators for the four schemas in [14-schemas.md](14-schemas.md) | small |
| 2 | Record schema, validator, CI check that rejects edits to `records/` | small |
| 3 | `cli export` and claim hash: canonical term printing, structure expansion, spec cut | medium |
| 4 | `cli status` (states, flags, `--base`, `--json`) and `blame` | medium |
| 5 | `cli release` with `lake check --paranoid` proof gate and manifest | small |
| 6 | Web page: doc-gen4 plus overlay | small |
| 7 | Sign server: `local`, then `openreview`, `orcid`, `github` | medium |
| 8 | `cli equiv`: `Old.` reconstruction from export, agent prompt, comparator check, object store | medium |
| 9 | Blueprint adapter: `blueprint-manifest.json` → boundary list | small |
| 10 | OpenPhysics: first tagged modules, conventions module, memo text | content |

## Later, if needed

- Delta replay with pinned kernel version.
- Records repos per institution with trust imports and exclusions.
- Account linking across providers.
- Sigstore keyless signatures.
- Delta records.
- Exporters for other proof assistants.

## Evaluation

Six-month rolling evaluation on fresh papers, see
[07-releases-and-eval.md](07-releases-and-eval.md). Clock starts at the first
fully signed release.
