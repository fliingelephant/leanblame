# 12. Roadmap

## Built

Every command of [04-architecture.md](04-architecture.md), tested end to end by
`cli/test/run.sh`.

## Next

| Item | Size |
|------|------|
| Tiers in `leanblame.toml`: who may sign which declarations, and how many | medium |
| OpenPhysics: first tagged modules, conventions module, memo text | content |

Pages, logins and records written with login-backed ids belong to a service
(OpenVouch), which calls the CLI.

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
