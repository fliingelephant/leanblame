# 4. Architecture

## Two repositories

| Repo | Owns | Contains no |
|------|------|-------------|
| `leanblame` | CLI (Lean package), web (sign server + page), schemas | physics, or any field content |
| `openphysics` (first user) | Lean library, `records/`, `leanblame.toml` | auth code, page code |

Any other library adopts LeanBlame the same way.

## Three parts

### 1. `cli` (Lean package)

Two Lake targets. A tiny library with the `@[trusted]` attribute and nothing
else, so user modules never import Lake. And the executable.

The executable reads a **boundary list**, an **export**, and **records**.
It uses the toolchain's export parser and its own closure walk, adapted from
comparator's `Compare.lean` (one Apache-2.0 file): seeds from the boundary
list, cuts at tagged declarations, hashes specs, skips proofs, collects every
mismatch.

| Command | Does |
|---------|------|
| `export` | Build at the current commit using the mathlib cache, run `leanexport`, write the export and the boundary list. |
| `status [--base A] [--json]` | One state per tagged declaration: **valid**, **outdated**, **unsigned**; flags **equiv-proven**, **withdrawn**, **blocked-by**. `--base A`: name the dependencies that changed since export `A`. `--json`: write the index the page reads. |
| `blame X` | Who signed `X`, when, at which claim hash. |
| `equiv` | For each outdated declaration: rebuild the old meaning from the old export under `Old.`, ask an agent to prove `Old.X = X`, check the proof with `lake comparator`, store the proof as evidence. Never writes a record. |
| `sign` | Write one record from the terminal. Dev path, `local:` ids only unless a provider token is given. |
| `release` | Run `lake check --paranoid` with the library's permitted axioms, mark each theorem proven or open, write the release manifest. Fails unless every tagged declaration is valid. |

### 2. `records` (git)

One file per signoff in the library's `records/` folder. Schema and validator
in `leanblame`. The validator runs as a required CI check and rejects any
commit that modifies or deletes an existing record. See
[05-records.md](05-records.md).

### 3. `web` (TypeScript)

- **Sign server.** Logs the reviewer in (OpenID Connect for OpenReview and
  ORCID, OAuth 2.0 for GitHub, `local` for dev), shows the declaration with its
  informal text, type, dependencies and their signers, and on approval writes
  one record. The reviewer never touches git.
- **Page.** doc-gen4 output for the library, plus an overlay from
  `status --json`: signers, state, blocked-by, withdrawn. Blueprint pages can
  read the same JSON and show the same badges.

## Adapters

Input adapters produce a boundary list. Shipped: `@[trusted]` attribute; a
reader for verso-blueprint's `blueprint-manifest.json`. Others are ~20 lines.

Output is `status --json`. Any page can read it.

## Config: `leanblame.toml` in the library

```toml
records = ["records/", "https://github.com/some-institute/records"]
exclude = ["sha256:…"]          # disputed records to ignore
permitted_axioms = ["propext", "Quot.sound", "Classical.choice"]
conventions = "OpenPhysics.Conventions"
providers = ["openreview", "orcid", "github"]
```

## Storage

- Code, records, config: git.
- Exports (50–250 MB each) and `equiv` proofs: an object store keyed by hash,
  not git. Only the current export and the exports named by records are kept.

## Platform

`status`, `blame`, `sign` run anywhere. `equiv` builds agent-written code and
`lake comparator` needs a Linux sandbox, so both run in Linux CI.

## Reuse

| Used as is | Copied and changed | New |
|------------|--------------------|-----|
| `leanexport` and its parser, `lake check --paranoid`, `lake comparator`, mathlib cache, doc-gen4, OIDC libraries, git | comparator's closure walk; lean-eval's attribute code | claim hash, records and validator, `status`/`blame`/`release`, sign server, `Old.` reconstruction, page overlay |

No forks. No upstream pull requests needed.

## Data flow

```
author tags declarations
  -> cli export
  -> web shows declaration to reviewer
  -> reviewer approves
  -> record committed, validator passes
  -> cli status --json -> page
```

On change:

```
cli export
  -> cli status
       -> hash unchanged: valid
       -> tagged dependency not valid: blocked, wait for its signer
       -> hash changed: outdated
            -> cli equiv
                 -> proven: equiv-proven; reviewer approves new hash with one click
                 -> not proven: reviewer reads the change
```

## Interfaces LeanBlame commits to

Boundary list, record, release manifest, `status --json`. Exact fields in
[14-schemas.md](14-schemas.md).

## Language

Lean for the CLI, TypeScript for the web. Lean FRO writes core tools in Lean
(comparator, lean4export, lean-eval, lean4checker, verso-blueprint) and web
tools in TypeScript (comparator-live). Rust was considered and dropped: it would
need a second export parser or an orchestration-only binary.
