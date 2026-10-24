# 4. Architecture

## Two repositories

| Repo | Owns | Contains no |
|------|------|-------------|
| `leanblame` | CLI (Lean package), web (sign server + page), schemas | physics, or any field content |
| `openphysics` (first user) | Lean library, `records/`, `leanblame.toml` | auth code, page code |

## Three parts

### 1. `cli` (Lean package)

Two Lake targets users see. A tiny library with the `@[trusted]` attribute and
nothing else, so user modules never import Lake. And the executable, whose own
modules sit in an internal third library: Lake builds an executable's imports
only from library targets.

The executable reads a **boundary list**, an **export**, and **records**. It
uses the toolchain's export parser and its own closure walk, adapted from
comparator's `Compare.lean` (one Apache-2.0 file): seeds from the boundary
list, cuts at tagged declarations, hashes specs, skips proofs, collects every
mismatch, charges each change to a cause.

Eight commands:

| Command | Does |
|---------|------|
| `init` | Create `leanblame.toml`, `records/`, and the CI job that runs `validate`. |
| `export [--boundary FILE]` | Build at the current commit using the mathlib cache, run `leanexport`, write the export and the boundary list. `--boundary` takes a list from an adapter instead of `@[trusted]`. |
| `status [--base A] [--json]` | One state per tagged declaration: `valid`, `outdated`, `unsigned`; flags `equiv-proven`, `withdrawn`, `blocked-by`; the cause of any hash move. `--base A`: compare with approve record `A`, that is with the export and boundary list it names. `--json`: write the complete index ([14-schemas.md](14-schemas.md)). |
| `blame X` | Who signed `X`, when, at which claim hash. |
| `equiv` | For each declaration outdated solely by an `untagged` cause: rebuild the old meaning under `Old.`, ask an agent to prove it equal to the new one, check with `lake comparator`, store the proof. Never writes a record. See [06-versioning.md](06-versioning.md). |
| `sign [--withdraw RECORD]` | Write one record from the terminal. Dev path; `local:` ids unless a provider token is given. |
| `validate` | Check record files against the schema and the authority rules. Refuse edits or deletions of existing records. Runs in CI on every pull request. |
| `release` | Kernel replay with `leanchecker --from-export`; per-theorem axiom report; manifest. Fails only on an invalid signoff or a non-permitted axiom. Open theorems are counted, not failed. |

### 2. `records` (git)

One TOML file per signoff in the library's `records/` folder. Schema and
validator in `leanblame`. See [05-records.md](05-records.md).

### 3. `web` (TypeScript)

- **Sign server.** Logs the reviewer in (OpenID Connect for OpenReview and
  ORCID, OAuth 2.0 for GitHub, `local` for dev), shows the declaration with its
  informal text, kernel-level type with notation off, dependencies and their
  signers, the cause of any pending change, and on approval writes one record.
- **Page.** doc-gen4 output plus an overlay from `status --json`: signers,
  state, cause, blocked-by, history. Any other viewer reads the same JSON.

## Adapters

Input adapters produce a boundary list. Shipped: `@[trusted]`; a reader for
verso-blueprint's `blueprint-manifest.json`; a hand-written TOML list
(`informal_source = "manual"`).

## Config: `leanblame.toml`

```toml
records = ["records/", "https://github.com/some-institute/records"]
exclude = ["sha256:…"]          # approve records this library refuses to count
conventions = "OpenPhysics.Conventions"
providers = ["openreview", "orcid", "github"]
required_signers = 1            # distinct live approvals a declaration needs
allowed_signers = "any"         # or a list of provider:id, or a records repo
```

Validity is a rule over records. The two signer knobs are the whole policy;
`status` reads them. Who gets *asked* to review is a queue in the web, not
part of validity.

No axiom list. Permitted axioms are the three standard ones plus any tagged,
signed `axiom` in the library or its tagged dependencies.

## Storage

- Code, records, config: git.
- Exports, boundary lists, `equiv` proofs, `status` logs: an object store
  keyed by hash. Every export named by a live record is kept.

## Platform

`status`, `blame`, `sign`, `validate` run anywhere. `export`, `equiv` and
`release` build code or run checkers and run in Linux CI.

## Reuse

| Used as is | Copied and changed | New |
|------------|--------------------|-----|
| `leanexport` and its parser, `leanchecker`, `lake comparator`, mathlib cache, doc-gen4, OIDC/OAuth libraries, git | comparator's closure walk; lean-eval's attribute code | claim hash, cause analysis, records and validator, `status`/`blame`/`release`, sign server, `Old.` reconstruction, page overlay |

No forks.

## Data flow

```
author tags declarations
  -> cli export
  -> web shows declaration to reviewer
  -> reviewer approves
  -> record committed, validate passes
  -> cli status --json -> page
```

On change:

```
cli export
  -> cli status
       -> hash unchanged: valid
       -> tagged dependency not valid: blocked, wait for its signer
       -> hash changed: outdated, with causes
            -> cause is only `untagged`: cli equiv
                 -> proven: equiv-proven; reviewer approves with one click
                 -> not proven: reviewer reads the change
            -> any other cause: reviewer reads the shown diff
```

## Interfaces

Boundary list, record, release manifest, `status --json`. Exact fields in
[14-schemas.md](14-schemas.md).

## Language

Lean for the CLI, TypeScript for the web. Lean FRO writes core tools in Lean
and web tools in TypeScript. Rust was considered and dropped: it would need a
second export parser or an orchestration-only binary.

## Beyond Lean

Only `export`, `equiv` and `release` know Lean. A backend for another proof
assistant replaces those three. Records, hashing rules, `status`, `blame`,
`sign`, `validate` and the web are unchanged.
