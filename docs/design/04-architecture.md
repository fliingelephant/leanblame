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

The executable reads a **boundary list**, an **export**, and **records**. Its
modules form two layers ([15-generic-core.md](15-generic-core.md)):

- `Core/`, the generic tool: schemas, hashes, the closure walk, records,
  validity, the object store, git. It knows declarations only by printed name,
  with what a frontend reports about each, and never sees a term. The closure
  walk is adapted from comparator's (`Lake/Check/Compare.lean` in the
  toolchain, Apache-2.0): seeds from the boundary list, cuts at tagged
  declarations, hashes specs, collects every mismatch, charges each change to
  a cause.
- `Lean/`, the Lean frontend: `export` and its blueprint reader, `id`, the toolchain's export
  parser, canonical printing, proof erasure, the `leanchecker` kernel gate,
  `equiv`. The export is turned back into a kernel environment by an
  adaptation of core's `Replay.lean`.

`Main` passes the Lean frontend to the core commands.

Nine commands:

| Command | Does |
|---------|------|
| `init` | Create `leanblame.toml` and `records/`. |
| `export [--boundary FILE]` | Build at the current commit using the mathlib cache, run `leanexport`, write the export and the boundary list of the `@[trusted "id"]` declarations, or of a blueprint's (see Blueprints). Outside a git repository with commits: an error. With uncommitted changes under the library root, the boundary list names no commit, and `sign` and `release` refuse it. |
| `id` | Write a new random id into each `@[trusted]` of the library that has none: `@[trusted "id"]`. Commit the change. |
| `status [--json]` | One state per tagged declaration: `valid`, `outdated`, `unsigned`; what blocks it; the causes of any hash move since the last live approval; the `equiv` evidence, if any. `--json`: write the complete index ([14-schemas.md](14-schemas.md)). A graph the store should have and does not is an error. |
| `blame X` | Who signed `X` (a name or an id), when, at which claim hash. |
| `equiv [NAME...]` | For each declaration outdated solely by an `untagged` cause: rebuild the old meaning under `Old.` from the old export, ask the kernel whether old and new are definitionally equal (one call per changed definition), store the proof as an export that `leanchecker` replays. Never writes a record. See [06-versioning.md](06-versioning.md). |
| `sign --signer local:NAME [--withdraw RECORD]` | Write one record from the terminal. Dev path: `local:` ids; provider identities come through the sign server. |
| `validate` | Check record files against the schema and the authority rules (the other commands stop on a file in a records directory that is not a record). Refuse edits or deletions of existing records. Gates every record; where it runs (the service that writes records, or a repository check) is the adopter's choice. |
| `release --tag TAG [--out FILE]` | Kernel replay with `leanchecker --from-export`; per-theorem axiom report; manifest, into the object store (and FILE). Fails only on an invalid signoff, a kernel error or a non-permitted axiom. Open theorems are counted, not failed. |

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

## Blueprints

`export --boundary FILE` reads verso-blueprint's `blueprint-manifest.json`
instead of `@[trusted]`: statement entries name their Lean declarations in
`codeData`, the text comes from the `statement` slot of `externalMarkup` or else
the entry's fragment in `blueprint-html-cache.json`. A label is the id of the
first declaration it names; its other declarations name that one as `parent`.
A name claimed by two labels, or a statement entry without label or text, is
an error.

## Config: `leanblame.toml`

```toml
records = ["records/"]          # records directories (local; a URL is an error for now)
exclude = ["sha256:…"]          # approve records this library refuses to count
required_signers = 1            # distinct live approvals a declaration needs
allowed_signers = "any"         # or a list of provider:id
```

Validity is a rule over records. The two signer knobs are the whole policy;
`status` reads them. Who gets *asked* to review is a queue in the web, not
part of validity.

No axiom list. Permitted axioms are the three standard ones plus any tagged,
signed `axiom` in the library or its tagged dependencies.

## Storage

- Code, records, config: git.
- Exports, boundary lists, graphs, `equiv` proofs, release manifests: an
  object store keyed by hash, one directory per kind
  (`.leanblame/store/<kind>/`). A graph is an export hashed against a boundary
  list: every claim hash, with the parts `status` compares and the axiom
  report. `export` writes it; the other commands read it and never hash. It is
  the one kind keyed by what it was computed from instead of its own bytes:
  `graphs/<export>-<boundary list>.json`. `export` deletes what nothing names
  any more: exports and boundary lists named by no record and not current, the
  graphs of deleted exports, evidence whose claim is no longer current, proofs
  named by no evidence and no record.
- `equiv` evidence: `.leanblame/equiv/evidence/`, one file per declaration and
  claim hash, naming the proof and the record it was compared with.

## Platform

`export`, `equiv` and `release` run wherever the library's toolchain is
installed: `export` builds the library (`lake build`), runs the exporter
in-process and hashes; `release` and `equiv` run `leanchecker`. `status`,
`blame`, `sign` and `validate` need no toolchain: they read graphs from the
object store, and records.

## Reuse

| Used as is | Copied and changed | New |
|------------|--------------------|-----|
| `leanexport` and its parser, `leanchecker`, Lake's TOML reader and git helpers, mathlib cache, doc-gen4, OIDC/OAuth libraries, git | comparator's closure walk; core's `Replay.lean` | claim hash, cause analysis, records and validator, `status`/`blame`/`release`, sign server, `Old.` reconstruction, page overlay |

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

On change, `status` reports state and causes and `equiv` may add evidence; who
acts is the table in [03-trust-model.md](03-trust-model.md).

## Interfaces

Boundary list, record, release manifest, `status --json`. Exact fields in
[14-schemas.md](14-schemas.md).

## Language

Lean for the CLI, TypeScript for the web. Lean FRO writes core tools in Lean
and web tools in TypeScript. Rust was considered and dropped: it would need a
second export parser or an orchestration-only binary.

## Beyond Lean

Another proof assistant needs a frontend. It implements `Source`, which serves
one export to the core: per declaration its name, kind, role, universe
parameters, the hashes of its canonical statement and body with proofs erased,
its dependencies, and what it rests on for the axiom report. And `Backend`:
the `Source` of a stored export, a replay by the assistant's own checker and
that checker's name, its standard axioms, and the axioms that stand for a
missing proof. `export` keeps the names in the graph. Exact fields in
[15-generic-core.md](15-generic-core.md). `export` and `equiv` belong to the
frontend too. The core, records, the validity rules, `status`, `blame`, `sign`,
`validate`, `release` and the web are unchanged.
