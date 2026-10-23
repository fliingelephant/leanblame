# 3. Architecture

## Two repositories

| Repo | Owns | Contains no |
|------|------|-------------|
| `leanblame` | CLI (Lean package, includes the `@[trusted]` attribute), web (sign server + page), record schema | physics, or any field content |
| `openphysics` (first user) | Lean library with `@[trusted]` declarations, `records/`, config | auth code, page code |

Any other library adopts LeanBlame the same way: a Lean package, a records
folder, a config file.

## Three parts

### 1. `cli` (Lean package)

One Lake package. It imports comparator's `Export.Parse` and `Compare` modules
as libraries, so "same declaration" means exactly what comparator means. No
second export parser.

It ships one attribute, `@[trusted]`, modeled on lean-eval's
`@[eval_problem]`. Put it on every declaration a human must read. The CLI
generates the comparator config from it.

Six commands:

| Command | Does |
|---------|------|
| `export` | Build the library at a commit using the mathlib cache, run `lean4export`, store the export file and its hash. |
| `status [--base A] [--json]` | For every `@[trusted]` constant: **valid**, **outdated**, **equiv-proven**, **unsigned**, or **withdrawn**. With `--base A`, compare against export `A` and list changed constants (comparator across two exports). With `--json`, emit the machine-readable index the web reads. |
| `blame X` | Who signed constant `X`, when, at which export hash. |
| `equiv` | For each outdated constant: copy the old definition into the current build, hand an agent the goal `old = new`, run comparator on the result, attach the outcome. Never changes a record. |
| `sign` | Write one record from the terminal. The web is the normal path. |
| `release` | Write a release manifest. Fails unless every trusted constant is valid. |

### 2. `records` (git)

One file per signoff in the library's `records/` folder. Schema and validator
live in `leanblame`. See [04-records.md](04-records.md).

### 3. `web` (TypeScript)

- **Sign server.** Logs the reviewer in through any OpenID Connect or OAuth
  provider, shows the trusted module with context, and on approval writes one
  record. The reviewer never touches git.
- **Page.** Reads `status --json`. Shows modules, constants, who signed what,
  validity per release, withdrawn records, outdated constants waiting for
  review. Built as a verso-blueprint custom client, so prose, Lean, and the
  dependency graph come from blueprint and signoffs are overlaid per node.

## Storage and visualization are decoupled

Storage: git repos (library, records) plus export files. Visualization: any
program that reads `status --json`. The page is one such program. OpenPhysics
may use it or write its own.

## Reuse policy: fork and pin

No upstream pull requests for now. Fork, patch, pin a commit:

| Fork | Patch |
|------|-------|
| `leanprover/comparator` (archived, standalone) | statements-only mode: compare theorem types, skip theorem values, keep comparing definition values |
| `leanprover/comparator-live` | trusted challenges carry signer records |
| `leanprover/verso-blueprint` | per-node external metadata overlay for signoff status |
| `leanprover/lean-eval` | copy the attribute and config generator (Apache 2.0) |

Upstream later if the patches prove out.

## Data flow

Normal path:

```
author marks declarations @[trusted]
  -> cli export
  -> web shows module to reviewer
  -> reviewer approves
  -> record committed
  -> cli status --json -> page
```

Upstream change (mathlib bump, or an edit to a signed definition):

```
cli export (new commit)
  -> cli status --base <old export>
       -> unchanged: valid, nothing to do
       -> changed constant X: outdated
            -> cli equiv
                 -> proven: X shown as equiv-proven; reviewer approves new hash with one click
                 -> not proven: reviewer reads new X
```

## Interfaces LeanBlame commits to

1. Record schema.
2. Release manifest schema.
3. `status --json` schema.

Everything else may change.

## Language choice

Lean for the CLI, TypeScript for the web. This matches the ecosystem: Lean FRO
writes core tools in Lean (comparator, lean4export, lean-eval, lean4checker,
verso-blueprint) and web tools in TypeScript (comparator-live, lean-atlas).
Rust was considered. It would require either a second export parser (nanoda
has one) with a risk of drifting from comparator, or an orchestration-only
binary that shells out to comparator. Neither buys much here.
