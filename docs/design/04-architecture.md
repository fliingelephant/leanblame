# 4. Architecture

## Who owns what

| Part | Owns | Contains no |
|------|------|-------------|
| `leanblame` | the CLI (a Lean package) and its schemas | field content, service code |
| a library (first: OpenPhysics) | its Lean code, `records/`, `leanblame.toml` | LeanBlame code |
| a service (first: OpenVouch) | pages, logins, writing records; it calls the CLI | validity rules |

LeanBlame knows nothing about any service.

## The CLI

Two Lake targets users see. A tiny library with the `@[trusted]` attribute and
nothing else, so user modules never import Lake. And the executable, whose own
modules sit in an internal third library: Lake builds an executable's imports
only from library targets.

The executable reads a **boundary list**, an **export**, and **records**. Its
modules form two layers:

- `Core/`, the generic tool: schemas, hashes, the closure walk, records,
  validity, the object store, git. It knows declarations only by printed name,
  with what a frontend reports about each, and never sees a term. The closure
  walk is adapted from comparator's (`Lake/Check/Compare.lean` in the
  toolchain, Apache-2.0): seeds from the boundary list, cuts at tagged
  declarations, hashes specs, collects every mismatch, charges each change to
  a cause.
- `Lean/`, the Lean frontend: `export` and its blueprint reader, `id`, the toolchain's export
  parser, canonical printing, proof erasure, the `leanchecker` kernel gate,
  `equiv`, challenges. The export is turned back into a kernel environment by an
  adaptation of core's `Replay.lean`. It maps printed names back to its constants and
  fails if two constants of one export print the same.

A module under `Core/` imports only `Init`, `Std`, `Lean.Data.*`, `Lake.Toml`,
`Lake.Util.*` and other `Core/` modules: nothing in it knows what a Lean term,
environment or kernel is. `Main` passes the Lean frontend to the core commands.

Eleven commands (`challenge` has two forms):

| Command | Does |
|---------|------|
| `init` | Create `leanblame.toml` and `records/`. |
| `export [--boundary FILE] [--lib NAME]` | Build the libraries (`--lib`, else the default `lean_lib` targets) at the current commit, using the mathlib cache, run `leanexport`, write the export and the boundary list of the `@[trusted "id"]` declarations, or of a blueprint's (see Blueprints). Outside a git repository with commits: an error. With uncommitted changes under the library root, the export names no commit, and `sign` and `release` refuse it. |
| `id` | Write a new random id into each `@[trusted]` of the library that has none: `@[trusted "id"]`. Commit the change. |
| `status [--json]` | One state per tagged declaration: `valid`, `outdated`, `unsigned`; what blocks it; the causes of any hash move since the last live approval; the `equiv` evidence, if any. `--json`: write everything, records included, and nothing on stderr ([14-schemas.md](14-schemas.md)). A graph the store should have and does not is an error. |
| `blame X` | Who signed `X` (a name or an id), when, at which claim hash, and what each approval is worth now. |
| `diff --from RECORD [--to RECORD] [--json] [X...]` | What changed between the export an approve record names and another's, or the last export: the comparison `status` makes against the last live approval, for two points the caller picks, with both readable versions ([14-schemas.md](14-schemas.md) §5). Reads graphs from the store; a point whose export the store lacks is an error. |
| `equiv [X...]` | For each declaration outdated solely by an `untagged` cause: rebuild the old meaning under `Old.` from the old export, ask the kernel whether old and new are definitionally equal (one call per changed definition), store the proof as an export that `leanchecker` replays. Never writes a record. See [06-versioning.md](06-versioning.md). |
| `sign --signer local:NAME [--withdraw RECORD]` | Write one record from the terminal, with a `local:` signer id. Ids backed by a login come from a service that writes records. |
| `validate` | Check record files against the schema and the authority rules (the other commands stop on any of these problems). Refuse edits or deletions of existing records. Gates every record; where it runs (the service that writes records, or a repository check) is the adopter's choice. |
| `challenge [X...] --out DIR` | Write the comparator challenge of the tagged theorems `X` (names or ids) into the new directory DIR, from the last export (see Challenges). Without names: only `ChallengeDeps.lean`, which every challenge of the library shares. |
| `challenge --check DIR` | Build the challenge in DIR against the library's build and hash it as `export` does: each tagged declaration in it must have the claim hash of the last export. A difference fails with the cause `status` would give. |
| `release --tag TAG [--out FILE]` | Kernel replay with `leanchecker --from-export`; per-theorem axiom report; manifest, into the object store (and FILE). Fails only on an invalid signoff, a kernel error or a non-permitted axiom. Open theorems are counted, not failed. |

## Records

One TOML file per signoff in the library's records directories (`records/` by
default). Schema and validator in `leanblame`. See [05-records.md](05-records.md).

## Blueprints

`export --boundary FILE` reads verso-blueprint's `blueprint-manifest.json`
instead of `@[trusted]`: statement entries name their Lean declarations in
`codeData`, the text comes from the `statement` slot of `externalMarkup` or else
the entry's fragment in `blueprint-html-cache.json`. A label is the id of the
first declaration it names; its other declarations name that one as `parent`,
and their ids are the label and their names (`def:point/norm`). A name claimed
by two labels, a statement entry without label or text, and a value of an
unexpected type are errors.

## Challenges

A comparator challenge must not depend on the library it comes from: it carries
what its theorems need, and nothing else. `export` finds that in the one
environment it imports, and takes it from the library's source as pieces: one
piece per command a challenge needs, as written. Nothing is elaborated again.
`challenge` joins the pieces into a challenge.

- What a challenge needs: the statements of the tagged theorems, the other
  tagged declarations, and what these use, then what that uses, and so on. A
  declaration uses the constants in its kernel terms (the type; the value or
  proof of one a challenge holds) and those its source names (the `.ilean`, as
  for "find references"). A module that gives a challenge something gives it
  all its instances, since Lean uses them without naming them; an `attribute`
  command comes along when it names kept declarations only.
- A piece is a command, from its first token (the docstring) to its end. Its
  scope comes with it: the `namespace`, `section`, `open`, `variable`,
  `universe` and `set_option` commands before it, and their `end`s; a command
  that opens or closes several scopes (`namespace A.B`) comes for each. A module's
  pieces start with a `section` of their own and end with a piece that closes
  what the module leaves open, so that nothing one module opens reaches the next.
  Lean refuses an `open` of a namespace that does not exist yet: one that no
  piece before it makes, and no constant of the modules the challenge imports,
  is declared at the start of the module's `section` (`namespace N` `end N`);
  declaring one that exists changes nothing.
- Module-system words (`module`, `public`, `meta`, `@[expose]`) and
  `@[trusted]` go. A name that would read differently in one file with the other
  modules is written as Lean writes it (`unresolveNameGlobal`): a name the
  `.ilean` says refers to a constant, which in the library's whole environment,
  with the command's namespace and `open`s, reads as other constants too or
  instead. A challenge holds some of those constants, so a name that reads as
  its constant alone, or as none (a local), reads the same there.
- `export` stops on: a tagged declaration no command declares; a tagged theorem
  that what its challenge holds uses (its proof would be in
  `ChallengeDeps.lean`); two `private` declarations of one name in two modules;
  two modules with pieces built with different Lean options.
- `challenge X... --out DIR` joins the pieces as lean-eval joins a challenge.
  `ChallengeDeps.lean` imports every module from outside the library that the
  library's modules import (through the library modules they import), then
  holds the pieces of each module, in import order, but the tagged theorems: it
  is the same for every challenge of the library. `Challenge.lean` imports it
  and holds, for each module with a named theorem, its scope pieces with the
  statements, proofs `sorry`. `lakefile.toml` requires what the library's
  lakefile requires, by git (LeanBlame left out; a path is an error), and sets
  `[leanOptions]` to the options Lake builds those modules with: its
  `leanOptions` and the `-D` options of `moreLeanArgs` and `weakLeanArgs`.
  `lean-toolchain` is the library's.
- `challenge --check DIR` builds the challenge with `lean` against the
  library's build, exports it and hashes it as `export` hashes the library. Each
  tagged declaration it holds must have the claim hash of the last export, and
  every tagged declaration but the theorems must be there: the challenge then
  means what the signers signed. A private name holds the module it is written
  in, so the challenge's private constants are hashed under the library's names.

## Config: `leanblame.toml`

```toml
records = ["records/"]          # records directories (local; a URL is an error for now)
exclude = ["sha256:…"]          # approve records this library refuses to count
required_signers = 1            # distinct live approvals a declaration needs
allowed_signers = "any"         # or a list of provider:id
```

Every key is required; `init` writes them all. Validity is a rule over records.
The two signer knobs are the whole policy; `status` reads them. Who gets *asked* to review is a service's queue, not
part of validity.

No axiom list. Permitted axioms are the three standard ones plus any tagged,
signed `axiom` in the library or its tagged dependencies.

## Storage

- Code, records, config: git.
- Exports, boundary lists, graphs, challenge pieces, `equiv` proofs, release manifests: an
  object store keyed by hash, one directory per kind
  (`.leanblame/store/<kind>/`). A graph is an export hashed against a boundary
  list: every claim hash, with the parts `status` compares and the axiom
  report. `export` writes it; the other commands read it and never hash. It is
  the one kind keyed by what it was computed from instead of its own bytes:
  `graphs/<export>-<boundary list>.json`, both by their hashes; a graph that is
  not complete is an error. `.leanblame/current` points at the last export and
  its pieces, with the commit, toolchain and dependencies it was made from.
  `export` deletes what nothing names any more: exports and boundary lists named
  by no record and not current, the graphs of deleted exports, pieces that are
  not current, evidence whose claim is no longer current, proofs named by
  no evidence and no record. Validity compares the records' claims with the graph
  of the current code, which whoever judges makes with `export`. Graphs of old
  exports only explain causes and show diffs; they never change a state.
- `equiv` evidence: `.leanblame/equiv/evidence/<claim>.json`, one file per claim
  hash, naming the declaration's id, the proof and the record it was compared
  with. Every JSON file here has a schema id and is read strictly.

## Platform

`export`, `equiv` and `release` run wherever the library's toolchain is
installed: `export` builds the library (`lake build`), runs the exporter
in-process and hashes; `release` and `equiv` run `leanchecker`. `status`,
`blame`, `sign` and `validate` need no toolchain: they read graphs from the
object store, and records.

## Reuse

| Used as is | Copied and changed | New |
|------------|--------------------|-----|
| `leanexport` and its parser, `leanchecker`, Lake's TOML reader and git helpers, mathlib cache, git | comparator's closure walk; core's `Replay.lean` | claim hash, cause analysis, records and validator, `status`/`blame`/`diff`/`release`, `Old.` reconstruction, challenge pieces |

No forks.

## Data flow

```
author tags declarations
  -> cli export
  -> a reviewer reads the declaration (in a service's page, or the terminal)
  -> a record is written (cli sign), validated and committed
  -> cli status --json -> any viewer
```

On change, `status` reports state and causes, `diff` shows what changed, and
`equiv` may add evidence; who acts is the table in [03-trust-model.md](03-trust-model.md).

## Formats

Boundary list, record, release manifest, `status --json`, challenge pieces,
`diff --json`. Exact fields in [14-schemas.md](14-schemas.md).

## Language

Lean. The CLI reuses the toolchain's export parser, kernel and Lake; another
language would need a second export parser.

## Beyond Lean

Another proof assistant needs a frontend. It implements `Source`, which serves
one export to the core: per declaration its name, kind, role, universe
parameters, the hashes of its canonical statement and body with proofs erased,
its dependencies, and what it rests on for the axiom report. And `Backend`:
the `Source` of a stored export, a replay by the assistant's own checker and
that checker's name, its standard axioms, and the axioms that stand for a
missing proof. `export` keeps the names in the graph. Exact fields in
`cli/LeanBlame/Core/Graph.lean`. `export` and `equiv` belong to the frontend too.
The core, records, the validity rules, `status`, `blame`, `diff`, `sign`,
`validate`, `release`, and every service on the CLI stay as they are.
