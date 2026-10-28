# 11. Decisions

Each entry: the decision, the reason, what was rejected.

### What a signature covers

Your own declaration fully; for tagged declarations you use, only name, type
and informal text; for untagged ones, everything underneath; proofs never.
Full text: [03-trust-model.md](03-trust-model.md). Rejected: full-closure hash
(re-sign on body changes you never read); names-only (not told when the
informal text changes meaning).

### Three kinds of authority

Over a record: its signer only. Over a library: its maintainers via git, who
tag, choose records repos, exclude records, release. Over identity: the login
provider and the hosting institution. Nobody edits another person's record;
a maintainer excludes it. Who wrote a declaration (git author, possibly an
agent) is separate from who signed it (always a human).

### What goes into the hash

Everything that changes meaning, nothing else. In: kind, role, name, universe
parameters, type and body with proof subterms erased, informal text of
tagged declarations. Out: proofs (wherever they occur: proof irrelevance),
binder names, implicitness, kernel hints, recursor rules. Cycles hashed as groups. `unsafe` cannot be tagged.
The rules read the role (`assumed`, `defined`, `proved`), so they hold for
any proof assistant; `kind` is the assistant's own label, and a body the kernel
does not see has no body hash. Rejected: Lean's kinds and safety as fixed lists
in the hash.

### `equiv` says why, and only for untagged causes

A hash move is charged to causes: own text, own body, dependency spec, cut
moved, untagged. `equiv` runs only when `untagged` is the sole cause, shares
unchanged constants, duplicates changed ones under `Old.`, and states equality
for same-typed values or `↔` for statements. Everything else is read by a
human.

### Humans never read proofs

The kernel checks them. Human reading adds nothing and costs the scarcest
resource.

### Agents inform, never decide

The kernel's answer from `equiv` is shown as evidence. The reviewer clicks.
Any agent check (vacuity, triviality, back-translation) may be shown as
information, never as a decision. Infrastructure for the signer is therefore plain: good
pretty-printing, hover to unfold, signer of each dependency, informal text next
to Lean.

### Why a claim hash and not `git blame` on the file

Git hashes text. Meaning changes with zero text change when an upstream
definition moves. And an upstream change has no diff in your repo. Git is the
storage; the claim hash is the identity.

### The boundary list is the input

Declarations plus informal text, from `@[trusted "id"]` or a verso-blueprint
manifest. Keeps LeanBlame independent of how a project plans or displays its
work: a blueprint project can sign statements before they are proved. An id is
how a declaration is cited and followed (owner, 2026-10-26): from a blueprint,
a label is the id of the first declaration it names, the parent of the others.
Rejected: a hand-written list, which has no ids.

### `status --json` is the output

It carries everything a viewer shows, so no viewer computes it again.
Rejected: building on verso-blueprint, which would force every library to
author Verso documents.

### One record type, no delta records

`action = approve | withdraw`. Not now: richer kinds and cargo-vet-style
delta records, harder to explain than useful.

### No merge or rebase

Approvals accumulate; they never conflict. Two edits of a declaration are two
hashes. `status` says what needs re-approval.

### Blame for independent changes that clash later

The signer of the module where the clash first appears owns that module. The
later signer owns compatibility with the conventions module. Nobody is blamed
retroactively.

### Kernel gate and axiom report

`lake check` hard-codes the three standard axioms and fails on `sorry`, so it
cannot serve a library with open theorems or signed axioms. `release` replays
with `leanchecker` and computes the axiom report itself. Permitted axioms are
the standard three plus tagged, signed axioms. Open theorems are reported,
never a failure. No axiom config.

### `equiv` rebuilds old meaning from the old export

Never from old source, which re-elaborates against new mathlib and makes
`old = new` trivially true. Records store the export and boundary hashes so
the old meaning can be found.

### Notation is not on the boundary

It never reaches the kernel. Conventions are declarations. Statements are
printed with notation (`pretty`) and without (`plain`).

### Formats and commands

TOML for what humans read in git (records, config), JSON for what programs
read. The commands are in [04-architecture.md](04-architecture.md).

### No forks

Adapt two Apache-2.0 files, comparator's closure walk and core's `Replay.lean`
(export to kernel environment). Use `leanexport`,
`leanchecker` and Lake's TOML reader as is. Rejected: forking the
archived comparator (it lacks `--from-export`), running `lake comparator` on
`equiv`'s proofs (the kernel has already checked them in-process; `leanchecker`
replays the stored export), comparator-live (no role in the data flow),
verso-blueprint (see above).

### Lean CLI

The CLI reuses the toolchain's export parser and data types. Another language
would need a second parser or an orchestration-only binary.

### Delta replay deferred

Sound by weakening, same as `import`. Needs a read-only hash-pinned base and a
pinned kernel version. Add only if throughput forces it.

### Distributed storage, no distributed build

Records repos per institution, exports in an object store, any viewer.
Mathlib's cache and Reservoir already work this way.

### Identity

Any provider, stable id stored as `provider:id`. GitHub numeric id, not login.
Cryptographic signing parked.

### Names

**LeanBlame**: the infrastructure. Says what it does; fits LeanDojo,
LeanSearch, LeanCopilot. **OpenPhysics**: the first library. Rejected:
OpenBlame (physicists parse "blame" better next to "Lean"), leanit (says
nothing).

### Who may sign, and how many

Per library, in `leanblame.toml`: `allowed_signers` (any, or a list) and
`required_signers` (`init` writes 1). Pure rule over records, no Lean in it.
Reviewer assignment is a service's queue and never affects validity.

### Declaration ids (owner, 2026-10-26)

Each tagged declaration gets a random UUID in its source, `@[trusted "id"]`,
written by `leanblame id`, never by `export` (a build on a server would make a
new one each time). It survives renames and edits; the name is a label. It is
not hashed, so writing it changes no claim. A cite is `id@record`: the record
fixes the commit, the Lean version and the dependency commits. Not the commit
alone (it moves when anything changes) and not the claim (it stops at signed
dependencies). `export` refuses a tag without an id, and two declarations with
one id. A structure's field has no id of its own; its id is the structure's id
and its name, `3f2b…/x` (owner: "Structure id + field name"), so a rename of the
structure keeps the field's history. A blueprint label's other declarations get
the label and their names the same way.

### Fail out loud (owner, 2026-10-26)

"I want things break out loud if not expected." An unexpected state is an
error, not a warning: a tag without an id, a graph the store should have
(its export and boundary list are there) and does not, a graph file that does
not read, `export` outside a git repository with commits, `sign` without
`--signer` (no default from the environment), a remote records repository in
`leanblame.toml`, a file in a records directory that is not a record. An export
of uncommitted changes names no commit (`null`), so `sign` and `release` refuse
it: a record names the commit it signs. A record made in another store, whose
objects this store lacks, is expected: its causes are unknown, `change` is
`null`. Development stage: no backward compatibility; after a format change,
data is made again.

### Root causes (owner, 2026-10-26: "Fix the three in root causes")

1. **Viewers compute nothing.** `status --json` carries what LeanBlame knows:
   the record files, the standing of approvals, the toolchain, the standard
   axioms. A viewer only displays it.
2. **No defaults on errors.** Every JSON file has a schema id and is read strictly:
   a missing or an unknown key is an error. Every `leanblame.toml` key is
   required. No fallback on a failure: proof erasure, the statement printer,
   the mathlib cache, Lake's output. A withdraw that breaks the rules, an
   `exclude` entry that names no approve record, and a record in two
   directories stop every command but `validate`, which lists them. `export`
   builds exactly the libraries it exports.
3. **Records name declarations by id**
   (`leanblame.record.2`), so an approval follows a rename: the declaration is
   `outdated`, not `unsigned`. A new id is a new declaration: the old approvals
   stay with the old id.

### Diff in LeanBlame (owner, 2026-10-27: "Proceed. Do the efficient clean way")

LeanBlame is to OpenVouch what git is to a code host: the semantic diff is LeanBlame's, as `git diff`
is git's; the service displays it. `status` compares each declaration with its last live approval;
`diff` compares two points the caller picks (approve records, or the last export), with the same
comparison (`Walk.compare`): each part of the claim, by hash, so a difference is one the kernel sees,
not a change of the printer. It reads the stored graphs and never hashes; a declaration whose claim did
not move is not walked.
