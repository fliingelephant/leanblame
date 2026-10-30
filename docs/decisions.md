# Decisions

How LeanBlame is built, and why. The trust model it implements: [trust-model.md](../trust-model.md).
Formats: [schemas.md](schemas.md). Commands: the [README](../README.md).

## Architecture

### Who owns what

| Part | Owns | Contains no |
|------|------|-------------|
| `leanblame` | the CLI (a Lean package) and its schemas | field content, service code |
| a library | its Lean code, `records/`, `leanblame.toml` | LeanBlame code |
| a service (first: OpenVouch) | pages, logins, writing records; it calls the CLI | validity rules |

LeanBlame knows nothing about any service.

### The CLI

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

Eleven commands; the [README](../README.md) lists them.

### Export, checker, comparator

Lean's toolchain ships `leanexport`, which writes every constant of an
environment (types, values, universe levels) to one text file, and
`leanchecker`, which replays such a file through the Lean kernel. LeanBlame
hashes from the export and gates releases and `equiv` proofs with the checker.

`lake comparator` (Lean FRO, in core since v4.35.0) builds on the same two
tools: it compares an untrusted solution against a trusted statement file,
walking the dependency closure of each target theorem. LeanBlame copies its
closure walk and changes it (cut at tagged declarations, skip proofs, collect
every mismatch). Comparator itself is not run: what it cannot check, the Lean
reference manual says explicitly, is that the trusted file means what you
intended, and that is the one thing LeanBlame records.

### Blueprints

`export --boundary FILE` reads verso-blueprint's `blueprint-manifest.json`
instead of `@[trusted]`: statement entries name their Lean declarations in
`codeData`, the text comes from the `statement` slot of `externalMarkup` or else
the entry's fragment in `blueprint-html-cache.json`. A label is the id of the
first declaration it names; its other declarations name that one as `parent`,
and their ids are the label and their names (`def:point/norm`). A name claimed
by two labels, a statement entry without label or text, and a value of an
unexpected type are errors.

### Challenges

A comparator challenge must not depend on the library it comes from: it carries
what its theorems need, and nothing else. `export` finds that in the one
environment it imports, and takes it from the library's source as a piece
graph: a piece is text in a file of a challenge, its links are the pieces it
needs. Nothing is elaborated again. The challenge of chosen tagged declarations is
the theorems' statements and the other declarations' commands, what those need,
what that needs, and so on: a cut of the graph.
What several theorems need is there once.

- A piece is mostly a command, from its first token (the docstring) to its end,
  as written. The others: the lakefile, the toolchain, an `import`, a
  `namespace N` `end N` that an `open` needs, a module's `section` and its
  `end`, and an `end` for a scope the module leaves open.
- A declaration needs the commands that declare the constants in its kernel
  terms (the type; the value or proof) and those its source names (the
  `.ilean`, as for "find references"), and the instances of its module, since
  Lean uses them without naming them. An `attribute` command is split by the
  names it gives the attribute to: each part comes with the declaration it
  names, or, for a constant from outside the library, with its module.
- A command needs its scope: the `namespace` and `section` commands around it
  with their `end`s and, unless it opens or closes a scope, the `open`,
  `variable`, `universe` and `set_option` commands before it in that scope; a
  command that opens or closes several scopes (`namespace A.B`) is needed for
  each. A command needs its module's `section`, which first sets the Lean
  options Lake builds the module with (its `leanOptions` and the `-D` options of
  `moreLeanArgs` and `weakLeanArgs`, as `lean` reads them) and needs what the
  module imports from outside the library; nothing one module opens or sets
  reaches the next. Lean refuses an `open` of a namespace that does not exist
  yet: one that no module from outside the library imported by its module makes
  is declared first (`namespace N` `end N`); declaring one that exists changes
  nothing.
- A tagged theorem's statement is a piece of `Challenge.lean`: its command with
  the proof `sorry`. It needs what the statement uses, copies of the scope
  commands around it, and `import ChallengeDeps`.
- Module-system words (`module`, `public`, `meta`, `@[expose]`) and
  `@[trusted]` go. A name that would read differently in one file with the other
  modules is written as Lean writes it (`unresolveNameGlobal`): a name the
  `.ilean` says refers to a constant, which in the library's whole environment,
  with the command's namespace and `open`s, reads as other constants too or
  instead. A challenge holds some of those constants, so a name that reads as
  its constant alone, or as none (a local), reads the same there. Lean names a
  private declaration after its module: one whose name a declaration of another
  module in the graph has too is written with its module
  (`«secret (Sample.Energy)»`), and so is every name that refers to it.
- What stops a challenge stops `challenge`, not `export`, which sign-offs need:
  a piece holds its problem (a declaration no command declares; a module whose
  source does not read; a Lean option the library itself declares, which a
  challenge file cannot set; a package the library requires by path), and a cut
  that holds such a piece cannot be made. A challenge cannot state a theorem
  whose proof its other theorems need.
- `challenge X... --out DIR` writes the cut of the named tagged declarations.
  `lakefile.toml` requires what the library's lakefile requires, by git
  (LeanBlame left out), and sets no Lean options: each module's section does.
  `lean-toolchain` is the library's. `ChallengeDeps.lean` holds the imports, the
  declared namespaces, then each module's part, in import order.
  `Challenge.lean` imports it and holds each module's scope copies with the
  statements, proofs `sorry`. `challenge --graph` prints the graph
  ([schemas.md](schemas.md) §6), so that a service cuts challenges itself.
- `challenge --check DIR` builds the challenge with `lean` against the
  library's build, imports it and hashes its own declarations as `export`
  hashes the library, in memory; what it imports from outside the library is
  the library's build, so those declarations keep the last export's hashes.
  Each tagged declaration it holds must have the claim hash of the last export,
  or the kernel must find it definitionally equal to the library's: the
  challenge then means what the signers signed, and a solution of it proves the
  library's theorem. Lean can write the same source as other terms in one file
  (a `match` shares the helper Lean made for another module's); the kernel
  decides as `equiv` does, against the library's versions of what differs, read
  from the compiled files of the modules that declare them. A private name holds
  the module it is written in, so the challenge's private constants are hashed
  under the library's names: by their names, or by the module a name written
  with its module gives.

### Config: `leanblame.toml`

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

### Storage

- Code, records, config: git.
- Exports, boundary lists, graphs, piece graphs, `equiv` proofs, release manifests: an
  object store keyed by hash, one directory per kind
  (`.leanblame/store/<kind>/`). A graph is an export hashed against a boundary
  list: every claim hash, with the parts `status` compares and the axiom
  report. `export` writes it; the other commands read it and never hash. It is
  the one kind keyed by what it was computed from instead of its own bytes:
  `graphs/<export>-<boundary list>.json`, both by their hashes; a graph that is
  not complete is an error. `.leanblame/current` points at the last export and
  its piece graph, with the commit, toolchain and dependencies it was made from.
  `export` deletes what nothing names any more: exports and boundary lists named
  by no record and not current, the graphs of deleted exports, a piece graph that
  is not current, evidence whose claim is no longer current, proofs named by
  no evidence and no record. Validity compares the records' claims with the graph
  of the current code, which whoever judges makes with `export`. Graphs of old
  exports only explain causes and show diffs; they never change a state.
- `equiv` evidence: `.leanblame/equiv/evidence/<claim>.json`, one file per claim
  hash, naming the declaration's id, the proof and the record it was compared
  with. Every JSON file here is read strictly.

### Platform

`export`, `equiv` and `release` run wherever the library's toolchain is
installed: `export` builds the library (`lake build`), runs the exporter
in-process and hashes; `release` and `equiv` run `leanchecker`. `status`,
`blame`, `sign` and `validate` need no toolchain: they read graphs from the
object store, and records.

### Reuse

| Used as is | Copied and changed | New |
|------------|--------------------|-----|
| `leanexport` and its parser, `leanchecker`, Lake's TOML reader and git helpers, mathlib cache, git | comparator's closure walk; core's `Replay.lean` | claim hash, cause analysis, records and validator, `status`/`blame`/`diff`/`release`, `Old.` reconstruction, the piece graph |

No forks, no glue scripts: LeanBlame reads Lean's own data (kernel terms, parsed syntax, `.ilean`
files, oleans), from the kernel's point of view.
Rejected: forking the archived comparator (it lacks `--from-export`), running `lake comparator`
on `equiv`'s proofs (the kernel has already checked them in-process; `leanchecker` replays the
stored export), comparator-live (no role in the data flow), verso-blueprint (see "`status --json`
is the output").

### Data flow

```
author tags declarations
  -> cli export
  -> a reviewer reads the declaration (in a service's page, or the terminal)
  -> a record is written (cli sign), validated and committed
  -> cli status --json -> any viewer
```

On change, `status` reports state and causes, `diff` shows what changed, and
`equiv` may add evidence; who acts is the table in [the trust model](../trust-model.md), "What happens on change".

### Formats

Boundary list, record, release manifest, `status --json`, `diff --json`, piece graph: TOML
for what people read in git (records, config), JSON for what programs read. Exact fields in
[schemas.md](schemas.md).

### Language

Lean. The CLI reuses the toolchain's export parser, kernel and Lake; another
language would need a second export parser.

### Beyond Lean

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

## Releases

### Stable and dev

- **`main`**: grows every day.
- **Release tag**, e.g. `2027.04`, patches `2027.04.1`: a frozen snapshot,
  fully signed and kernel-checked.

Development never stops for a release.

### What `release` does

Two gates, then a report.

1. **Signoff gate.** Every tagged declaration is `valid`. Fails otherwise.
2. **Kernel gate.** `leanchecker --from-export` replays the whole export. Fails
   on a kernel error.
3. **Axiom report.** From the export, per theorem, the axioms it rests on:
   - only permitted axioms, that is the three standard ones and tagged, signed
     `axiom`s: **proven**, each axiom listed;
   - includes `sorryAx`: **open**;
   - anything else: **fail**. No axiom config.

Not `lake check`: it hard-codes the three standard axioms and fails on `sorry`, so it
cannot serve a library with open theorems or signed axioms.

`release` never fails on open theorems. It reports how many are proven and
how many are open, by name. A reader who wants only proven results filters the
manifest. Whether a declaration claims a theorem or a conjecture is in its
informal text, which its signer signed.

Manifest fields in [schemas.md](schemas.md) §3. The axiom report is bound
to the export hash it was computed on; `export` computes it, `release` replays
the kernel. `status` shows it per theorem and warns about an axiom that is
neither standard nor tagged and signed.

**Patch releases**: fixes to existing declarations, dependency bumps whose
changes were re-approved. A withdrawal makes a release impossible until the
declaration is approved again or removed.

**Downstream** pins a release. Mathlib tags one commit per Lean release but has
no version scheme of its own; a LeanBlame release is what gives users
something stable to cite.

### Evaluation on fresh results

Question: how good is the library at expressing new results in its field?

1. Freeze release `R`.
2. For six months, every new paper in scope is a test item. Formalize its main
   result using `R` only.
3. Record, per item:

   | Metric | Why |
   |--------|-----|
   | New declarations needed | Zero is perfect. The missing ones are the to-add list. |
   | Size of what the reviewer must read | Smaller means better abstractions. |
   | Closure size, proofs excluded | `status` reports it. |
   | Review minutes | Actual human time to sign. The real objective. |
   | Later withdrawals | Did the library prevent mis-formalization? |
   | Signoff survival | How many signoffs stayed valid across upstream bumps. |

4. After six months, the declarations added to `main` are the answer to "what
   was missing." Tag `R+1`.

Fresh papers cannot have influenced `R`. The test is rolling and never runs
out. The clock starts at the first fully signed
release.

## Why, and what was rejected

Each entry: the decision, the reason, what was rejected.

### Why a claim hash and not `git blame` on the file

Git hashes text. Meaning changes with zero text change when an upstream
definition moves. And an upstream change has no diff in your repo. Git is the
storage; the claim hash is the identity.

### The boundary list is the input

Declarations plus informal text, from `@[trusted "id"]` or a verso-blueprint
manifest. Keeps LeanBlame independent of how a project plans or displays its
work: a blueprint project can sign statements before they are proved. An id is
how a declaration is cited and followed: from a blueprint,
a label is the id of the first declaration it names, the parent of the others.
Rejected: a hand-written list, which has no ids.

### `status --json` is the output

It carries everything a viewer shows, so no viewer computes it again.
Rejected: building on verso-blueprint, which would force every library to
author Verso documents.

### One record type, no delta records

`action = approve | withdraw`. Not now: richer kinds and cargo-vet-style
delta records, harder to explain than useful. The signer approves the new
hash; `equiv` evidence is attached as information.

### No merge or rebase

Approvals accumulate; they never conflict. Two edits of a declaration are two
hashes. `status` says what needs re-approval.

### Delta replay deferred

Sound by weakening, same as `import`. Needs a read-only hash-pinned base and a
pinned kernel version. Add only if throughput forces it.

### Distributed storage, no distributed build

Records in the library's git, exports in an object store, any viewer. Remote
records repositories (an institution's, with trust imports and exclusions) may come later.
Mathlib's cache and Reservoir already work this way.

### Names

**LeanBlame**: the infrastructure. Says what it does; fits LeanDojo,
LeanSearch, LeanCopilot. Rejected:
OpenBlame (physicists parse "blame" better next to "Lean"), leanit (says
nothing).

### Declaration ids

An id is written by `leanblame id`, never by `export`: a build on a server would make a new one
each time. A cite is `id@record`, as the record fixes the commit, the Lean version and the
dependency commits. Not the commit alone (it moves when anything changes) and not the claim (it
stops at signed dependencies). A field's id is its structure's id and its name, so a rename of the
structure keeps the field's history.

### Tags written after the fact

`attribute [trusted "id"] Name` tags a declaration of any module, also of a library
one does not own (a fork with a library of tags; OpenVouch `docs/decisions.md` §8).
One mechanism: Lean writes every attribute both ways, `@[simp]` and `attribute
[simp]`. Lean's parametric attributes refuse declarations of imported modules, so
`trusted` keeps its own store: each tag with its id and where `trusted` ends in the
module that wrote it, where `leanblame id` writes the id, for both forms. A
declaration has one tag; a second, also from another module, is an error. A tag on
a deprecated alias whose value is another constant (a rename, `@[deprecated] alias
old := new`) is on that constant, with a warning to write its name; the id stays.
A deprecated declaration with a value of its own is not a rename. A rename without
an alias is Lean's unknown-constant error at the tag. Blueprints and Mathlib users
follow renames the same way; only tags in the author's code are cleaner.

### Fail out loud

An unexpected state is an
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

### Root causes

1. **Viewers compute nothing.** `status --json` carries what LeanBlame knows:
   the record files, the standing of approvals, the toolchain, the standard
   axioms. A viewer only displays it.
2. **No defaults on errors.** Every JSON file is read strictly:
   a missing or an unknown key is an error. Every `leanblame.toml` key is
   required. No fallback on a failure: proof erasure, the statement printer,
   the mathlib cache, Lake's output. A withdraw that breaks the rules, an
   `exclude` entry that names no approve record, and a record in two
   directories stop every command but `validate`, which lists them. `export`
   builds exactly the libraries it is run on.
3. **Records name declarations by id**, so an approval follows a rename: the declaration is
   `outdated`, not `unsigned`. A new id is a new declaration: the old approvals
   stay with the old id.

### Diff in LeanBlame

The semantic diff is LeanBlame's; a service displays it. `status` compares each declaration with its last live approval;
`diff` compares two points the caller picks (approve records, or the last export), with the same
comparison (`Walk.compare`): each part of the claim, by hash, so a difference is one the kernel sees,
not a change of the printer. It reads the stored graphs and never hashes; a declaration whose claim did
not move is not walked.

### One environment, challenges from the source

`export` imports the library once, with the environment extensions of everything it imports, as an
editor or doc-gen4 loads it, and makes every output from that environment: the export, the
statements (printed in-process, as doc-gen4 prints them) and the piece graph. A challenge is
not a copy of each module elaborated again in other `lean` processes: it is the commands of the
library's source that its theorems need, found from the kernel terms and the `.ilean`, with their
scope. The pieces are a graph whose links are what each piece needs; the challenge of chosen
theorems is the cut from their statements: one `ChallengeDeps.lean` (one file, not one per module)
with what they need and nothing else, and `Challenge.lean`. `leanblame challenge` cuts it; `challenge --graph` gives a service the graph, to
cut challenges live. Names are rewritten only where they would read differently in that file. Lake's own loader
gives the libraries, their modules and their Lean options. `challenge --check` hashes the challenge
with the claim hash, the rule a sign-off follows, so that "the challenge means what the library
means" is the same question as "the claim did not move". What stops a challenge stops `challenge`,
not `export`: sign-offs do not wait on challenges. In the one file, each module's section sets the
Lean options Lake builds that module with, and a private name that another module's declaration in
the graph has too is written with its module.
Rejected: copying every module (416 `lean` processes for Lean-QIT, about 1.6 GB each), one challenge file per module, comparing a challenge with its
own hash of terms, hashing the names Lean makes up (a shared `match` helper) by their content
instead of letting the kernel decide, and one `ChallengeDeps.lean` shared by every challenge
(6,989 lines for any Lean-QIT challenge).

## Prior art

### Lean ecosystem

| Project | Has | Lacks for us |
|---------|-----|--------------|
| **comparator** / `lake comparator` (Lean FRO) | Trusted/untrusted split, closure comparison, axiom check, kernel and external replay, compare from exports | Any notion of a person; stops at first mismatch; compares proofs |
| **comparator-live** | Web UI for comparator; trusted challenges identified by `sha256(text.trimRight() + "\n")` | Signer identity; hashes text, not meaning |
| **lean-eval** | `@[eval_problem]`; one TOML per problem with `submitter`, `status`, `statement_revision`; append-only revision history with a sha256 digest | It is a benchmark; the "signer" is the submitter |
| **lean-eval-submissions** | Append-only results per GitHub login, exact commit binding | GitHub-only identity |
| **verso-blueprint** (Lean FRO) | Prose, Lean declarations and dependency graph in one document; `@[blueprint]`; `blueprint-manifest.json` with labels, statuses, ownership; custom clients documented (the repo notes the manifest is not yet a stable interface) | Signoff, hash binding. A natural consumer of `status --json`. |
| **LeanArchitect** (Hanwen Zhu) | `@[blueprint]` generating blueprint nodes from Lean declarations, for the Python leanblueprint; used by PNT+ and infinity-cosmos | Review, hashes. Precedent for `@[trusted]`. |
| **leaff** (alexjbest) | Diff of two Lean environments: all added, removed, renamed, changed declarations | Closure walk, hash binding |
| **doc-gen4** | Per-declaration HTML with docstrings for any Lake package | Nothing |
| **Mathlib review** | Reviewer plus maintainer merge is an implicit attestation | Record is only GitHub history |
| **formal-conjectures** (Google DeepMind) | Registry of formal statements of open conjectures; version bump when a misformalization is fixed | Named signer per statement, hash binding |
| **hex** libraries (Lean FRO) | Mathlib-free executable definitions plus separate `-theory` correspondence packages | Not review; the slim-dependency pattern reduces cascades |

Also: nanoda, con-ron and con-leche, independent re-implementations of the Lean kernel, usable as
extra checkers; AXLE, Kimina and Pantograph, fast proof-check services that trust the elaborator:
filters, not gates. lean-eval's per-problem TOML files were the model for records.

### Other proof assistants

- **Isabelle Archive of Formal Proofs.** Organized like a journal. Anonymous
  referees chosen by named editors. Rules: no `sorry`, `back`, `sledgehammer`
  or `smt_oracle`; must build. Named maintainer per entry: "If accepted, you
  must agree to maintain your archive entry or nominate someone else." Kept
  building against each Isabelle release; old versions stay available. Public
  maintainer for buildability, anonymous reviewer for content: the opposite of
  LeanBlame on the review side.
- **Formal Abstracts** (Thomas Hales, ~2018). Registry of formal statements
  from papers. Stalled. From memory, not verified.

### Other fields

| System | Unit of signoff | Change handling | Blame |
|--------|-----------------|-----------------|-------|
| **cargo-vet** | One crate version, or a delta `a -> b`, per criterion | Trusted if a chain of audits reaches this version | Reputational; audits imported from other orgs by URL and locked; exclusions |
| **Gerrit**, **Linux kernel** | Patch vote; `Reviewed-by` | Votes survive only listed change kinds; else "outdated" | `Reviewed-by` disclaims warranty |
| **OWNERS** files | Directory change | Owners keep deps current | Two named owners per dependency |
| **Sigstore**, **Go sumdb**, **Certificate Transparency** | Signature over a digest | Append-only Merkle log | Monitors |
| **Professional Engineer seal** | One drawing sheet | Reviser seals changed sheets and explains; old seals stay | Personal license |
| **FAA DER**, **NRC 10 CFR 50.59** | Compliance finding; design change | Change-impact analysis scopes re-verification | Designation revocable |
| **PCAOB Form AP**, **SOX 302** | Audit report | Refiling | Partner id never reused |
| **IETF** | RFC | Never changes; `Updates`/`Obsoletes` | Reputational |
| **Crossmark**, **Zenodo**, **Registered Reports** | Article version; protocol | Typed update links; one DOI per version; protocol accepted before results | Public retractions |

What LeanBlame adds: a named human bound to a kernel-level claim hash. The
hash cuts at signed dependencies. It is tracked across upstream versions.
Reviewers do not need GitHub.
