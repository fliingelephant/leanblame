# 11. Decisions

Each entry: the decision, the reason, what was rejected. All 2026-10-23.

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

Everything that changes meaning, nothing else. In: kind, name, universe
parameters, type and body with proof subterms erased, safety, informal text of
tagged declarations. Out: proofs (wherever they occur: proof irrelevance),
binder names, implicitness, kernel hints, recursor rules. Cycles hashed as groups. `unsafe` cannot be tagged.

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

Declarations plus informal text, from any source. `@[trusted]` is one
generator; a blueprint manifest is another. Keeps LeanBlame independent of how
a project plans or displays its work.

### `status --json` is the output

Any page can read it. Our page is doc-gen4 plus this overlay. Rejected:
building on verso-blueprint, which would force every library to author Verso
documents.

### One record type, no delta records

`action = approve | withdraw`. Richer kinds and cargo-vet-style delta records
were tried and dropped as harder to explain than useful. Can be added later.

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

It never reaches the kernel. Conventions are declarations. The sign server
shows types with notation off.

### Formats and commands

TOML for records and config, JSON for machine output. Eight commands: `init`,
`export`, `status`, `blame`, `equiv`, `sign`, `validate`, `release`.

### No forks

Copy one Apache-2.0 file (comparator's closure walk). Use `leanexport`,
`leanchecker`, Lake's TOML reader, doc-gen4 as is. Rejected: forking the
archived comparator (it lacks `--from-export`), running `lake comparator` on
`equiv`'s proofs (the kernel has already checked them in-process; `leanchecker`
replays the stored export), comparator-live (no role in the data flow),
verso-blueprint (see above).

### Lean CLI, TypeScript web

The CLI reuses the toolchain's export parser and data types. Rust would need a
second parser or an orchestration-only binary. TypeScript matches
comparator-live.

### Delta replay deferred

Sound by weakening, same as `import`. Needs a read-only hash-pinned base and a
pinned kernel version. Add only if throughput forces it.

### Distributed storage, no distributed build

Records repos per institution, exports in an object store, one stateless page.
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

Per library, in `leanblame.toml`: `allowed_signers` (any, a list, or a repo)
and `required_signers` (default 1). Pure rule over records, no Lean in it.
Reviewer assignment is a web queue and never affects validity.
