# 11. Decisions

Each entry: the decision, the reason, what was rejected. All 2026-10-23.

### What a signature covers

Your own declaration fully; for tagged declarations you use, only name, type
and informal text; for untagged ones, everything underneath; proofs never.
Full text: [03-trust-model.md](03-trust-model.md). Rejected: full-closure hash
(re-sign on body changes you never read); names-only (not told when the
informal text changes meaning).

### Humans never read proofs

The kernel checks them. Human reading adds nothing and costs the scarcest
resource.

### Agents inform, never decide

`equiv` marks a declaration equiv-proven. The reviewer clicks. Any other agent
check (vacuity, triviality, back-translation) may be shown as information,
never as a decision. Infrastructure for the signer is therefore plain: good
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

### Proof gate

`release` runs `lake check --paranoid` with the permitted axioms and records
proven/open per theorem. Needed because proofs are outside the hash by design.

### `equiv` rebuilds old meaning from the old export

Never from old source, which re-elaborates against new mathlib and makes
`old = new` trivially true.

### No forks

Copy one Apache-2.0 file (comparator's closure walk) and lean-eval's attribute
code. Use `leanexport`, `lake check`, `lake comparator`, doc-gen4 as is.
Rejected: forking the archived comparator (it lacks `--from-export`),
comparator-live (no role in the data flow), verso-blueprint (see above).

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

### Open policy questions

- Who may sign: anyone with an account, or institution-vouched only?
- Quorum: one signer now; the format allows more.
