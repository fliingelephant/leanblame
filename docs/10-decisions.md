# 10. Decisions and FAQ

Each entry records a decision made during design and the reason. Dates are
2026-10-23 unless noted.

### Why not just `git blame` on the Lean file?

Git hashes text. Meaning can change with zero text change, when mathlib moves
under you. And a "change is OK" judgement about an upstream change has no diff
in your repo at all. So records point at the export hash, and git is only the
storage.

### Why do humans never read proofs?

The kernel checks them. Human reading adds nothing and costs the scarcest
resource. Comparator's Challenge/Solution split already removes proofs from the
file the human reads.

### Can agent checks replace the human reading the boundary?

No. Agents can run endless checks: vacuity, triviality, back-translation,
mutation tests, debates. None of them is a human reading the definition and
confirming it matches intent. LeanBlame records the reading. Infrastructure for
the signer is therefore plain: good pretty-printing, hover to unfold, show who
signed each import, prose next to Lean. Nothing clever. Agent output may be
displayed as information, never as a decision.

### Why is "proven equivalent" not an automatic carry-over?

Because agents must not decide for the reviewer. `equiv` marks the constant
equiv-proven. The reviewer clicks. One click, but a human click.

### Why one record type (approve / withdraw) and no delta records?

We tried richer kinds and delta records. They were harder to explain than the
value they added. The format can grow later without breaking old records.

### Do we need merge or rebase semantics?

No. Approvals do not conflict; they accumulate. Two different edits of a
definition are two versions; combining them is a third version, reviewed as
new. The export hash of the closure decides whether anything needs re-review.
Comparator computes it.

### Who is blamed when two independently signed changes clash in a later module?

Nobody is retroactively blamed. The later module's signer owns that module.
To give the clash itself an owner, we adopt: the later signer owns
compatibility with the shared conventions file. Feasible only when conventions
are written in one signed file.

### Is delta replay sound?

Yes, by weakening: checking a declaration depends only on the declarations it
uses, so a base verified once can be reused. It is how `import` works. The base
must be read-only, hash-pinned, and tied to a kernel version. Deferred until
volume requires it.

### Distributed build?

No. Distributed storage (records repos, export files), central stateless page.
This is how Lean already works: mathlib cache, Reservoir, GitHub repos.

### Why two repos, generic vs specific?

So any field can adopt LeanBlame without pulling physics, and OpenPhysics never
carries auth or page code. The alternative split (records vs tools) was
rejected because the tools are one small CLI around comparator.

### Why not build on lean4export directly?

Comparator already builds on lean4export and already does the closure
comparison we need, with `--challenge-from-export`. Do not invent a second
notion of "same declaration".

### Why not AXLE-style fast checking as the gate?

It trusts the elaborator and can accept an unsound declaration. Filter only.

### Names

- **LeanBlame**: the infrastructure. Unused name; fits LeanDojo, LeanSearch,
  LeanCopilot. "Blame" may read as punitive to non-developers; test on two
  physicists.
- **OpenPhysics**: the first library. Not physics-specific infra, so the infra
  is not called OpenPhysics.
- **OpenBlame** was considered; dropped for LeanBlame because physicists will
  parse "blame" better next to "Lean" than next to "Open".

### Why three parts and six commands, not five layers?

A first draft had five layers: attribute, evidence CLI, records, index, web.
The attribute is one Lean file inside the CLI package. The index is
`status --json`. `diff A B` is `status --base A`. `bridge` was renamed `equiv`
because it says what it does: try to prove old and new equivalent. Result:
`cli`, `records`, `web`; `export`, `status`, `blame`, `equiv`, `sign`,
`release`.

### Why no `rebase` or `merge` command?

Nothing is replayed. `status` lists what needs re-approval; the reviewer
approves. See the merge/rebase entry above.

### Why fork and pin instead of upstream PRs?

Speed and control while the design is unproven. Four forks: comparator
(archived standalone, so no lean4 fork), comparator-live, verso-blueprint, and
a copy of lean-eval's attribute and generator. Upstream later.

### Why Lean for the CLI, not Rust?

The CLI can import comparator's `Export.Parse` and `Compare` directly, so
"same declaration" has one definition. Rust would need a second export parser
or an orchestration-only binary. TypeScript for the web, matching
comparator-live.

### Why verso-blueprint for the page?

It already emits `blueprint-manifest.json` with labels, statuses, dependency
graph and Lean declaration links, and documents "dashboard, audit view" as a
supported custom client. We overlay signoff status per node. LeanArchitect is
a precedent for declaration attributes but targets the older Python
leanblueprint; not a dependency.

### Identity

Any OpenID Connect or OAuth provider: OpenReview, ORCID, GitHub, local for
dev. Store `provider:id`. Cryptographic signing parked.

### Granularity

Unit is the declaration. Default record covers one module file. Open: whether
to default to per-definition records for high-value definitions.

### Open policy questions

- Who may sign: anyone with an account, or institution-vouched only?
- Quorum: one signer now; format allows more.
- Statements-only comparator mode: patch in our pinned fork now; upstream later.
