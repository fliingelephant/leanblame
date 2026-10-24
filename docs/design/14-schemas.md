# 14. Schemas

The four interfaces LeanBlame commits to. TOML for what humans read in git
(records, config); JSON for what machines pass around. Hashes are `sha256:`
plus 64 lowercase hex digits. Dates are UTC: native datetimes in TOML, ISO 8601
strings in JSON.

## 1. Boundary list (JSON)

Produced by `export` from `@[trusted]`, including tags found in imported
libraries, or from `--boundary FILE`, a verso-blueprint manifest or a manual
TOML list ([04-architecture.md](04-architecture.md), Adapters). Read by
`status`, from the object store.

```json
{
  "schema": "leanblame.boundary.2",
  "library": "OpenPhysics",
  "commit": "9f8e7d…",
  "toolchain": "v4.35.0",
  "deps": { "mathlib": "a1b2c3…", "physlib": "d4e5f6…" },
  "declarations": [
    {
      "name": "OpenPhysics.Ising.Hamiltonian",
      "module": "OpenPhysics.Ising",
      "kind": "def",
      "role": "defined",
      "informal": "Nearest-neighbour Ising Hamiltonian on a finite chain, H = -J Σ σᵢσᵢ₊₁, open boundary.",
      "informal_source": "docstring"
    }
  ]
}
```

| Field | Meaning |
|-------|---------|
| `name` | fully qualified constant name, after structure expansion |
| `kind` | the proof assistant's own label, non-empty, never interpreted. Lean: `def`, `theorem`, `axiom`, `inductive`, `ctor`, `opaque`, `quot`, `rec` (`rec` is never on the list). A definition the export marks partial would be labelled `partial def`; Lean 4.35 exports them as `opaque` |
| `role` | `assumed` (no body; the statement is taken as true), `defined` (the body is the meaning), `proved` (the body is a proof) |
| `informal` | the text the signer relies on; required |
| `informal_source` | `docstring`, `blueprint:<label>`, or `manual` |

## 2. Record (storage, TOML)

One file per signoff in `records/`. Filename = sha256 of the file bytes.

| Field | Approve | Withdraw | Meaning |
|-------|---------|----------|---------|
| `schema` | ✓ | ✓ | `leanblame.record.1` |
| `action` | ✓ | ✓ | `approve` or `withdraw` |
| `signer` | ✓ | ✓ | `provider:id`, stable id |
| `date` | ✓ | ✓ | TOML datetime, UTC |
| `constants` | ✓ | optional | approve: table name → claim hash; withdraw: list of names, default all |
| `module` | ✓ | | Lean module name |
| `commit` | ✓ | | library commit |
| `toolchain` | ✓ | | Lean version |
| `deps` | ✓ | | inline table of dependency commits |
| `export` | ✓ | | hash of the export the signer saw |
| `boundary` | ✓ | | hash of the boundary list the signer saw |
| `evidence` | optional | | hash of an `equiv` proof relied on |
| `refers_to` | | ✓ | hash of the approve record withdrawn |
| `note` | optional | optional | free text |

Validity rules: `refers_to` names an approve record; withdraw `signer` equals
that record's signer; existing files are never modified or deleted.
Examples in [05-records.md](05-records.md).

## 3. Release manifest (output of `release`, JSON)

```json
{
  "schema": "leanblame.release.1",
  "library": "OpenPhysics",
  "tag": "2027.04",
  "commit": "9f8e7d…",
  "toolchain": "v4.35.0",
  "deps": { "mathlib": "a1b2c3…", "physlib": "d4e5f6…" },
  "export": "sha256:…",
  "boundary": "sha256:…",
  "records": ["sha256:…", "sha256:…"],
  "kernel": { "checker": "leanchecker", "version": "v4.35.0", "passed": true },
  "theorems": {
    "OpenPhysics.Ising.groundEnergy_le": { "status": "proven", "axioms": ["Classical.choice", "propext"] },
    "OpenPhysics.Ising.gap_conjecture":  { "status": "open", "axioms": ["sorryAx"] },
    "OpenPhysics.Ising.uses_postulate":  { "status": "proven", "axioms": ["OpenPhysics.Conventions.locality"] }
  },
  "counts": { "proven": 2, "open": 1 }
}
```

`records` lists every record that makes a tagged declaration valid at this
commit. `theorems` lists the tagged declarations with role `proved`. `release` fails on an invalid signoff, a kernel error, or an axiom that
is neither standard nor a tagged, signed axiom.

## 4. Status (output of `status --json`)

The complete truth, one entry per tagged declaration. Viewers filter; they
never need another source.

```json
{
  "schema": "leanblame.status.2",
  "library": "OpenPhysics",
  "commit": "9f8e7d…",
  "export": "sha256:…",
  "generated": "2026-10-23T15:00:00Z",
  "declarations": {
    "OpenPhysics.Ising.groundEnergy_le": {
      "module": "OpenPhysics.Ising",
      "kind": "theorem",
      "role": "proved",
      "informal": "…",
      "informal_source": "docstring",
      "claim": "sha256:77c0…",
      "state": "outdated",
      "change": [{ "cause": "untagged", "names": ["Mathlib.Finset.sum"] }],
      "signers": [],
      "history": [
        { "record": "sha256:…", "action": "approve", "signer": "openreview:~Jane_Doe1", "date": "2026-10-23T14:02:11Z", "claim": "sha256:3b1f…", "note": "…" }
      ],
      "blocked_by": [],
      "proof": { "status": "proven", "axioms": ["propext"] },
      "evidence": "sha256:…",
      "tagged_deps": ["OpenPhysics.Ising.Hamiltonian"],
      "closure_size": 3412
    }
  }
}
```

| Field | Values |
|-------|--------|
| `kind`, `role` | as in the boundary list |
| `state` | `valid` (enough live approvals carry `claim`), `outdated` (live approvals exist, not enough carry `claim`), `unsigned` (none) |
| `change` | causes since the last live approval: `own-text`, `own-body`, `dep-spec`, `cut-moved`, `untagged`, each with the names involved; empty when valid |
| `signers` | live approve records matching `claim` |
| `history` | every record that ever touched this declaration |
| `blocked_by` | tagged dependencies whose state is not `valid`, recursively |
| `proof` | role `proved`: `proven` (every axiom standard, or tagged, `assumed` and valid), `open` (`sorryAx` or another axiom); `n/a` otherwise; with all axioms |
| `evidence` | hash of an `equiv` proof that the current hash means what the last live approval meant, if any; `history` shows withdrawals |
| `closure_size` | constants hashed into `claim`, proofs excluded |
