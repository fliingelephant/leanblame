# 14. Schemas

The four interfaces LeanBlame commits to. Everything else may change.
All files are TOML or JSON, UTF-8, keys as written here. Hashes are
`sha256:` plus 64 lowercase hex digits. Dates are ISO 8601 in UTC.

## 1. Boundary list (input)

Produced by `cli export` from `@[trusted]`, or by an adapter. JSON.

```json
{
  "schema": "leanblame.boundary.1",
  "library": "OpenPhysics",
  "commit": "9f8e7d…",
  "toolchain": "v4.35.0",
  "deps": { "mathlib": "a1b2c3…", "physlib": "d4e5f6…" },
  "declarations": [
    {
      "name": "OpenPhysics.Ising.Hamiltonian",
      "module": "OpenPhysics.Ising",
      "kind": "def",
      "informal": "Nearest-neighbour Ising Hamiltonian on a finite chain, H = -J Σ σᵢσᵢ₊₁, open boundary.",
      "informal_source": "docstring"
    }
  ]
}
```

| Field | Meaning |
|-------|---------|
| `name` | fully qualified constant name; a `structure` lists only itself, expansion is automatic |
| `kind` | `def`, `theorem`, `axiom`, `structure`, `inductive`, `instance`, `opaque` |
| `informal` | the text the signer relies on |
| `informal_source` | `docstring`, `blueprint:<label>`, or `manual` |

## 2. Record (storage)

One TOML file per signoff in `records/`. Filename = sha256 of the file bytes.

| Field | Approve | Withdraw | Meaning |
|-------|---------|----------|---------|
| `schema` | ✓ | ✓ | `leanblame.record.1` |
| `action` | ✓ | ✓ | `approve` or `withdraw` |
| `signer` | ✓ | ✓ | `provider:id`, stable id |
| `date` | ✓ | ✓ | |
| `constants` | ✓ | | table: name → claim hash |
| `module` | ✓ | | Lean module name |
| `commit` | ✓ | | library commit |
| `toolchain` | ✓ | | Lean version |
| `deps` | ✓ | | inline table of dependency commits |
| `evidence` | optional | | hash of an `equiv` proof relied on |
| `refers_to` | | ✓ | hash of the record withdrawn |
| `note` | optional | optional | free text |

Examples in [05-records.md](05-records.md).

## 3. Release manifest (output of `release`)

JSON, one per tag.

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
  "theorems": {
    "OpenPhysics.Ising.groundEnergy_le": { "status": "proven", "axioms": ["propext", "Classical.choice"] },
    "OpenPhysics.Ising.gap_conjecture":  { "status": "open" }
  },
  "check": { "tool": "lake check --paranoid", "passed": true }
}
```

`records` lists every record that makes a tagged declaration valid at this
commit. `release` fails if any tagged declaration is not valid, if `check`
fails, or if a theorem whose informal text claims a result is `open`.

## 4. Status (output of `status --json`)

JSON. One entry per tagged declaration. The page and any other viewer read
this and nothing else.

```json
{
  "schema": "leanblame.status.1",
  "library": "OpenPhysics",
  "commit": "9f8e7d…",
  "generated": "2026-10-23T15:00:00Z",
  "declarations": {
    "OpenPhysics.Ising.groundEnergy_le": {
      "module": "OpenPhysics.Ising",
      "kind": "theorem",
      "claim": "sha256:77c0…",
      "state": "valid",
      "flags": [],
      "signers": [{ "signer": "openreview:~Jane_Doe1", "date": "2026-10-23T14:02:11Z", "record": "sha256:…" }],
      "blocked_by": [],
      "proof": "proven",
      "tagged_deps": ["OpenPhysics.Ising.Hamiltonian"],
      "closure_size": 3412
    }
  }
}
```

| Field | Values |
|-------|--------|
| `state` | `valid`, `outdated`, `unsigned` |
| `flags` | any of `equiv-proven`, `withdrawn` |
| `blocked_by` | tagged dependencies whose state is not `valid`, recursively |
| `signers` | live approve records matching `claim`; empty unless `valid` |
| `proof` | `proven`, `open`, or `n/a` for non-theorems; from the last proof gate run |
| `tagged_deps` | direct tagged dependencies |
| `closure_size` | number of constants hashed into `claim` |
