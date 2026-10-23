# 4. Records

## Unit of signoff

The **declaration**. In Lean, `def`, `structure` (and the constants it
generates), `axiom`, `theorem`, `instance` and `abbrev` are all constants in
the environment. Comparator already works on constant names. A record lists
the constant names it covers plus the export hash they were read at.

One record may cover one definition or a whole file. That is only the length
of the list. Default: one record per module file.

## Fields

| Field | Meaning |
|-------|---------|
| `export` | sha256 of the export file the signer saw |
| `constants` | fully qualified names covered |
| `module` | Lean module name |
| `toolchain` | Lean version, e.g. `v4.35.0` |
| `deps` | pinned dependency commits, copied from `lake-manifest.json` |
| `signer` | `provider:id`, e.g. `openreview:~Jane_Doe1`, `orcid:0000-0002-1825-0097`, `github:alice`, `local:alice` |
| `date` | ISO 8601 |
| `action` | `approve` or `withdraw` |
| `refers_to` | withdraw only: hash of the record being withdrawn |
| `note` | optional free text |

### Example: approve

```toml
export = "sha256:3b1f…"
constants = ["OpenPhysics.Ising.Hamiltonian", "OpenPhysics.Ising.groundEnergy_le"]
module = "OpenPhysics.Ising"
toolchain = "v4.35.0"
[deps]
mathlib = "a1b2c3…"
physlib = "d4e5f6…"
signer = "openreview:~Jane_Doe1"
date = "2026-10-23T14:02:11Z"
action = "approve"
note = "Sign convention follows the shared conventions file, section 2."
```

### Example: withdraw

```toml
refers_to = "sha256:9c0d…"
signer = "openreview:~Jane_Doe1"
date = "2027-01-05T09:30:00Z"
action = "withdraw"
note = "Hamiltonian missed the boundary term for periodic chains. See issue 42."
```

## Storage

- One file per record in the library's `records/` folder.
- Filename is the record's own hash.
- Written by the sign server, never by hand.
- Branch protection: append only. No force push, no deletion.

Later: one records repo per institution. A library's config lists which
records repos it trusts (the cargo-vet import model) and may exclude a single
disputed record.

## Decisions

- **One signer is enough** for now. The format allows several records for the
  same hash; they simply accumulate.
- **No delta records** for now. After a change, the signer approves the new
  hash. The `equiv` result ("proven equivalent to hash H") is attached as
  information, not as a signoff. We considered cargo-vet-style delta records
  ("old -> new is fine") and dropped them for simplicity. They can be added
  later without breaking existing records.
- **`action` is the only type field.** Richer kinds were tried and dropped.

## What a signoff means: the memo

Shown to every signer before the approve button. Draft text:

> I have read the listed declarations at this exact version, including their
> imports and the checker configuration. I believe they mean what their
> documentation says. I have not checked proofs; the kernel does that. I take
> responsibility for the meaning of these declarations, not for their
> importance. If a declaration I signed is later shown not to mean what it
> says, this record will remain and a withdrawal will be added next to it.
>
> If other declarations in this library were already signed when I sign, I am
> responsible for my declarations being compatible with the shared conventions
> file as it stands today.

The last paragraph is the "later signer owns compatibility" rule; see
[05-versioning.md](05-versioning.md).
