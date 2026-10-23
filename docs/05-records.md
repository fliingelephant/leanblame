# 5. Records

## Unit

The declaration, each with its own claim hash. A `structure` counts as its
generated constants. One record may cover one declaration or a whole module.
Default: one record per module.

## Fields

| Field | Meaning |
|-------|---------|
| `action` | `approve` or `withdraw` |
| `signer` | `provider:id`, a stable id: `openreview:~Jane_Doe1`, `orcid:0000-0002-1825-0097`, `github:1234567` (numeric id, logins get reused), `local:alice` |
| `date` | ISO 8601 |
| `constants` | approve only: map from fully qualified name to claim hash |
| `module` | approve only: Lean module name |
| `commit` | approve only: library commit the signer saw |
| `toolchain` | approve only: Lean version |
| `deps` | approve only: dependency commits from `lake-manifest.json` |
| `evidence` | approve only, optional: hash of an `equiv` proof the signer relied on |
| `refers_to` | withdraw only: hash of the record being withdrawn |
| `note` | optional free text |

### Approve

```toml
action = "approve"
signer = "openreview:~Jane_Doe1"
date = "2026-10-23T14:02:11Z"
module = "OpenPhysics.Ising"
commit = "9f8e7d…"
toolchain = "v4.35.0"
deps = { mathlib = "a1b2c3…", physlib = "d4e5f6…" }
note = "Sign convention follows OpenPhysics.Conventions, section 2."

[constants]
"OpenPhysics.Ising.Hamiltonian" = "sha256:3b1f…"
"OpenPhysics.Ising.groundEnergy_le" = "sha256:77c0…"
```

### Withdraw

```toml
action = "withdraw"
signer = "openreview:~Jane_Doe1"
date = "2027-01-05T09:30:00Z"
refers_to = "sha256:9c0d…"
note = "Hamiltonian missed the boundary term for periodic chains. See issue 42."
```

## Several records for one declaration

A record is **live** if no withdraw record points at it. A declaration is
`valid` if any live approve record carries its current claim hash. Otherwise
`outdated` if live records exist, `unsigned` if none. Flag `withdrawn` if any
record was ever withdrawn.

## Storage

- One file per record in `records/`. Filename = sha256 of the file bytes as the
  sign server wrote them.
- Written by the sign server. The terminal `sign` command writes `local:`
  records only, unless given a provider token.
- The validator runs as a required CI check. It rejects any commit that
  modifies or deletes an existing record file, and any record that fails the
  schema.
- The party you trust is whoever holds the sign server's push credential.
  Name it in the library's README.

Later: one records repo per institution, listed in `leanblame.toml`; a
disputed record can be excluded by hash.

## Decisions

- One signer suffices. Several records for the same hash simply accumulate.
- No delta records ("old → new is fine"). The signer approves the new hash;
  `equiv` evidence is attached as information.
- `action` is the only type field.

## What a signoff means: the memo

Shown above the approve button:

> I have read these declarations: their text and their informal description.
> I believe they mean what that description says.
> For tagged declarations they use, I have read the name, type and description, and I rely on their named signers for the rest.
> Everything untagged underneath is mine.
> I have not checked proofs. The kernel does that.
> I own the meaning of these declarations, not their importance.
> If one is later shown not to mean what it says, this record stays and a withdrawal is added next to it.
> I have checked my declarations against the shared conventions module as it stands today.
