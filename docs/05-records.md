# 5. Records and authority

## Unit

The declaration, each with its own claim hash. A record lists expanded
constants explicitly: tagging a structure produces entries for the type, its
constructors and its projections. One record may cover one declaration or a
whole module. Default: one record per module.

## Fields

Exact schema in [14-schemas.md](14-schemas.md). Two examples:

### Approve

```toml
schema = "leanblame.record.1"
action = "approve"
signer = "openreview:~Jane_Doe1"
date = 2026-10-23T14:02:11Z
module = "OpenPhysics.Ising"
commit = "9f8e7d…"
toolchain = "v4.35.0"
deps = { mathlib = "a1b2c3…", physlib = "d4e5f6…" }
export = "sha256:…"
boundary = "sha256:…"
note = "Sign convention follows OpenPhysics.Conventions, section 2."

[constants]
"OpenPhysics.Ising.Hamiltonian" = "sha256:3b1f…"
"OpenPhysics.Ising.groundEnergy_le" = "sha256:77c0…"
```

### Withdraw

```toml
schema = "leanblame.record.1"
action = "withdraw"
signer = "openreview:~Jane_Doe1"
date = 2027-01-05T09:30:00Z
refers_to = "sha256:9c0d…"
constants = ["OpenPhysics.Ising.Hamiltonian"]   # optional; default: all in the record
note = "Hamiltonian missed the boundary term for periodic chains. See issue 42."
```

Dates are native TOML datetimes in UTC.

## Authority: three kinds

| Over | Who | Can |
|------|-----|-----|
| **a record** | its signer, only | approve, withdraw, approve again |
| **a library** | its maintainers, via git | tag declarations, choose which records repos count, exclude a record by hash, cut releases, edit the conventions module |
| **identity** | the login provider; the institution hosting a records repo | say who a signer is; host and back their records |

A record is one person's statement. Nobody edits it, not even a maintainer.
A maintainer who thinks a record is wrong **excludes** it in `leanblame.toml`
and opens an issue. That is a dispute. Git blame on the config shows which
maintainer excluded what.

Who wrote the declaration is a separate trail: the git commit author. Agents
may write declarations. Only humans sign.

## Withdraw rules

- `refers_to` must point at an approve record, never at a withdraw.
- A withdraw counts only if its `signer` equals the approve record's signer.
  `validate` rejects others.
- A withdraw may list `constants`; default is every constant in the record.
- To undo a withdrawal, approve again. There is no withdraw of a withdraw.

## Several records for one declaration

A record is **live** if no valid withdraw points at it, or at this constant in
it, and its signer is allowed by `leanblame.toml`. A declaration is `valid` if
at least `required_signers` distinct signers have live approve records carrying
its current claim hash (default one). Otherwise `outdated` if live records
exist, `unsigned` if none. Flag `withdrawn` if any record for it was ever
withdrawn.

## Storage

- One file per record in `records/`. Filename = sha256 of the file bytes as
  the sign server wrote them.
- Written by the sign server. Terminal `sign` writes `local:` records only,
  unless given a provider token.
- `validate` runs as a required CI check: schema, authority rules, and no
  modification or deletion of an existing record file.
- The party you trust is whoever holds the sign server's push credential,
  normally the hosting institution. Name it in the library's README.

A library may list several records repos in `leanblame.toml` and exclude
individual records by hash. `exclude` is applied before liveness.

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
