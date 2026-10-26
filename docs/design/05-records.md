# 5. Records and authority

## Unit

The declaration, each with its own claim hash. A record names each declaration
by its id, with its name and claim hash at that export, so an approval follows
the declaration through a rename. A record lists expanded constants explicitly:
tagging a structure produces entries for the type, its constructors and its
projections, whose ids are the structure's id and their names (`3f2b…/x`). One
record may cover one declaration or a whole module. Default: one record per
module.

## Fields

Exact schema in [14-schemas.md](14-schemas.md). Two examples:

### Approve

```toml
schema = "leanblame.record.2"
action = "approve"
signer = "openreview:~Jane_Doe1"
date = 2026-10-23T14:02:11Z
module = "OpenPhysics.Ising"
commit = "9f8e7d…"
toolchain = "v4.35.0"
export = "sha256:…"
boundary = "sha256:…"
note = "Sign convention follows OpenPhysics.Conventions, section 2."

[deps]
mathlib = "a1b2c3…"
physlib = "d4e5f6…"

[constants]
3f2b8c1e-5a7d-4e9f-8b6a-0c1d2e3f4a5b = {name = "OpenPhysics.Ising.Hamiltonian", claim = "sha256:3b1f…"}
0b9c4e2a-7f13-4d5e-9a8b-6c7d8e9f0a1b = {name = "OpenPhysics.Ising.groundEnergy_le", claim = "sha256:77c0…", evidence = "sha256:5e6f…"}
```

`evidence` is optional: an `equiv` proof the signer relied on for that
declaration ([06-versioning.md](06-versioning.md)).

### Withdraw

```toml
schema = "leanblame.record.2"
action = "withdraw"
signer = "openreview:~Jane_Doe1"
date = 2027-01-05T09:30:00Z
refers_to = "sha256:9c0d…"
constants = ["3f2b8c1e-5a7d-4e9f-8b6a-0c1d2e3f4a5b"]   # ids; optional: left out, all in the record
note = "Hamiltonian missed the boundary term for periodic chains. See issue 42."
```

Dates are native TOML datetimes in UTC.

## Authority: three kinds

| Over | Who | Can |
|------|-----|-----|
| **a record** | its signer, only | approve, withdraw, approve again |
| **a library** | its maintainers, via git | tag declarations, choose which records repos count, exclude an approve record by hash, cut releases, edit the conventions module |
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
- A withdraw may list `constants`, ids of declarations in that record, at least
  one; left out, it withdraws every declaration in the record.
- To undo a withdrawal, approve again. There is no withdraw of a withdraw.

## Several records for one declaration

An approve record is **live** for a declaration if no counting withdraw (rules
above) covers that declaration in it, `exclude` does not list it, and its signer
is allowed by `leanblame.toml`. This is the one definition; validity is built on
it ([03-trust-model.md](03-trust-model.md), Validity). Every record stays visible
in `blame` and in the `history` of `status --json`, each approval with its
standing: `current` (live, at the current claim), `superseded` (live, an older
claim), `withdrawn`, `excluded` or `not-allowed`.

A withdraw that breaks the rules above, an `exclude` entry that names no approve
record, a record in two records directories, and a file in a records directory
that is not a record are problems. `validate` lists them; the other commands
stop.

## Storage

- One file per record in a records directory (`records/` by default).
  Filename = sha256 of the file bytes as the sign server wrote them.
- Terminal `sign` writes `local:` records. Provider identities (OpenReview,
  ORCID, GitHub) come through the sign server, which is not built yet.
- `validate` gates every record, wherever the adopter runs it: schema, authority rules, and no
  modification or deletion of an existing record.
- The party you trust is whoever holds the sign server's push credential,
  normally the hosting institution. Name it in the library's README.

A library lists its records directories in `leanblame.toml` (local
directories; remote repositories later) and excludes individual approve records
by hash. Every key of `leanblame.toml` is required; `init` writes them all. A
withdrawal cannot be excluded: a signer's word about their own record stands,
and nobody can be made to vouch for what they took back.

## Decisions

- One signer suffices with `required_signers = 1`, which `init` writes. Several
  records for the same hash accumulate.
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
