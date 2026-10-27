# 14. Schemas

The four interfaces LeanBlame commits to. TOML for what humans read in git
(records, config); JSON for what machines pass around. Hashes are `sha256:`
plus 64 lowercase hex digits. Dates are UTC: native datetimes in TOML, ISO 8601
strings in JSON. A JSON object has every key, `null` for none; readers fail on a
missing or an unknown key. A name identifies a declaration in one export; its id
identifies it across exports.

## 1. Boundary list (JSON)

Produced by `export` from `@[trusted "id"]`, including tags found in imported
libraries, or from a verso-blueprint manifest (`--boundary FILE`,
[04-architecture.md](04-architecture.md), Blueprints). Read by `status`, from
the object store. It holds the declarations only. The commit, toolchain and
dependencies they come from are in `.leanblame/current` and in each record.

```json
{
  "schema": "leanblame.boundary.4",
  "library": "OpenPhysics",
  "declarations": [
    {
      "name": "OpenPhysics.Ising.Hamiltonian",
      "id": "3f2b8c1e-5a7d-4e9f-8b6a-0c1d2e3f4a5b",
      "parent": null,
      "module": "OpenPhysics.Ising",
      "kind": "def",
      "role": "defined",
      "informal": "Nearest-neighbour Ising Hamiltonian on a finite chain, H = -J Σ σᵢσᵢ₊₁, open boundary.",
      "statement": {
        "pretty": [{ "text": "OpenPhysics.Ising.Hamiltonian (J : ", "const": null }, { "text": "ℝ", "const": "Real" }, { "text": ") : ", "const": null }, { "text": "ℝ", "const": "Real" }],
        "plain": [{ "text": "OpenPhysics.Ising.Hamiltonian (J : ", "const": null }, { "text": "Real", "const": "Real" }, { "text": ") : ", "const": null }, { "text": "Real", "const": "Real" }]
      }
    }
  ]
}
```

| Field | Meaning |
|-------|---------|
| `name` | fully qualified constant name, after structure expansion |
| `id` | stays when the declaration is renamed or edited; never hashed. Its own: the UUID in `@[trusted "id"]`, or, from a blueprint, the label of its first declaration. Else the parent's id, `/`, and its name under the parent: `3f2b…/x` for the field `x` of a tagged structure, `def:point/norm` for another declaration of the label `def:point`. A tag without an id stops `export`. No two declarations share an id |
| `parent` | the declaration whose id stands for this one: the first declaration of its blueprint label, else the tagged structure or inductive it is a constructor or projection of; a parent without an id of its own is passed over for its own parent; else `null` |
| `kind` | the proof assistant's own label, non-empty, never interpreted. Lean: `def`, `theorem`, `axiom`, `inductive`, `ctor`, `opaque`, `quot`, `rec` (`rec` is never on the list). A definition the export marks partial would be labelled `partial def`; Lean 4.35 exports them as `opaque` |
| `role` | `assumed` (no body; the statement is taken as true), `defined` (the body is the meaning), `proved` (the body is a proof) |
| `informal` | the text the signer relies on, the docstring or the blueprint's statement, trimmed, with LF line endings; required. An untagged member without a docstring has its parent's |
| `statement` | the signature (name, binders, type) as segments, `pretty` with the assistant's default printer and `plain` with notation off; a segment is `{"text", "const"}`, `const` the printed name of the constant the text refers to, or `null` |

## 2. Record (storage, TOML)

One file per signoff in a records directory. Filename = sha256 of the file
bytes.

| Field | Approve | Withdraw | Meaning |
|-------|---------|----------|---------|
| `schema` | ✓ | ✓ | `leanblame.record.2` |
| `action` | ✓ | ✓ | `approve` or `withdraw` |
| `signer` | ✓ | ✓ | `provider:id`, stable id |
| `date` | ✓ | ✓ | TOML datetime, UTC |
| `module` | ✓ | | Lean module name |
| `commit` | ✓ | | library commit |
| `toolchain` | ✓ | | Lean version |
| `deps` | ✓ | | table of dependency commits |
| `export` | ✓ | | hash of the export the signer saw |
| `boundary` | ✓ | | hash of the boundary list the signer saw |
| `refers_to` | | ✓ | hash of the approve record withdrawn |
| `constants` | ✓ | optional | approve: table id → `{ name, claim, evidence }`, at least one; withdraw: list of ids, not empty; left out: all of the record |
| `note` | optional | optional | free text |

In an approve record, each declaration has its `name` in that export, its
`claim` hash, and optionally the `evidence`: the hash of an `equiv` proof the
signer relied on.

Validity rules: `refers_to` names an approve record; withdraw `signer` equals
that record's signer; the ids it lists are in that record; existing files are
never modified or deleted. Examples in [05-records.md](05-records.md).

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

Everything about the current export: one entry per tagged declaration, and
every record. Viewers display it; they never need another source. With
`--json`, nothing goes to stderr.

```json
{
  "schema": "leanblame.status.6",
  "library": "OpenPhysics",
  "commit": "9f8e7d…",
  "toolchain": "v4.35.0",
  "deps": { "mathlib": "a1b2c3…", "physlib": "d4e5f6…" },
  "requires": [{ "name": "physlib", "git": "https://github.com/leanprover-community/physlib", "rev": "d4e5f6…", "sub_dir": null }],
  "export": "sha256:…",
  "boundary": "sha256:…",
  "generated": "2026-10-23T15:00:00Z",
  "modules": [
    { "name": "OpenPhysics", "imports": ["OpenPhysics.Ising"], "sorried": "sha256:…" },
    { "name": "OpenPhysics.Ising", "imports": ["Mathlib.Analysis.SpecialFunctions.Exp"], "sorried": "sha256:…" }
  ],
  "standard_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "declarations": {
    "OpenPhysics.Ising.groundEnergy_le": {
      "id": "0b9c4e2a-7f13-4d5e-9a8b-6c7d8e9f0a1b",
      "parent": null,
      "module": "OpenPhysics.Ising",
      "kind": "theorem",
      "role": "proved",
      "informal": "…",
      "statement": { "pretty": [ "…" ], "plain": [ "…" ] },
      "claim": "sha256:77c0…",
      "state": "outdated",
      "change": [{ "cause": "untagged", "names": ["Mathlib.Finset.sum"] }],
      "signers": [],
      "history": [
        { "record": "sha256:…", "action": "approve", "signer": "openreview:~Jane_Doe1", "date": "2026-10-23T14:02:11Z",
          "name": "OpenPhysics.Ising.groundEnergy_le", "claim": "sha256:3b1f…", "note": null, "standing": "superseded" }
      ],
      "blocked_by": [],
      "proof": { "status": "proven", "axioms": ["propext"], "unpermitted": [] },
      "evidence": "sha256:…",
      "tagged_deps": ["OpenPhysics.Ising.Hamiltonian"],
      "untagged_deps": [{ "name": "Finset.sum", "module": "Mathlib.Algebra.BigOperators.Group.Finset.Defs" }],
      "closure_size": 3412
    }
  },
  "records": [
    { "record": "sha256:…", "path": "records/….toml", "action": "approve", "signer": "openreview:~Jane_Doe1",
      "date": "2026-10-23T14:02:11Z", "note": null, "module": "OpenPhysics.Ising", "commit": "1a2b3c…",
      "toolchain": "v4.35.0", "deps": { "mathlib": "a1b2c3…" }, "export": "sha256:…", "boundary": "sha256:…",
      "constants": [{ "id": "0b9c4e2a-7f13-4d5e-9a8b-6c7d8e9f0a1b", "name": "OpenPhysics.Ising.groundEnergy_le",
                      "claim": "sha256:3b1f…", "evidence": null }] }
  ],
  "untagged_in_library": [{ "name": "OpenPhysics.Ising.bond", "used_by": ["OpenPhysics.Ising.Hamiltonian"] }]
}
```

| Field | Values |
|-------|--------|
| `commit` | the commit the export comes from; `null` when a file under the library root differs from it (tracked or untracked): such an export cannot be signed or released |
| `toolchain`, `deps` | the Lean version, and the commits of git dependencies |
| `requires` | what the library's lakefile requires: the git URL, commit and subdirectory of each; `git` and `rev` are `null` for a path dependency |
| `modules` | the library's own modules: the modules each imports directly but `Init`, in its order, and `sorried`, the hash of its sorried copy (the module after its imports, in pieces), which `leanblame sorried` prints ([04-architecture.md](04-architecture.md), Sorried copies) |
| `standard_axioms` | the axioms every proof may rest on |
| `id`, `parent`, `module`, `kind`, `role`, `informal`, `statement` | as in the boundary list |
| `state` | `valid` (enough live approvals carry `claim`), `outdated` (live approvals exist, not enough carry `claim`), `unsigned` (none) |
| `change` | causes since the last live approval: `own-text`, `own-body`, `dep-spec`, `cut-moved`, `untagged`, each with the names involved; `[]` when the claim did not move or there is no live approval; `null` when unknown, because this store lacks the export that approval names |
| `signers` | signers of live approvals carrying `claim` |
| `history` | every record about this declaration, found by id, so across renames, in date order; `name` is its name in the record; a withdraw's `claim` is the one of the approval it withdraws |
| `standing` | what an approval is worth now: `current` (live, carries `claim`), `superseded` (live, an older claim), `withdrawn`, `excluded` (by `leanblame.toml`), `not-allowed` (the signer is not in `allowed_signers`); `null` for a withdraw |
| `blocked_by` | tagged dependencies whose state is not `valid`, recursively |
| `proof` | role `proved`: `proven` (every axiom standard, or tagged, `assumed` and valid), `open` (`sorryAx` or another axiom); `n/a` otherwise; with all axioms, and the `unpermitted` ones: neither standard, nor tagged and valid, nor `sorryAx` |
| `evidence` | hash of an `equiv` proof that the current claim means what a live approval meant, if any |
| `tagged_deps` | the tagged declarations the claim stops at |
| `untagged_deps` | the untagged declarations it uses directly, with their modules |
| `closure_size` | constants hashed into `claim`, proofs excluded |
| `records` | every record of the records directories, with all its fields, its hash and its path |
| `untagged_in_library` | untagged declarations of this library that tagged ones use, with those users; tag them so they get their own signer |

## 5. Sorried copies (output of `sorried`)

```json
{
  "sha256:…": [
    { "text": "namespace OpenPhysics", "keep": true, "declares": [], "uses": [] },
    { "text": "\n\n/-- The energy of a spin chain. -/\ndef energy (s : Chain) : ℝ := …",
      "keep": false, "declares": ["OpenPhysics.energy"], "uses": ["OpenPhysics.Chain"] },
    { "text": "\nend OpenPhysics", "keep": true, "declares": [], "uses": [] }
  ]
}
```

One key per hash asked for, as `status --json` lists them under `modules`; the
pieces of that module's copy, in order ([04-architecture.md](04-architecture.md),
Sorried copies). Joined, the texts are the module after its imports, proofs
replaced by `:= sorry`, with a last piece that closes the scopes it leaves open.

| Field | Meaning |
|-------|---------|
| `text` | the command, with the comments before it |
| `keep` | a challenge keeps the piece whatever its theorems need: it is not a declaration, or it is an instance written as one |
| `declares` | the constants the command added |
| `uses` | the constants of the library, declared by other pieces, that the command needs |
