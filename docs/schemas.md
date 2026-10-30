# Schemas

The interfaces LeanBlame commits to. TOML for what humans read in git
(records, config); JSON for what machines pass around. Hashes are `sha256:`
plus 64 lowercase hex digits. Dates are UTC: native datetimes in TOML, ISO 8601
strings in JSON. A JSON object has every key, `null` for none; readers fail on a
missing or an unknown key. A name identifies a declaration in one export; its id
identifies it across exports.

## 1. Boundary list (JSON)

Produced by `export` from `@[trusted "id"]`, including tags found in imported
libraries, or from a verso-blueprint manifest (`--boundary FILE`,
[decisions.md](decisions.md), Blueprints). Read by `status`, from
the object store. It holds the declarations only, in source order: a module
after the modules it imports, then by position in the file (a member without a
position of its own at its parent's), ties by name. The commit, toolchain and
dependencies they come from are in `.leanblame/current` and in each record.

```json
{
  "library": "Example",
  "declarations": [
    {
      "name": "Example.Ising.Hamiltonian",
      "id": "3f2b8c1e-5a7d-4e9f-8b6a-0c1d2e3f4a5b",
      "parent": null,
      "module": "Example.Ising",
      "kind": "def",
      "role": "defined",
      "informal": "Nearest-neighbour Ising Hamiltonian on a finite chain, H = -J Σ σᵢσᵢ₊₁, open boundary.",
      "statement": {
        "pretty": [{ "text": "Example.Ising.Hamiltonian (J : ", "const": null }, { "text": "ℝ", "const": "Real" }, { "text": ") : ", "const": null }, { "text": "ℝ", "const": "Real" }],
        "plain": [{ "text": "Example.Ising.Hamiltonian (J : ", "const": null }, { "text": "Real", "const": "Real" }, { "text": ") : ", "const": null }, { "text": "Real", "const": "Real" }]
      }
    }
  ]
}
```

| Field | Meaning |
|-------|---------|
| `library` | the name of the library's Lake package |
| `name` | fully qualified constant name, after structure expansion |
| `id` | stays when the declaration is renamed or edited; never hashed. Its own: the UUID in its tag, `@[trusted "id"]` or `attribute [trusted "id"] Name`, or, from a blueprint, the label of its first declaration. Else the parent's id, `/`, and its name under the parent: `3f2b…/x` for the field `x` of a tagged structure, `def:point/norm` for another declaration of the label `def:point`. A tag without an id stops `export`. No two declarations share an id |
| `parent` | the declaration whose id stands for this one: the first declaration of its blueprint label, else the tagged structure or inductive it is a constructor or projection of; a parent without an id of its own is passed over for its own parent; else `null` |
| `kind` | what it is, in the proof assistant's own words; never interpreted, never hashed (the hash takes the kernel's kind, [trust-model.md](../trust-model.md)). Lean, as its documentation (doc-gen4) names it: `def`, `theorem`, `axiom`, `opaque`, `instance`, `inductive`, `structure`, `class`, `constructor`, and `field` for a structure's projection |
| `role` | `assumed` (no body; the statement is taken as true), `defined` (the body is the meaning), `proved` (the body is a proof) |
| `informal` | the text the signer relies on, the docstring or the blueprint's statement, trimmed, with LF line endings; required. An untagged member without a docstring has its parent's |
| `statement` | the signature (name, binders, type), printed twice as segments: `pretty` as the library's documentation (doc-gen4) prints it, with the notations of the library and what it imports; `plain` with notation, field notation and coercions off. A segment is `{"text", "const"}`, `const` the printed name of the constant the text refers to, or `null` |

## 2. Record (storage, TOML)

One file per signoff in a records directory. Filename = sha256 of the file
bytes.

| Field | Approve | Withdraw | Meaning |
|-------|---------|----------|---------|
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
never modified or deleted.

An approve record:

```toml
action = "approve"
signer = "example:jane"
date = 2026-10-23T14:02:11Z
module = "Example.Ising"
commit = "9f8e7d…"
toolchain = "v4.35.0"
export = "sha256:…"
boundary = "sha256:…"
note = "Sign convention follows Example.Conventions, section 2."

[deps]
mathlib = "a1b2c3…"
physlib = "d4e5f6…"

[constants]
3f2b8c1e-5a7d-4e9f-8b6a-0c1d2e3f4a5b = {name = "Example.Ising.Hamiltonian", claim = "sha256:3b1f…"}
0b9c4e2a-7f13-4d5e-9a8b-6c7d8e9f0a1b = {name = "Example.Ising.groundEnergy_le", claim = "sha256:77c0…", evidence = "sha256:5e6f…"}
```

A withdraw record:

```toml
action = "withdraw"
signer = "example:jane"
date = 2027-01-05T09:30:00Z
refers_to = "sha256:9c0d…"
constants = ["3f2b8c1e-5a7d-4e9f-8b6a-0c1d2e3f4a5b"]   # ids; optional: left out, all in the record
note = "Hamiltonian missed the boundary term for periodic chains. See issue 42."
```

## 3. Release manifest (output of `release`, JSON)

```json
{
  "library": "Example",
  "tag": "2027.04",
  "commit": "9f8e7d…",
  "toolchain": "v4.35.0",
  "deps": { "mathlib": "a1b2c3…", "physlib": "d4e5f6…" },
  "export": "sha256:…",
  "boundary": "sha256:…",
  "records": ["sha256:…", "sha256:…"],
  "kernel": { "checker": "leanchecker", "version": "v4.35.0", "passed": true },
  "theorems": {
    "Example.Ising.groundEnergy_le": { "status": "proven", "axioms": ["Classical.choice", "propext"] },
    "Example.Ising.gap_conjecture":  { "status": "open", "axioms": ["sorryAx"] },
    "Example.Ising.uses_postulate":  { "status": "proven", "axioms": ["Example.Conventions.locality"] }
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
  "library": "Example",
  "commit": "9f8e7d…",
  "toolchain": "v4.35.0",
  "deps": { "mathlib": "a1b2c3…", "physlib": "d4e5f6…" },
  "export": "sha256:…",
  "boundary": "sha256:…",
  "generated": "2026-10-23T15:00:00Z",
  "standard_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "declarations": [
    {
      "name": "Example.Ising.groundEnergy_le",
      "id": "0b9c4e2a-7f13-4d5e-9a8b-6c7d8e9f0a1b",
      "parent": null,
      "module": "Example.Ising",
      "kind": "theorem",
      "role": "proved",
      "informal": "…",
      "statement": { "pretty": […], "plain": […] },
      "claim": "sha256:77c0…",
      "state": "outdated",
      "change": [{ "cause": "untagged", "names": ["Mathlib.Finset.sum"] }],
      "signers": [],
      "history": [
        { "record": "sha256:…", "action": "approve", "signer": "example:jane", "date": "2026-10-23T14:02:11Z",
          "name": "Example.Ising.groundEnergy_le", "claim": "sha256:3b1f…", "note": null, "standing": "superseded" }
      ],
      "blocked_by": [],
      "proof": { "status": "proven", "axioms": ["propext"], "unpermitted": [] },
      "evidence": "sha256:…",
      "tagged_deps": ["Example.Ising.Hamiltonian"],
      "untagged_deps": [{ "name": "Finset.sum", "module": "Mathlib.Algebra.BigOperators.Group.Finset.Defs" }],
      "closure_size": 3412
    }
  ],
  "records": [
    { "record": "sha256:…", "path": "records/….toml", "action": "approve", "signer": "example:jane",
      "date": "2026-10-23T14:02:11Z", "note": null, "module": "Example.Ising", "commit": "1a2b3c…",
      "toolchain": "v4.35.0", "deps": { "mathlib": "a1b2c3…" }, "export": "sha256:…", "boundary": "sha256:…",
      "constants": [{ "id": "0b9c4e2a-7f13-4d5e-9a8b-6c7d8e9f0a1b", "name": "Example.Ising.groundEnergy_le",
                      "claim": "sha256:3b1f…", "evidence": null }] }
  ],
  "untagged_in_library": [{ "name": "Example.Ising.bond", "used_by": ["Example.Ising.Hamiltonian"] }]
}
```

| Field | Values |
|-------|--------|
| `commit` | the commit the export comes from; `null` when a file under the library root differs from it (tracked or untracked): such an export cannot be signed or released |
| `toolchain`, `deps` | the Lean version, and the commits of git dependencies |
| `standard_axioms` | the axioms every proof may rest on |
| `declarations` | one entry per tagged declaration, in the boundary list's order (source order) |
| `name`, `id`, `parent`, `module`, `kind`, `role`, `informal`, `statement` | as in the boundary list |
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

## 5. Diff (output of `diff --json`)

What changed between two points: the export an approve record names (`--from`), and another approve
record's (`--to`) or the last export. The comparison is the one `status` makes against the last live
approval, part by part of each claim, by hash: a difference is one the kernel sees, and a change of
the printer is none. Declarations are matched by id. With names or ids, those declarations; without,
every declaration whose claim differs, and those only one point has. With `--json`, nothing goes to
stderr.

```json
{
  "library": "Example",
  "from": { "record": "sha256:…", "commit": "1a2b3c…", "export": "sha256:…", "boundary": "sha256:…" },
  "to": { "record": null, "commit": "9f8e7d…", "export": "sha256:…", "boundary": "sha256:…" },
  "declarations": [
    {
      "id": "0b9c4e2a-7f13-4d5e-9a8b-6c7d8e9f0a1b",
      "from": { "name": "Example.Ising.groundEnergy_le", "module": "Example.Ising", "kind": "theorem",
                "claim": "sha256:3b1f…", "informal": "…", "statement": { "pretty": […], "plain": […] } },
      "to": { "name": "Example.Ising.groundEnergy_le", "module": "Example.Ising", "kind": "theorem",
              "claim": "sha256:77c0…", "informal": "…", "statement": { "pretty": […], "plain": […] } },
      "changes": {
        "informal": false, "statement": false, "body": false,
        "relies_on": { "added": [], "removed": [], "changed": ["Example.Ising.Hamiltonian"] },
        "cut_moved": [], "untagged": []
      }
    }
  ]
}
```

| Field | Meaning |
|-------|---------|
| `from`, `to` (top) | the two points: the record (`null`: the last export), its commit (`null`: uncommitted changes), the export and the boundary list |
| `from`, `to` (declaration) | the declaration at each point, as the boundary list has it, with its claim there; `null` where it does not exist (added, removed) |
| `changes` | `null` when one side is `null` |
| `informal` | its informal text differs |
| `statement` | its kind, role, universe parameters or type differs |
| `body` | its body differs |
| `relies_on` | the tagged declarations its claim stops at: `added` (the old closure lacks them), `removed` (the new one lacks them), `changed` (in both, their spec differs: name, kind, type or informal text) |
| `cut_moved` | dependencies in both closures that gained or lost their tag |
| `untagged` | untagged declarations in both closures that differ |

A renamed declaration has two names, and its claim moved, as the name is hashed. The text form
prints one line per declaration: `NAME [renamed-from=OLD] change=cause:names;..
[relies-on=+ADDED,-REMOVED]`, with the causes of `status`, or `NAME added`, `NAME removed`, `NAME
unchanged`; then the old and the new informal text and statement where they differ.

## 6. Piece graph (output of `challenge --graph`)

The pieces the comparator challenges of the library's tagged declarations are cut from
([decisions.md](decisions.md), "Challenges"), in the order their files hold them.

```json
{
  "pieces": [
    { "file": "lakefile.toml", "text": "name = \"challenge\"\n…", "needs": [], "theorem": null, "problem": null },
    { "file": "ChallengeDeps.lean", "text": "\n/-- Twice a natural number. -/\ndef double …\n", "needs": [3, 4],
      "theorem": null, "problem": null },
    { "file": "Challenge.lean", "text": "\ntheorem energy_even (n : Nat) : energy n % 2 = 0 := sorry\n",
      "needs": [0, 1, 5, 9], "theorem": "Sample.energy_even", "problem": null }
  ]
}
```

| Field | Meaning |
|-------|---------|
| `file` | `lakefile.toml`, `lean-toolchain`, `ChallengeDeps.lean` or `Challenge.lean` |
| `text` | the piece's text in that file |
| `needs` | the pieces it needs, by index |
| `theorem` | in `Challenge.lean`: the tagged theorem it states; in `ChallengeDeps.lean`: the tagged declaration it declares (a theorem with its proof); else `null` |
| `problem` | why a challenge that holds it cannot be made, or `null` |

The challenge of tagged declarations D: start from the lakefile and toolchain pieces, the
`Challenge.lean` pieces whose `theorem` is in D, and, for each other declaration in D, the
`ChallengeDeps.lean` piece whose `theorem` it is; add the pieces they need, then the pieces those
need, until nothing is added. It cannot be made when a piece it holds has a `problem`, or a
`ChallengeDeps.lean` piece it holds has its `theorem` among the theorems of D that have a statement
(the others need that one's proof). Otherwise each file is the text of its pieces, in index order.

