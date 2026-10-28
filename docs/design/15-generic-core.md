# 15. Generic core

Decided 2026-10-24. This file is the specification of the core/frontend split of
`cli/`. It is written so that someone who has not followed the discussion can
implement it without inventing anything. Where it says "must", the choice was
made by the owner; do not reopen it.

## 1. Why

LeanBlame tracks trust at the boundary of formalized content: the declarations a
human must read because the kernel cannot check their meaning. The owner's
stated goal is a clean, minimal, generic, reusable tool for that. Lean is the
first proof assistant, not the last; a field, a library or an institution must
be able to reuse the mechanism without the Lean parts.

The mechanism itself does not know Lean. It is:

1. a graph of declarations, each with a statement, possibly a body,
   dependencies and the assumptions it rests on;
2. a hash of exactly what a human reads of each declaration;
3. records in git in which named people sign those hashes;
4. validity recomputed from the graph and the records.

Only step 1 needs the proof assistant: reading its export, printing its terms
canonically, erasing proofs, asking its kernel. Today that knowledge is mixed
into the walk, the status computation and the schemas (`Lean.Name` as the key,
Lean's constant kinds as an enum, Lean's three standard axioms and `sorryAx` as
constants of the status code). This document separates the two.

Why now: the web service (OpenVouch, a separate repository) is about to build on
`status --json`, the boundary list and the cache. Those formats must carry the
generic model before anything depends on them.

## 2. The model

### 2.1 Roles

Every declaration has a **statement** (its type: what it claims) and may have a
**body**. A human reviewing meaning reads the statement always, and the body only
when the body *is* the meaning. The three cases:

| role | meaning of the body | Lean kinds |
|------|---------------------|------------|
| `assumed` | there is no body; the statement is taken as true | `axiom` |
| `defined` | the body is the meaning; the signer reads it | `def`, `opaque`, `inductive`, `ctor`, `quot`, `rec` |
| `proved` | the body is a proof; the kernel checks it, nobody reads it | `theorem` |

`lemma`, `structure`, `class`, `instance`, `abbrev` are surface syntax; the
kernel already presents them as `theorem`, `inductive` or `def`. Rocq
(`Definition`/`Fixpoint`/`Inductive`, `Theorem`/`Lemma`, `Axiom`/`Parameter`) and
Isabelle (definitions and datatypes, theorems, axiomatizations) map onto the
same three roles. A definition the export marks partial would be labelled
`partial def`; Lean 4.35 exports them as `opaque`.

A `defined` declaration may have **no visible body**: Lean hides the body of
`opaque` and `partial` definitions from the kernel, `quot` and `rec` have none
to read. Then the signer signs kind, statement and informal text only, exactly
as today for `opaque` and `partial`.

### 2.2 Kind is a label, role is the generic field

The proof assistant's own classification is kept as a free string, `kind`,
because the signer sees it and it belongs in the hash ("def" and "theorem" with
the same statement are different things to sign). The core never interprets
`kind`. It interprets `role`:

- the body is hashed iff `role = defined` and the frontend reports a body;
- the dependencies of a `proved` declaration are those of its statement only;
- the assumption footprint (today's axiom report) is computed for `proved`
  declarations;
- a permitted assumption is one with `role = assumed`, tagged and valid.

Consequence: the `Safety` field (`safe`/`partial`/`opaque`) disappears. What it
carried is now in the label (`partial def`) and in the absence of a body hash.

### 2.3 Names

The core keys everything by the **printed name**, a `String`, exactly as the
boundary list, the records and `status --json` already write it. `Lean.Name`
stays inside the Lean frontend. The frontend must map strings back to its own
names and must fail if two distinct constants of one export print the same
(it never happens for exported constants; the check costs one hash map).

### 2.4 What the frontend reports about one declaration

```lean
namespace LeanBlame.Core

inductive Role where
  | assumed | defined | proved
-- prints as "assumed" | "defined" | "proved"

/-- The raw facts about one declaration, as a frontend reports them. -/
structure Decl where
  /-- The printed name; the key within one export. -/
  name : String
  /-- Where it is defined (Lean: its module); never hashed. -/
  module : String
  /-- The assistant's own label. Lean: `def`, `theorem`, `axiom`, `inductive`,
  `ctor`, `opaque`, `quot`, `rec`. Never interpreted by the core. -/
  kind : String
  role : Role
  /-- Universe (level) parameters; 0 for an assistant without them. -/
  uparams : Nat
  /-- Hex SHA-256 of the canonical statement, proofs erased. -/
  typeHash : String
  /-- Hex SHA-256 of the canonical body, proofs erased. `none` when the role is
  not `defined` or the body is not visible. -/
  bodyHash : Option String
  /-- The direct dependencies the hash follows: every constant of the statement
  and, when `bodyHash` is `some`, of the body; the frontend adds what the signer
  relies on through this declaration (Lean: the constructors of an inductive,
  the inductive of a constructor). Sorted by name, without the declaration
  itself, no repetitions. -/
  deps : Array String
```

`typeHash` and `bodyHash` are computed by the frontend; the core never sees a
term. For Lean they are exactly today's `Canon.exprHash` of the erased type and
body (canonical printing unchanged).

### 2.5 What the frontend serves for one export

```lean
/-- One export, as a frontend serves it to the core. -/
structure Source where
  /-- The facts about a constant. Throws when the export lacks it or it cannot
  be hashed (Lean: `unsafe`). Called once per constant the hash walk reaches. -/
  decl : String → IO Decl
  /-- Every constant the statement and the body of a constant rest on, proofs
  included; `#[]` for a constant the footprint ignores (unknown; Lean: `unsafe`
  or `partial`). The core walks this transitively for the assumption footprint. -/
  uses : String → Array String
  /-- Whether a constant is an assumption. `false` for unknown constants. -/
  isAssumed : String → Bool

/-- What a proof assistant contributes to the tool besides the `Source` of each
export, which `export` builds (§10). -/
structure Backend where
  /-- Whether the assistant's own checker replays the export at a path. -/
  kernelAccepts : System.FilePath → IO Bool
  /-- The name of that checker, for the release manifest. Lean: `leanchecker`. -/
  checker : String
  /-- Assumptions that are part of the logic itself. Lean: `propext`,
  `Classical.choice`, `Quot.sound`. -/
  standard : Array String
  /-- Assumptions standing for a missing proof. Lean: `sorryAx`. -/
  incomplete : Array String
```

The core hashes a `Source` against a boundary list and produces `Hashed`:

```lean
/-- One hashed declaration. -/
structure Node where
  decl : Decl
  /-- Tagged declarations only. -/
  informal : Option String
  own : String
  /-- Tagged declarations only. -/
  spec : Option String
  claim : String

/-- Every constant reached from the boundary list, hashed. -/
structure Hashed where
  nodes : Std.HashMap String Node
  /-- Per tagged declaration, the assumptions its statement and body rest on,
  proofs included, sorted. A function of the export alone. -/
  axioms : Std.HashMap String (Array String)
  boundary : BoundaryList
```

(`Hashed.declarations` goes away: `boundary.declarations` already holds the
names, in list order.)

The frontend's `decl` is called from the core's worklist loop, one constant at
a time, so a frontend may compute lazily. The Lean frontend must keep one
`Meta` state for the whole walk so its caches serve every constant, as today;
with `IO` callbacks that means holding the `Core.State` and `Meta.State` in
references across calls, not starting a fresh `MetaM` per constant.

## 3. Two layers

```
cli/LeanBlame/Attr.lean          @[trusted]                                (unchanged)
cli/LeanBlame/Core/*.lean        the generic tool: knows strings, hashes, records, git
cli/LeanBlame/Lean/*.lean        the Lean frontend: export, terms, kernel
cli/Main.lean                    wires the Lean backend into the core commands
```

| `Core/` | from today's |
|---------|--------------|
| `Util`, `Sha256`, `Time` | the same files, moved |
| `Schema` | `Schema` with `Role`, `kind : String`, without `Kind` and `Safety` |
| `Config`, `Records`, `Store` | the same files, moved |
| `Hash` | the hash part of `Canon`: `netstr`, `hashFields`, `optField`, `own`, `spec`, `DepEntry`, `claim`, `group`, `member` |
| `Graph` | `Role`, `Decl`, `Source`, `Backend`, `Node`, `Hashed`, `sortNames`; may live in `Schema`/`Walk` instead if that reads better; and, per §9, `Cache` as the `graphs` store objects, schema `leanblame.graph.1` |
| `Walk` | `Walk` over strings: the worklist cut at tagged declarations, Tarjan, the footprint walk, `closureOf`, `compare` |
| `Status`, `Sign`, `Validate` | the same; per §9 no `Backend`: they read graphs from the store and never hash |
| `Release` | the same, taking the `Backend` for the kernel gate |

| `Lean/` | from today's |
|---------|--------------|
| `Canon` | the term printer: `name`, `level`, `expr`, `print`, `exprHash` |
| `Erase`, `Load` | unchanged |
| `Source` | new: `ofExport : LeanExport.ExportedEnv → IO Core.Source`, `ofFile`, `kindOf`, `roleOf`, the string→`Name` map with the collision check, the `Meta` runner, `backend : Core.Backend` |
| `Export`, `Blueprint`, `Equiv` | the same, building `BoundaryDecl` with `kind` and `role` from `Source.kindOf`/`roleOf`, calling the core |

Import rule, checked by grep: a module under `Core/` imports only `Init`, `Std`,
`Lean.Data.*` (Json, HashMap and the like), `Lake.Toml`, `Lake.Util.*` and other
`Core/` modules. It never imports `Lean.Meta.*`, `Lean.Expr`, `Lean.Environment`,
`Lean.AddDecl`, `Lean.Util.FoldConsts`, `LeanExport.*`, `Lake.Load.*`,
`LeanBlame.Attr` or anything under `LeanBlame.Lean`. The executable is written
in Lean; that is not what the rule is about. The rule is that nothing in `Core/`
knows what a Lean term, environment or kernel is.

`lakefile.toml`: the internal library's globs become
`["LeanBlame.Core.+", "LeanBlame.Lean.+"]`. `test/Canon.lean` imports
`LeanBlame.Lean.Canon`.

## 4. The hash

Formulas as in [03-trust-model.md](03-trust-model.md), with `role` in and
`safety` out, and the name entering as its printed string. Every domain tag
moves to `.2`; every claim hash changes. There are no records in the wild
(v0.1.0 has no users), so no compatibility is kept.

```
own(c)   = H("leanblame.own.2",   kind, role, name, uparams, type, body?, informal?)
spec(c)  = H("leanblame.spec.2",  kind, role, name, uparams, type, informal)
claim(c) = H("leanblame.claim.2", own(c), sorted over direct dependencies d:
               tagged(d)   -> ("spec", spec(d))
               untagged(d) -> ("full", claim(d)))
group    = H("leanblame.group.2",  count, member owns sorted, external entries)
member   = H("leanblame.member.2", group, name)
```

`H` is SHA-256 over the tag and the fields, each as `<byte length>:<bytes>`;
`body?` and `informal?` as today (`+<len>:<bytes>` or `-`). `type` and `body`
are the hex hashes the frontend reports. Canonical printing of terms (inside
the Lean frontend) does not change; constants inside a printed term keep the
component encoding of `Canon.name`, which is part of the term printer, not of
the field encoding.

The hash walk is unchanged in substance: seed from the boundary list, cut at
tagged declarations (each tagged declaration is a seed of its own), follow
`deps`, group cycles with Tarjan, hash components in dependency order.

The footprint walk is unchanged in substance: from each tagged declaration,
follow `uses` transitively; the assumptions found (`isAssumed`) are the
declaration's `axioms`. The status rule is unchanged, with the two name sets
coming from the `Backend`: a `proved` declaration is `proven` when every
assumption is in `standard` or is tagged, `assumed` and valid; `open` otherwise;
a warning names each assumption that is neither in `incomplete` nor permitted.

## 5. Schemas

**Boundary list** → `leanblame.boundary.2`. Each declaration gains `role`;
`kind` is a non-empty label. The strict reader checks `role` is one of the
three and `kind` is non-empty; the Lean frontend keeps refusing to tag `rec`
and `unsafe` at export time.

**Status** → `leanblame.status.2`. Each declaration gains `role`. `kind` is
the label. `proof` is computed for `role = proved`, `n/a` otherwise.

**Cache** → `leanblame.cache.3`. Names are plain strings; a node carries
`name, kind, role, uparams, type, body, informal, deps, own, spec, claim`; the
file also holds the `Backend`'s `standard`, `incomplete` and `checker`.

**Record** `leanblame.record.1` and **release manifest** `leanblame.release.1`
do not change shape. The manifest's `theorems` are the declarations with
`role = proved`.

Update [14-schemas.md](14-schemas.md) accordingly, including the `kind` row
(labels, with Lean's list) and a `role` row.

## 6. Behaviour that must not change

The eight commands, their flags, their output lines and messages; `equiv`;
`validate`; the records format; the store layout and the sweep; the warnings
of `status`; the test script's scenario. `bash cli/test/run.sh` passes with
its assertions updated only where this document changes a schema (the status
JSON gains `role`, the schema id moves to `.2`, the `kind` values are unchanged
for the sample library) and extended with one assertion per role value on the
sample (`Sample.energy` defined, `Sample.energy_even` proved, `Sample.energy_pos`
assumed). The build stays warning-free.

## 7. Documents to update

[03-trust-model.md](03-trust-model.md) ("The hash, precisely": fields, formulas,
tags, roles); [04-architecture.md](04-architecture.md) ("Three parts" and
"Beyond Lean": the two layers, what a frontend implements); [11-decisions.md](11-decisions.md)
(the hash decision: `role` in, `safety` out); [13-glossary.md](13-glossary.md)
(`role`, `kind`, `frontend`); [14-schemas.md](14-schemas.md) (§1, §4);
[12-roadmap.md](12-roadmap.md) ("Exporters for other proof assistants" →
"a frontend, `Backend` and `Source`, for another proof assistant");
[README.md](../README.md) of this folder (row 15). Keep the existing style:
short, plain, no marketing.

## 8. Out of scope

Not part of this change, do not add:
transfer of signatures between different declarations; evidence theorems;
citation conventions; change classification; verifiable signatures; a second
frontend; any CI mechanism; any new command or flag; any change to records.

## 9. Amendment (same day): the hashed graph is a store object

Decided after §1–§8 were written; it supersedes them where they differ.

**Why.** Validity is arithmetic over claim hashes and records. Today `status`
re-hashes an export when the cache lacks it, and hashing needs the Lean
toolchain (`Meta`, for proof erasure). So a service that only shows states would
need a toolchain. Store the hashed graph instead, and `status` needs no proof
assistant at all.

**What changes.**

- The cache (`.leanblame/cache/`) becomes a kind of store object: `graphs`, at
  `.leanblame/store/graphs/<exportHex>-<boundaryHex>.json`, schema
  `leanblame.graph.1`. Keyed by export and boundary list as the cache is today
  (the one store kind that is keyed rather than content-addressed; say so in the
  `Store` module comment). Written by `export`, swept with the exports exactly
  as the cache is today. Same content as §5 "Cache" (string names; a node is
  `name, kind, role, uparams, type, body, informal, deps, own, spec, claim`;
  `axioms`; the boundary list's names for the match check; the `Backend`'s
  `standard`, `incomplete` and `checker`). The cache schema id
  `leanblame.cache.3` is not used.
- `status`, `blame`, `sign`, `validate` take no `Backend`. They read graphs from
  the store and never hash. The `standard` and `incomplete` names of the status
  rule, and the release manifest's `checker`, come from the graph, which
  `export` writes from the `Backend`. Current graph missing: fail with
  `no graph for the current export; run leanblame export`. Graph of an old
  export (named by a record) missing: `warning: record <id>: no graph for export
  <hash>; causes unknown`, as today when the export itself is missing.
- `export` takes the `Backend` (`source`, then the core hashing) and writes the
  graph. `release` takes the `Backend` for `kernelAccepts`. `equiv` is in the
  Lean frontend; it reads old and new graphs from the store like `status` and
  fails with a clear message if one is missing.
- `Backend.source` is therefore used by `export` only. Keep the structure as in
  §2.5.

**Soundness, per the trust model.** Validity compares record claims with the
graph of the current code. That graph is computed by whoever judges (the
developer's `export`; in the web, the institution's service running `export`),
never taken from a file someone else committed. Old graphs only explain causes
and show diffs; they cannot change a state. `equiv` keeps needing the old
export, since it needs terms. The graph has the same standing as the export
today: a derived artifact anyone can reproduce from the code.

**Not now.** Committing graphs to git next to records (so validity needs no
build at all) is a later decision.

**Docs.** [04-architecture.md](04-architecture.md): "Storage" (graphs are store
objects, the cache paragraph goes), "Platform" (`status`, `blame`, `sign`,
`validate` need no toolchain; `export`, `equiv`, `release` do). This file's §3
table: `Status`, `Sign`, `Validate` take no `Backend`; `Release` takes it for the
kernel gate; `Cache` becomes the `graphs` part of `Store` (or a `Graph` store
module), schema `leanblame.graph.1`.

## 10. Amendment (2026-10-26): ids, strict files, a complete status

Decided with the owner; it supersedes §1–§9 where they differ.

- Records name declarations by id (`leanblame.record.2`, [05-records.md](05-records.md)).
  The ledger, `history`, `status` and `blame` go by id, so an approval follows a
  rename; `compare` finds the old node by the name the record gives. A
  declaration without an id of its own (a structure's field, a blueprint label's
  other declarations) has its parent's id and its name under the parent.
- Every JSON file LeanBlame writes has a schema id and is read strictly: a
  missing or an unknown key is an error. A graph is checked for completeness when
  it is read. A failure of proof erasure or of the statement printer stops
  `export`; nothing falls back to a default.
- `Decl` has `module`, never hashed. `export` builds the `Source`, since only it
  has the environment that knows modules; `Backend` has no `source`.
- The boundary list holds the declarations only (`leanblame.boundary.4`);
  `.leanblame/current` holds the commit, toolchain and dependencies. A graph is
  keyed by the store hashes of its export and boundary list (`leanblame.graph.2`).
- `status --json` (`leanblame.status.6`, [14-schemas.md](14-schemas.md)) carries
  everything a viewer needs, so no viewer computes it again: toolchain,
  dependencies, what the lakefile requires, modules with their imports and
  the hash of each sorried copy, standard axioms, every record, each approval's
  standing, each declaration's untagged dependencies with their modules, the
  untagged declarations of the library that tagged ones use, and the unpermitted
  axioms. `change` is `null` when the graph of the last live approval is not in
  this store; there is no warning. With `--json`, nothing goes to stderr.
