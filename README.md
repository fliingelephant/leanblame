# LeanBlame

LeanBlame is `git blame` for the meaning of Lean declarations.

The kernel checks proofs. Humans check semantics. LeanBlame tracks the human
checks, incrementally and with kernel help.

- Tag the declarations that need a human reader with `@[trusted]`.
- A reviewer signs them. Each signature is a file in the repository, bound to a
  hash of the declaration's kernel-level content, proofs excluded.
- After any change to the library or its dependencies, `leanblame status` shows
  which signatures still hold and, for the rest, what changed and who must look
  again.

Requires Lean `v4.35.0`, the version in `cli/lean-toolchain`. Older versions have no
`leanexport` and are not supported.

## Adding LeanBlame to your project

In `lakefile.toml`:

```toml
[[require]]
name = "leanblame"
git = "https://github.com/fliingelephant/leanblame"
rev = "v0.1.0"
subDir = "cli"
```

Then `lake update leanblame` and `lake exe leanblame init`. `init` writes
`leanblame.toml`, an empty `records/`, and adds `.leanblame/` to `.gitignore`.

## Quickstart

```lean
import LeanBlame.Attr

/-- The energy of a chain of `n` sites: two units per site. -/
@[trusted] def energy (n : Nat) : Nat := double n
```

The reviewer approves the docstring with the statement; without a docstring,
the statement is the name and type. Tagging a `structure` or `inductive` also tags its constructors and
projections.

A declaration of another module, also of a library you do not own, is tagged
after the fact, as `attribute [simp]` does: `attribute [trusted] Name`, in a
library of yours that `libraries` in `leanblame.toml` lists. A declaration has one tag. When the
library renames it with a deprecated alias (`@[deprecated] alias old := new`),
the tag and its id follow, with a warning to write the new name; a rename
without an alias stops the build at the tag.

```
lake exe leanblame id                              # tag every declaration, each with an id
lake exe leanblame export                          # build and export the tagged declarations
lake exe leanblame sign --signer local:alice --all # one approve record per module
lake exe leanblame status                          # every tagged declaration: valid
```

Every declaration needs a sign-off, so `id` tags every one. It turns `@[trusted]`
into `@[trusted "3f2b8c1e-…"]`, and `attribute [trusted] Name` into `attribute
[trusted "3f2b8c1e-…"] Name`: a random id that stays when the declaration is
renamed. A declaration with no tag gets `attribute [trusted "…"] Name` at the end
of its module; when a library `libraries` lists declares nothing (the library of
tags of a library you do not own), it gets it there instead. A structure's
projections and what Lean generates come with their parent. Cite a declaration
by its id. Commit the change.
`export` refuses a tag without an id. `sign` needs an export of committed
files: with uncommitted changes, the export names no commit.

Instead of `@[trusted]`, `export` reads the verso-blueprint
`blueprint-manifest.json` that `boundary` in `leanblame.toml` names. A label is the id of the first declaration it names;
its other declarations point to that one.

## Commands

Run in the library root as `lake exe leanblame <command>`.

| Command | Does |
|---------|------|
| `init` | Create `leanblame.toml`, `records/`. |
| `export` | Build, write the list of tagged declarations, export them and what they use. |
| `id` | Tag every declaration of the library, each with a random id. |
| `status [--json]` | Per tagged declaration: `valid`, `outdated` or `unsigned`, and the cause of any change. |
| `diff --from RECORD [--to RECORD] [--json] [NAME\|ID...]` | What changed between two sign-offs, or a sign-off and now, as the kernel sees it; with the old and new text. |
| `blame NAME\|ID` | Who signed it, when, at which hash. |
| `sign --signer local:NAME [--note TEXT] (NAME\|ID... \| --module M \| --all)` | Write approve records, one per module: of the declarations named, of one module, or of the whole library. |
| `withdraw RECORD --signer local:NAME [--note TEXT] [NAME\|ID...]` | Withdraw your own record, or some of its declarations (names or ids). |
| `equiv [NAME\|ID...]` | Kernel check that old and new are definitionally equal, for declarations outdated only by an untagged change. |
| `challenge write NAME\|ID... --out DIR` | Write the `lake comparator` package of these tagged declarations: what they need from the library and nothing else, the theorems' statements with proofs `sorry`, `Solution.lean` to prove them in, and `comparator.json` (the theorems, the permitted axioms). |
| `challenge graph` | Print the piece graph that challenges are cut from. |
| `challenge check DIR` | Build the challenge against the library: each tagged declaration in it has the library's claim hash, or the kernel finds it definitionally equal to the library's. |
| `validate [--base-ref REF]` | Check record files: schema, signer authority, no edits or deletions since `REF`. |
| `release --tag TAG [--out FILE]` | Signoff and kernel gates, axiom report, manifest. |

Example `status` output:

```
MyLib.energy outdated change=own-body:MyLib.energy;untagged:MyLib.double
MyLib.energy_even valid blocked
2 tagged: 1 valid, 1 outdated, 0 unsigned; 1 blocked
```

Causes: `own-text`, `own-body`, `dep-spec` (a tagged dependency's name, type or
docstring), `cut-moved` (a dependency gained or lost its tag), `untagged`.

## Records and policy

Records are TOML files in `records/`, named by the SHA-256 of their bytes,
never edited. They name declarations by id, so a sign-off follows a rename.
`leanblame.toml` sets the policy, every key required: `records` directories,
`exclude` (records the library refuses to count), `required_signers`,
`allowed_signers`; and, optionally, `libraries` (the package's libraries to read),
`boundary` (a blueprint manifest instead of `@[trusted]`) and `trusted` (the packages
whose declarations enter claims by their statement alone, with what they require;
default `mathlib`; Lean's own always do). From the terminal, `sign` writes `local:` signer ids; a service that
writes records with login-backed ids (OpenVouch) is not built yet.

`.leanblame/` holds the object store. It is local and ignored by git.

## Development

```
cd cli && lake build && bash test/run.sh
```

Design: [trust-model.md](trust-model.md), [docs/decisions.md](docs/decisions.md),
[docs/schemas.md](docs/schemas.md).
