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

A tagged declaration needs a docstring; the docstring is what the reviewer
approves. Tagging a `structure` or `inductive` also tags its constructors and
projections.

A declaration of another module, also of a library you do not own, is tagged
after the fact, as `attribute [simp]` does: `attribute [trusted] Name`, in a
library of yours that you name with `--lib`. A declaration has one tag. When the
library renames it with a deprecated alias (`@[deprecated] alias old := new`),
the tag and its id follow, with a warning to write the new name; a rename
without an alias stops the build at the tag.

```
lake exe leanblame id                          # write an id into each @[trusted]
lake exe leanblame export                      # build and export the library
lake exe leanblame sign --signer local:alice   # one approve record per module
lake exe leanblame status                      # every tagged declaration: valid
```

`id` turns `@[trusted]` into `@[trusted "3f2b8c1e-…"]`, and `attribute
[trusted] Name` into `attribute [trusted "3f2b8c1e-…"] Name`: a random id that
stays when the declaration is renamed. Cite a declaration by its id. Commit the change.
`export` refuses a tag without an id. `sign` needs an export of committed
files: with uncommitted changes, the export names no commit.

Instead of `@[trusted]`, `export --boundary FILE` reads a verso-blueprint
`blueprint-manifest.json`. A label is the id of the first declaration it names;
its other declarations point to that one.

## Commands

Run in the library root as `lake exe leanblame <command>`.

| Command | Does |
|---------|------|
| `init` | Create `leanblame.toml`, `records/`. |
| `export [--boundary FILE] [--lib NAME]` | Build, export the library, write the list of tagged declarations. |
| `id [--lib NAME]` | Write a random id into each tag of the library that has none. |
| `status [--json]` | Per tagged declaration: `valid`, `outdated` or `unsigned`, and the cause of any change. |
| `diff --from RECORD [--to RECORD] [--json] [NAME\|ID...]` | What changed between two sign-offs, or a sign-off and now, as the kernel sees it; with the old and new text. |
| `blame NAME\|ID` | Who signed it, when, at which hash. |
| `sign --signer local:NAME [--module M] [--note TEXT] [NAME\|ID...]` | Write an approve record (default: one per module of the library). |
| `sign --withdraw RECORD --signer local:NAME [--constants A,B] [--note TEXT]` | Withdraw your own record, or some of its declarations (names or ids). |
| `equiv [NAME\|ID...]` | Kernel check that old and new are definitionally equal, for declarations outdated only by an untagged change. |
| `challenge NAME\|ID... --out DIR` | Write the comparator challenge of these theorems: what they need from the library and nothing else, and their statements with proofs `sorry`. |
| `challenge --graph` | Print the piece graph that challenges are cut from. |
| `challenge --check DIR` | Check that each tagged declaration in the challenge has the library's hash. |
| `validate [--base-ref REF]` | Check record files: schema, signer authority, no edits or deletions since `REF`. |
| `release --tag TAG [--out FILE]` | Signoff and kernel gates, axiom report, manifest. |

Example `status` output:

```
MyLib.energy outdated change=own-body:MyLib.energy;untagged:MyLib.double
MyLib.energy_even valid
2 tagged: 1 valid, 1 outdated, 0 unsigned; 0 blocked
```

Causes: `own-text`, `own-body`, `dep-spec` (a tagged dependency's name, type or
docstring), `cut-moved` (a dependency gained or lost its tag), `untagged`.

## Records and policy

Records are TOML files in `records/`, named by the SHA-256 of their bytes,
never edited. They name declarations by id, so a sign-off follows a rename.
`leanblame.toml` sets the policy, every key required: `records` directories,
`exclude` (records the library refuses to count), `required_signers`,
`allowed_signers`. From the terminal, `sign` writes `local:` signer ids; a service that
writes records with login-backed ids (OpenVouch) is not built yet.

`.leanblame/` holds the object store (exports, boundary lists, graphs, proofs, manifests). It is
local and ignored by git.

## Development

```
cd cli && lake build && bash test/run.sh
```

Design: [trust-model.md](trust-model.md), [docs/decisions.md](docs/decisions.md),
[docs/schemas.md](docs/schemas.md).
