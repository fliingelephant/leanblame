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

Requires Lean `v4.35.0`, the version in `cli/lean-toolchain`.

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

```
lake exe leanblame export                      # build and export the library
lake exe leanblame sign --signer local:alice   # one approve record per module
lake exe leanblame status                      # every tagged declaration: valid
```

Without `@[trusted]`, `export --boundary FILE` takes a verso-blueprint
`blueprint-manifest.json` or a TOML list (`schema = "leanblame.manual.1"`,
`[declarations]` with name = text).

## Commands

Run in the library root as `lake exe leanblame <command>`.

| Command | Does |
|---------|------|
| `init` | Create `leanblame.toml`, `records/`. |
| `export [--boundary FILE] [--lib NAME]` | Build, export the library, write the list of tagged declarations. |
| `status [--json]` | Per tagged declaration: `valid`, `outdated` or `unsigned`, and the cause of any change. |
| `blame NAME` | Who signed `NAME`, when, at which hash. |
| `sign [--signer local:NAME] [--module M] [--note TEXT] [NAME...]` | Write an approve record (default: one per module of the library). |
| `sign --withdraw RECORD [--constants A,B] [--note TEXT]` | Withdraw your own record, or some of its constants. |
| `equiv [NAME...]` | Kernel check that old and new are definitionally equal, for declarations outdated only by an untagged change. |
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
never edited. `leanblame.toml` sets the policy: `records` directories,
`exclude` (records the library refuses to count), `required_signers`,
`allowed_signers`. From the terminal, `sign` writes `local:` signer ids; a sign
server with login-backed ids is not built yet.

`.leanblame/` holds the object store (exports, boundary lists, graphs, proofs, manifests). It is
local and ignored by git.

## Development

```
cd cli && lake build && bash test/run.sh
```

Design documents and schemas: [docs/design/](docs/design/README.md).
