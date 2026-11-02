/-
`leanblame.toml`, the library's trust policy (docs/decisions.md, Config).
-/
import Lake.Toml
import LeanBlame.Core.Schema

namespace LeanBlame

structure Config where
  /-- Records directories, relative to the library root, without a trailing slash (`records/` and
  `records` name the same one). Remote repositories are not supported yet. -/
  records : Array String
  /-- Approve records this library refuses to count. Withdrawals cannot be excluded. -/
  exclude : Array String
  /-- Distinct live approvals a declaration needs. -/
  requiredSigners : Nat
  /-- `none`: any signer. -/
  allowedSigners : Option (Array String)
  /-- The package's libraries to read; empty: its default `lean_lib` targets, else all its `lean_lib`s. -/
  libraries : Array String
  /-- A verso-blueprint `blueprint-manifest.json` that names the tagged declarations instead of
  `@[trusted]`, relative to the library root. -/
  boundary : Option String
  /-- The packages whose declarations enter claims by their statement alone, with the packages they
  require; `none`: `mathlib` when the workspace has it. Lean's own declarations always do. -/
  trusted : Option (Array String)
  deriving Inhabited, Repr

def Config.fileName : String := "leanblame.toml"

/-- What `init` writes. -/
def Config.defaultText : String :=
  "# LeanBlame trust policy. See docs/decisions.md in the leanblame repository.
records = [\"records/\"]   # records repositories (local directories)
exclude = []              # approve records this library refuses to count
required_signers = 1      # distinct live approvals a declaration needs
allowed_signers = \"any\"   # or a list of provider:id

# The package's libraries to read (default: its default lean_lib targets). To tag a library you do not
# own, add a library of yours holding `attribute [trusted] Name` commands and list both:
# libraries = [\"Lib\", \"Tags\"]
# A verso-blueprint blueprint-manifest.json that names the tagged declarations instead of @[trusted],
# relative to this file:
# boundary = \"blueprint-manifest.json\"
# The packages whose declarations enter claims by their statement alone, unreviewed, with the packages
# they require (default: mathlib, when the package requires it). Lean's own declarations always do.
# trusted = [\"mathlib\"]
"

open Lake.Toml (DecodeM Table logDecodeErrorAt) in
/-- Decode a parsed `leanblame.toml`, logging every problem. Every key is required but `libraries`,
`boundary` and `trusted`. -/
def Config.decode (t : Table) : DecodeM Config := do
  checkKeys t #["records", "exclude", "required_signers", "allowed_signers", "libraries", "boundary", "trusted"]
    Config.fileName
  let records : Array String ← t.tryDecode `records
  if (t.find? `records).isSome && records.isEmpty then
    logDecodeErrorAt (refOf t `records) "`records` lists no records directory"
  for r in records do
    if (r.splitOn "://").length > 1 || r.startsWith "git@" then
      logDecodeErrorAt (refOf t `records) s!"`records`: {r}: only local directories are supported"
  let exclude : Array String ← t.tryDecode `exclude
  for x in exclude do
    unless isHash x do logDecodeErrorAt (refOf t `exclude) s!"`exclude`: `{x}` is not a sha256: record hash"
  let requiredSigners : Nat ← t.tryDecode `required_signers
  if requiredSigners < 1 then
    logDecodeErrorAt (refOf t `required_signers) "`required_signers` must be at least 1"
  let allowedSigners ← match t.find? `allowed_signers with
    | some (.string _ "any") => pure none
    | some (.string ref s) =>
      logDecodeErrorAt ref s!"`allowed_signers = \"{s}\"`: a records repository as the signer list is not implemented yet; use \"any\" or a list of provider:id"
      pure none
    | some v =>
      let ids : Array String ← Lake.Toml.tryDecodeD #[] (Lake.decodeToml v)
      for id in ids do
        unless isSignerId id do logDecodeErrorAt v.ref s!"`allowed_signers`: `{id}` is not provider:id"
      pure (some ids)
    | none =>
      logDecodeErrorAt .missing "missing required key: allowed_signers (\"any\" or a list of provider:id)"
      pure none
  let libraries : Array String ← t.tryDecodeD `libraries #[]
  let boundary : Option String ← t.tryDecode? `boundary
  let trusted : Option (Array String) ← t.tryDecode? `trusted
  return { records := records.map fun r => if r.length > 1 then (r.dropSuffix "/").copy else r, exclude
           requiredSigners, allowedSigners, libraries, boundary, trusted }

/-- Parse the text of a `leanblame.toml`; `path` names it in messages. -/
def Config.parse (contents path : String) : IO (Except String Config) :=
  return (← parseToml contents path Config.decode).mapError ("\n".intercalate ·.toList)

def Config.load (root : System.FilePath) : IO Config := do
  let path := root / Config.fileName
  unless ← path.pathExists do
    fail s!"{path} not found; run `leanblame init` first"
  match ← Config.parse (← IO.FS.readFile path) path.toString with
  | .ok cfg => return cfg
  | .error e => fail s!"{path}: {e}"

def Config.allows (cfg : Config) (signer : String) : Bool :=
  match cfg.allowedSigners with
  | none => true
  | some ids => ids.contains signer

end LeanBlame
