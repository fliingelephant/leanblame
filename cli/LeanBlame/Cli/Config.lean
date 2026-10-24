/-
`leanblame.toml`, the library's trust policy (docs/04-architecture.md, Config).
-/
import Lake.Toml
import LeanBlame.Cli.Schema

namespace LeanBlame

structure Config where
  /-- Records repositories. Local directories, relative to the library root. -/
  records : Array String := #["records/"]
  /-- Approve records this library refuses to count. Withdrawals cannot be excluded. -/
  exclude : Array String := #[]
  conventions : Option String := none
  providers : Array String := #[]
  /-- Distinct live approvals a declaration needs. -/
  requiredSigners : Nat := 1
  /-- `none`: any signer. -/
  allowedSigners : Option (Array String) := none
  deriving Inhabited, Repr

def Config.fileName : String := "leanblame.toml"

/-- What `init` writes. -/
def Config.defaultText : String :=
  "# LeanBlame trust policy. See docs/04-architecture.md in the leanblame repository.
records = [\"records/\"]   # records repositories (local directories)
exclude = []              # approve records this library refuses to count
required_signers = 1      # distinct live approvals a declaration needs
allowed_signers = \"any\"   # or a list of provider:id
# conventions = \"MyLib.Conventions\"
# providers = [\"openreview\", \"orcid\", \"github\"]
"

open Lake.Toml (DecodeM Table logDecodeErrorAt) in
/-- Decode a parsed `leanblame.toml`, logging every problem. -/
def Config.decode (t : Table) : DecodeM Config := do
  checkKeys t #["records", "exclude", "conventions", "providers", "required_signers",
    "allowed_signers"] Config.fileName
  let d : Config := {}
  let exclude : Array String ← t.tryDecodeD `exclude d.exclude
  for x in exclude do
    unless isHash x do logDecodeErrorAt (refOf t `exclude) s!"`exclude`: `{x}` is not a sha256: record hash"
  let requiredSigners ← t.tryDecodeD `required_signers d.requiredSigners
  if requiredSigners < 1 then
    logDecodeErrorAt (refOf t `required_signers) "`required_signers` must be at least 1"
  let allowedSigners ← match t.find? `allowed_signers with
    | none | some (.string _ "any") => pure none
    | some (.string ref s) =>
      logDecodeErrorAt ref s!"`allowed_signers = \"{s}\"`: a records repository as the signer list is not implemented yet; use \"any\" or a list of provider:id"
      pure none
    | some v =>
      let ids : Array String ← Lake.Toml.tryDecodeD #[] (Lake.decodeToml v)
      for id in ids do
        unless isSignerId id do logDecodeErrorAt v.ref s!"`allowed_signers`: `{id}` is not provider:id"
      pure (some ids)
  return { records := ← t.tryDecodeD `records d.records, exclude
           conventions := ← t.tryDecode? `conventions, providers := ← t.tryDecodeD `providers d.providers
           requiredSigners, allowedSigners }

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
