/-
`leanblame.toml`, the library's trust policy (docs/04-architecture.md, Config).
-/
import Lake.Toml
import LeanBlame.Cli.Schema

namespace LeanBlame

structure Config where
  /-- Records repositories. Local directories, relative to the library root. -/
  records : Array String := #["records/"]
  /-- Record hashes this library refuses to count. -/
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
exclude = []              # record hashes this library refuses to count
required_signers = 1      # distinct live approvals a declaration needs
allowed_signers = \"any\"   # or a list of provider:id
# conventions = \"MyLib.Conventions\"
# providers = [\"openreview\", \"orcid\", \"github\"]
"

private def keyString (k : Lean.Name) : String :=
  match k with
  | .str .anonymous s => s
  | _ => k.toString (escape := false)

private def strArray (k : String) (v : Lake.Toml.Value) : Except String (Array String) :=
  match v with
  | .array _ vs => vs.mapM fun
    | .string _ s => .ok s
    | _ => .error s!"`{k}` must be a list of strings"
  | _ => .error s!"`{k}` must be a list of strings"

def Config.ofTable (t : Lake.Toml.Table) : Except String Config := do
  let mut cfg : Config := {}
  for (k, v) in t.items do
    match keyString k, v with
    | "records", v => cfg := { cfg with records := ← strArray "records" v }
    | "exclude", v =>
      let xs ← strArray "exclude" v
      for x in xs do
        unless isHash x do throw s!"`exclude`: `{x}` is not a sha256: record hash"
      cfg := { cfg with exclude := xs }
    | "conventions", .string _ s => cfg := { cfg with conventions := some s }
    | "providers", v => cfg := { cfg with providers := ← strArray "providers" v }
    | "required_signers", .integer _ n =>
      if n < 1 then throw "`required_signers` must be at least 1"
      cfg := { cfg with requiredSigners := n.toNat }
    | "allowed_signers", .string _ "any" => cfg := { cfg with allowedSigners := none }
    | "allowed_signers", .string _ s =>
      throw s!"`allowed_signers = \"{s}\"`: a records repository as the signer list is not implemented yet; use \"any\" or a list of provider:id"
    | "allowed_signers", v =>
      let ids ← strArray "allowed_signers" v
      for id in ids do
        unless isSignerId id do throw s!"`allowed_signers`: `{id}` is not provider:id"
      cfg := { cfg with allowedSigners := some ids }
    | key, _ => throw s!"unknown or ill-typed key `{key}`"
  return cfg

/-- Parse the text of a `leanblame.toml`; `path` names it in messages. -/
def Config.parse (contents path : String) : IO (Except String Config) := do
  let ictx := Lean.Parser.mkInputContext contents path
  match ← (Lake.Toml.loadToml ictx).toBaseIO with
  | .error log =>
    let msgs ← log.toList.mapM fun m => m.toString
    return .error ("\n".intercalate msgs)
  | .ok t => return Config.ofTable t

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
