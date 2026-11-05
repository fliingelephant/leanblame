/-
The object store (docs/decisions.md, Storage): `.leanblame/store/<kind>/<hex>`, where
`<hex>` is the SHA-256 of the file's bytes and `<kind>` one directory per kind of object: exports
(each the list of a build's modules), the files of the modules that are not trusted, boundary lists,
listings of a library's own constants, `equiv` proofs (exports as `leanexport` writes them), release
manifests and piece graphs (`Pieces`). Two kinds are keyed by what made them: graphs, exports hashed
against boundary lists (`Graph`), as `graphs/<export hex>-<boundary hex>.json`; and module keys,
`module-keys/<key hex>`, each the hash of the module file made from that key (`Export.moduleKey`).

One small local file points into it: `.leanblame/current` (JSON), the export, boundary list,
constant listing and piece graph of the last `export` run, with the commit, toolchain and
dependencies it was made from. `equiv` writes evidence files next to it,
`.leanblame/equiv/evidence/<claim hex>.json`. `export` sweeps: an export, boundary list or listing
that neither the current pointer nor a record names is deleted, so are the module files no kept
export lists, the module keys of an earlier build, the graphs of a deleted export, a piece graph the
current pointer does not name, evidence for a claim that is no longer current, and a proof that
neither evidence nor a record names. Every JSON file here is read strictly: an unknown or missing
key is an error.
-/
import LeanBlame.Core.Schema

namespace LeanBlame.Store

def dir (root : System.FilePath) : System.FilePath := root / ".leanblame"

def objectsDir (root : System.FilePath) : System.FilePath := dir root / "store"

/-- The kinds of object, one directory each. -/
inductive Kind where
  | exports | modules | moduleKeys | boundaries | owned | proofs | manifests | graphs | pieces
  deriving BEq, Repr

def Kind.dir : Kind → String
  | .exports => "exports"
  | .modules => "modules"
  | .moduleKeys => "module-keys"
  | .boundaries => "boundaries"
  | .owned => "owned"
  | .proofs => "proofs"
  | .manifests => "manifests"
  | .graphs => "graphs"
  | .pieces => "pieces"

def kindDir (root : System.FilePath) (k : Kind) : System.FilePath := objectsDir root / k.dir

def objectPath (root : System.FilePath) (k : Kind) (hash : String) : System.FilePath :=
  kindDir root k / hashHex hash

/-- Move a finished file, whose SHA-256 is `hex`, into the store; returns `sha256:<hex>`. -/
def putFile (root : System.FilePath) (k : Kind) (tmp : System.FilePath) (hex : String) : IO String := do
  let dest := kindDir root k / hex
  IO.FS.createDirAll (kindDir root k)
  if ← dest.pathExists then IO.FS.removeFile tmp else IO.FS.rename tmp dest
  return mkHash hex

/-- Store a string; returns `sha256:<hex>`. -/
def putString (root : System.FilePath) (k : Kind) (contents : String) : IO String := do
  let hex := Sha256.hexOfString contents
  IO.FS.createDirAll (kindDir root k)
  Lake.writeFileIfNew (kindDir root k / hex) contents
  return mkHash hex

/-- A fresh temporary path inside the store directory (same file system as the objects). -/
def tmpPath (root : System.FilePath) (tag : String) : IO System.FilePath := do
  IO.FS.createDirAll (objectsDir root)
  let n ← IO.monoNanosNow
  return objectsDir root / s!".tmp-{tag}-{n}"

/-- The file of object `hash` of kind `k`; an error when the store lacks it. -/
def objectFile (root : System.FilePath) (k : Kind) (hash : String) : IO System.FilePath := do
  let p := objectPath root k hash
  unless ← p.pathExists do fail s!"{k.dir} object {hash} is not in the store {objectsDir root}"
  return p

def readString (root : System.FilePath) (k : Kind) (hash : String) : IO String := do
  IO.FS.readFile (← objectFile root k hash)

/-- The modules of export `hash` that are not trusted, in import order, each with the hash of its
file. -/
def exportModules (root : System.FilePath) (hash : String) : IO (Array (String × String)) := do
  readJson (← objectFile root .exports hash) fun j => do
    let o ← JsonObj.read j "export" ["trusted", "modules"]
    let entries (k field : String) : Except String (Array (String × String)) := do
      (← o.get (Array Lean.Json) k).mapM fun m => do
        let mo ← JsonObj.read m s!"export.{k}" ["name", field]
        let h ← mo.get String field
        unless isHash h do throw s!"export.{k}: `{h}` is not a sha256: hash"
        return (← mo.get String "name", h)
    discard <| entries "trusted" "compiled"
    entries "modules" "export"

/-- The hash of the module file made from key `key` (`Export.moduleKey`), if the store has the key. -/
def moduleFile? (root : System.FilePath) (key : String) : IO (Option String) := do
  let p := objectPath root .moduleKeys key
  unless ← p.pathExists do return none
  let e := strTrim (← IO.FS.readFile p)
  unless isHash e do fail s!"{p}: `{e}` is not a sha256: hash"
  unless ← (objectPath root .modules e).pathExists do fail s!"{p}: module file {e} is not in the store"
  return some e

/-- Record that key `key` made the module file `e`. -/
def putModuleKey (root : System.FilePath) (key e : String) : IO Unit :=
  writeFileMkdirs (objectPath root .moduleKeys key) (e ++ "\n")

/-- Boundary list `hash`, from the object store. -/
def readBoundary (root : System.FilePath) (hash : String) : IO BoundaryList := do
  readJson (← objectFile root .boundaries hash) BoundaryList.fromJson?

/-- Delete every file of `d` whose name is not in `keep`; returns how many. -/
def sweepDir (d : System.FilePath) (keep : Std.HashSet String) : IO Nat := do
  unless ← d.isDir do return 0
  let mut n := 0
  for e in ← d.readDir do
    unless keep.contains e.fileName do
      IO.FS.removeFile e.path
      n := n + 1
  return n

/-- Delete every object of kind `k` whose hex digest is not in `keep`; returns how many. -/
def sweep (root : System.FilePath) (k : Kind) (keep : Std.HashSet String) : IO Nat :=
  sweepDir (kindDir root k) keep

/-- The last `export`: its export, boundary list and listing of the constants the library defines;
the library's own modules and the piece graph its challenges are cut from; and what it was made
from: the commit (`none` with uncommitted changes, which cannot be signed), the toolchain and the
commits of git dependencies. -/
structure Current where
  exportHash : String
  boundary : String
  owned : String
  modules : Array String
  pieces : String
  commit : Option String
  toolchain : String
  deps : Array (String × String)

instance : Lean.ToJson Current where
  toJson c := Lean.Json.mkObj [("export", c.exportHash), ("boundary", c.boundary), ("owned", c.owned),
    ("modules", Lean.toJson c.modules), ("pieces", c.pieces), ("commit", Lean.toJson c.commit),
    ("toolchain", c.toolchain), ("deps", stringsJson c.deps)]

def Current.fromJson? (j : Lean.Json) : Except String Current := do
  let o ← JsonObj.read j "current"
    ["export", "boundary", "owned", "modules", "pieces", "commit", "toolchain", "deps"]
  let c : Current := {
    exportHash := ← o.get String "export", boundary := ← o.get String "boundary"
    owned := ← o.get String "owned", modules := ← o.get (Array String) "modules", pieces := ← o.get String "pieces"
    commit := ← o.get (Option String) "commit", toolchain := ← o.get String "toolchain"
    deps := ← o.getStrings "deps" }
  for (k, h) in [("export", c.exportHash), ("boundary", c.boundary), ("owned", c.owned), ("pieces", c.pieces)] do
    unless isHash h do throw s!"current.{k}: `{h}` is not a sha256: hash"
  return c

def currentPath (root : System.FilePath) : System.FilePath := dir root / "current"

def writeCurrent (root : System.FilePath) (c : Current) : IO Unit :=
  writeFileMkdirs (currentPath root) (jsonText c)

def readCurrent (root : System.FilePath) : IO Current := do
  unless ← (currentPath root).pathExists do fail s!"no export yet: run `leanblame export` first"
  readJson (currentPath root) Current.fromJson?

def evidenceDir (root : System.FilePath) : System.FilePath := dir root / "equiv" / "evidence"

/-- What `equiv` proved: that declaration `id` at claim `claim` means what the approve record
`oldRecord` meant, by the solution export `proof`. -/
structure Evidence where
  id : String
  claim : String
  oldRecord : String
  proof : String

instance : Lean.ToJson Evidence where
  toJson e := Lean.Json.mkObj [("id", e.id), ("claim", e.claim),
    ("old_record", e.oldRecord), ("proof", e.proof)]

def Evidence.fromJson? (j : Lean.Json) : Except String Evidence := do
  let o ← JsonObj.read j "evidence" ["id", "claim", "old_record", "proof"]
  let e : Evidence := { id := ← o.get String "id", claim := ← o.get String "claim"
                        oldRecord := ← o.get String "old_record", proof := ← o.get String "proof" }
  for (k, h) in [("claim", e.claim), ("old_record", e.oldRecord), ("proof", e.proof)] do
    unless isHash h do throw s!"evidence.{k}: `{h}` is not a sha256: hash"
  return e

/-- Where the evidence for claim `claim` is: `<claim hex>.json`. A claim belongs to one declaration,
since its name is hashed. -/
def evidencePath (root : System.FilePath) (claim : String) : System.FilePath :=
  evidenceDir root / s!"{hashHex claim}.json"

def readEvidence (path : System.FilePath) : IO Evidence :=
  readJson path Evidence.fromJson?

/-- The evidence for `claim`, if `equiv` wrote one. -/
def evidence? (root : System.FilePath) (claim : String) : IO (Option Evidence) := do
  let p := evidencePath root claim
  unless ← p.pathExists do return none
  let e ← readEvidence p
  unless e.claim == claim do fail s!"{p}: the evidence is for claim {e.claim}, not {claim}"
  return some e

/-- The proofs every evidence file names, as hex digests. -/
def evidenceProofs (root : System.FilePath) : IO (Std.HashSet String) := do
  let d := evidenceDir root
  unless ← d.isDir do return {}
  let mut out : Std.HashSet String := {}
  for e in ← d.readDir do
    out := out.insert (hashHex (← readEvidence e.path).proof)
  return out

end LeanBlame.Store
