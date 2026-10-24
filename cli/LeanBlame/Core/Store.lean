/-
The object store (docs/design/04-architecture.md, Storage): `.leanblame/store/<kind>/<hex>`, where
`<hex>` is the SHA-256 of the file's bytes and `<kind>` one directory per kind of object: exports,
boundary lists, listings of a library's own constants, `equiv` proofs (exports too) and release
manifests.

One small local file points into it: `.leanblame/current` (JSON), the export, boundary list and
constant listing of the last `export` run. `equiv` writes evidence files next to it, in
`.leanblame/equiv/evidence/`. `export` sweeps: an export, boundary list or listing that neither the
current pointer nor a record names is deleted, so is evidence for a claim that is no longer current,
and a proof that neither evidence nor a record names.
-/
import LeanBlame.Cli.Util

namespace LeanBlame.Store

def dir (root : System.FilePath) : System.FilePath := root / ".leanblame"

def objectsDir (root : System.FilePath) : System.FilePath := dir root / "store"

/-- The kinds of object, one directory each. -/
inductive Kind where
  | exports | boundaries | owned | proofs | manifests
  deriving BEq, Repr

def Kind.dir : Kind → String
  | .exports => "exports"
  | .boundaries => "boundaries"
  | .owned => "owned"
  | .proofs => "proofs"
  | .manifests => "manifests"

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

def readString (root : System.FilePath) (k : Kind) (hash : String) : IO String := do
  let p := objectPath root k hash
  unless ← p.pathExists do
    fail s!"{k.dir} object {hash} is not in the store {objectsDir root}"
  IO.FS.readFile p

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

/-- The export and boundary list of the last `export`, the library's own modules, and the
object listing the constants defined in them. -/
structure Current where
  exportHash : String
  boundary : String
  modules : Array String
  owned : String
  deriving Lean.ToJson, Lean.FromJson

def currentPath (root : System.FilePath) : System.FilePath := dir root / "current"

def writeCurrent (root : System.FilePath) (c : Current) : IO Unit :=
  writeFileMkdirs (currentPath root) (jsonText c)

def readCurrent (root : System.FilePath) : IO Current := do
  let some text ← readFileIfExists (currentPath root)
    | fail s!"no export yet: run `leanblame export` first"
  match Lean.Json.parse text >>= Lean.fromJson? with
  | .ok (c : Current) => if isHash c.exportHash && isHash c.boundary then return c
  | .error _ => pure ()
  fail s!"{currentPath root} is malformed; run `leanblame export`"

def evidenceDir (root : System.FilePath) : System.FilePath := dir root / "equiv" / "evidence"

/-- Where `equiv` records that declaration `name` at claim hash `claim` means what its last live
approval meant: `<sha256 of "name claim">.json`, naming the proof (`evidence`) and the approve
record it was compared with (`old_record`). -/
def evidencePath (root : System.FilePath) (name claim : String) : System.FilePath :=
  evidenceDir root / s!"{Sha256.hexOfString s!"{name} {claim}"}.json"

/-- The proof and record an evidence file names. -/
def evidenceFields (text : String) : Option (String × String) :=
  let field (k : String) := (Lean.Json.parse text >>= (·.getObjValAs? String k)).toOption.filter isHash
  match field "evidence", field "old_record" with
  | some proof, some record => some (proof, record)
  | _, _ => none

/-- The evidence for `name` at `claim`, if `equiv` wrote one. -/
def evidence? (root : System.FilePath) (name claim : String) : IO (Option (String × String)) := do
  let some text ← readFileIfExists (evidencePath root name claim) | return none
  return evidenceFields text

/-- The proofs every evidence file names, as hex digests. -/
def evidenceProofs (root : System.FilePath) : IO (Std.HashSet String) := do
  let d := evidenceDir root
  unless ← d.isDir do return {}
  let mut out : Std.HashSet String := {}
  for e in ← d.readDir do
    if let some (proof, _) := evidenceFields (← IO.FS.readFile e.path) then
      out := out.insert (hashHex proof)
  return out

end LeanBlame.Store
