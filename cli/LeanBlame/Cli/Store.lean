/-
The object store (docs/design/04-architecture.md, Storage): exports, boundary lists and
status logs, each in `.leanblame/store/<hex>` where `<hex>` is the SHA-256 of
the file's bytes.

One small local file points into it: `.leanblame/current` (JSON), the export
and boundary list of the last `export` run. `equiv` writes evidence files next to
it, in `.leanblame/equiv/evidence/`.
-/
import LeanBlame.Cli.Util

namespace LeanBlame.Store

def dir (root : System.FilePath) : System.FilePath := root / ".leanblame"

def objectsDir (root : System.FilePath) : System.FilePath := dir root / "store"

def objectPath (root : System.FilePath) (hash : String) : System.FilePath :=
  objectsDir root / hashHex hash

/-- Move a finished file, whose SHA-256 is `hex`, into the store; returns `sha256:<hex>`. -/
def putFile (root : System.FilePath) (tmp : System.FilePath) (hex : String) : IO String := do
  let dest := objectsDir root / hex
  IO.FS.createDirAll (objectsDir root)
  if ← dest.pathExists then
    IO.FS.removeFile tmp
  else
    IO.FS.rename tmp dest
  return mkHash hex

/-- Store a string; returns `sha256:<hex>`. -/
def putString (root : System.FilePath) (contents : String) : IO String := do
  let hex := Sha256.hexOfString contents
  IO.FS.createDirAll (objectsDir root)
  Lake.writeFileIfNew (objectsDir root / hex) contents
  return mkHash hex

/-- A fresh temporary path inside the store directory (same file system as the objects). -/
def tmpPath (root : System.FilePath) (tag : String) : IO System.FilePath := do
  IO.FS.createDirAll (objectsDir root)
  let n ← IO.monoNanosNow
  return objectsDir root / s!".tmp-{tag}-{n}"

def readString (root : System.FilePath) (hash : String) : IO String := do
  let p := objectPath root hash
  unless ← p.pathExists do
    fail s!"object {hash} is not in the store {objectsDir root}"
  IO.FS.readFile p

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

/-- Where `equiv` records that declaration `name` at claim hash `claim` means what its last live
approval meant: `<sha256 of "name claim">.json`, naming the proof (`evidence`) and the approve
record it was compared with (`old_record`). -/
def evidencePath (root : System.FilePath) (name claim : String) : System.FilePath :=
  dir root / "equiv" / "evidence" / s!"{Sha256.hexOfString s!"{name} {claim}"}.json"

/-- The evidence for `name` at `claim`, if `equiv` wrote one: the proof hash and the approve record
whose meaning it was compared with. -/
def evidence? (root : System.FilePath) (name claim : String) : IO (Option (String × String)) := do
  let some text ← readFileIfExists (evidencePath root name claim) | return none
  let field (k : String) := (Lean.Json.parse text >>= (·.getObjValAs? String k)).toOption.filter isHash
  return match field "evidence", field "old_record" with
    | some proof, some record => some (proof, record)
    | _, _ => none

end LeanBlame.Store
