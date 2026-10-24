/-
The object store (docs/04-architecture.md, Storage): exports, boundary lists and
status logs, each in `.leanblame/store/<hex>` where `<hex>` is the SHA-256 of
the file's bytes.

One small local file points into it: `.leanblame/current` (JSON), the export
and boundary list of the last `export` run.
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
  let dest := objectsDir root / hex
  unless ← dest.pathExists do
    writeFileMkdirs dest contents
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

end LeanBlame.Store
