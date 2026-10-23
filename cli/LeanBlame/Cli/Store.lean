/-
The object store (docs/04-architecture.md, Storage): exports, boundary lists and
status logs, each in `.leanblame/store/<hex>` where `<hex>` is the SHA-256 of
the file's bytes.

Two small local files point into it:
* `.leanblame/current`: the export and boundary list of the last `export` run;
* `.leanblame/exports`: one line per `export` run, `<export> <boundary> <commit>`,
  so `status --base A` can find the boundary list exported with export `A`.
-/
import LeanBlame.Cli.Util

namespace LeanBlame.Store

def dir (root : System.FilePath) : System.FilePath := root / ".leanblame"

def objectsDir (root : System.FilePath) : System.FilePath := dir root / "store"

def objectPath (root : System.FilePath) (hash : String) : System.FilePath :=
  objectsDir root / hashHex hash

/-- Move a finished file into the store under its hash; returns `sha256:<hex>`. -/
def putFile (root : System.FilePath) (tmp : System.FilePath) : IO String := do
  let hex ← Sha256.hexOfFile tmp
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

def has (root : System.FilePath) (hash : String) : IO Bool :=
  (objectPath root hash).pathExists

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
  modules : Array String := #[]
  owned : Option String := none

def currentPath (root : System.FilePath) : System.FilePath := dir root / "current"

def writeCurrent (root : System.FilePath) (c : Current) (commit : String) : IO Unit := do
  let owned := match c.owned with
    | some h => s!"owned {h}\n"
    | none => ""
  writeFileMkdirs (currentPath root)
    (s!"export {c.exportHash}\nboundary {c.boundary}\nmodules {" ".intercalate c.modules.toList}\n" ++ owned)
  -- The log keeps one line per (export, boundary list, commit), the latest run last.
  let log := dir root / "exports"
  let line := s!"{c.exportHash} {c.boundary} {commit}"
  let old := ((← readFileIfExists log).getD "" |> strLines).filter (fun l => l != "" && l != line)
  IO.FS.writeFile log ("\n".intercalate (old ++ [line]) ++ "\n")

def readCurrent (root : System.FilePath) : IO Current := do
  let some text ← readFileIfExists (currentPath root)
    | fail s!"no export yet: run `leanblame export` first"
  let mut e := ""
  let mut b := ""
  let mut mods := #[]
  let mut owned := none
  for l in strLines text do
    match l.splitOn " " with
    | ["export", h] => e := h
    | ["boundary", h] => b := h
    | ["owned", h] => owned := some h
    | "modules" :: ms => mods := (ms.filter (· != "")).toArray
    | _ => pure ()
  unless isHash e && isHash b do fail s!"{currentPath root} is malformed; run `leanblame export`"
  return { exportHash := e, boundary := b, modules := mods, owned }

/-- The boundary lists exported together with `exportHash`, from the local export log, latest
first. Docstrings are not in exports, so a docstring edit pairs a new list with the same export. -/
def boundariesForExport (root : System.FilePath) (exportHash : String) : IO (Array String) := do
  let some text ← readFileIfExists (dir root / "exports") | return #[]
  let mut out := #[]
  for l in (strLines text).reverse do
    match l.splitOn " " with
    | e :: b :: _ => if e == exportHash && !out.contains b then out := out.push b
    | _ => pure ()
  return out

end LeanBlame.Store
