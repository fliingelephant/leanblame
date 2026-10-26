/-
Small helpers shared by the commands: strings, hashes, JSON, files, processes.
-/
import Lake.Util.IO
import Lean.Data.Json
import LeanBlame.Core.Sha256

namespace LeanBlame

/-! Strings (Lean 4.35 returns slices from most `String` operations). -/

def strTrim (s : String) : String := s.trimAscii.copy

/-! Arrays. -/

/-- `xs` without repetitions, keeping first occurrences in order. -/
def dedup [BEq α] [Hashable α] (xs : Array α) : Array α := Id.run do
  let mut seen : Std.HashSet α := {}
  let mut out := #[]
  for x in xs do
    unless seen.contains x do
      seen := seen.insert x
      out := out.push x
  return out

/-! Hashes: `sha256:` plus 64 lowercase hex digits. -/

def hashPrefix : String := "sha256:"

def isLowerHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

def isHexDigest (h : String) : Bool := h.length == 64 && h.all isLowerHex

def isHash (s : String) : Bool :=
  match s.dropPrefix? hashPrefix with
  | some hex => isHexDigest hex.copy
  | none => false

def mkHash (hex : String) : String := hashPrefix ++ hex

/-- The hex digest of a `sha256:` hash, or the argument itself if it is a bare digest. -/
def hashHex (s : String) : String := (s.dropPrefix hashPrefix).copy

def sha256OfBytes (b : ByteArray) : String := mkHash (Sha256.hexOfBytes b)

/-! JSON. Key order is not part of any schema. Every key is written, `null` for none, and read
strictly: a missing or an unknown key is an error. -/

/-- The text the commands write: pretty-printed JSON and a final newline. -/
def jsonText [Lean.ToJson α] (a : α) : String := (Lean.toJson a).pretty ++ "\n"

/-- A JSON object whose keys are exactly the expected ones; `what` names it in errors. -/
structure JsonObj where
  what : String
  fields : Std.TreeMap.Raw String Lean.Json

/-- `j` as an object with exactly the keys `keys`: a missing or an unknown key is an error. -/
def JsonObj.read (j : Lean.Json) (what : String) (keys : List String) : Except String JsonObj := do
  let .obj fields := j | throw s!"{what}: not a JSON object"
  for (k, _) in fields do
    unless keys.contains k do throw s!"{what}: unknown key `{k}`"
  for k in keys do
    unless fields.contains k do throw s!"{what}: missing key `{k}`"
  return { what, fields }

/-- Key `k`, decoded; `null` is a value only for an `Option`. -/
def JsonObj.get (o : JsonObj) (α : Type) [Lean.FromJson α] (k : String) : Except String α := do
  let some v := o.fields.get? k | throw s!"{o.what}: missing key `{k}`"
  (Lean.fromJson? v).mapError (s!"{o.what}.{k}: " ++ ·)

/-- Key `k`, an object of strings, as pairs in key order. -/
def JsonObj.getStrings (o : JsonObj) (k : String) : Except String (Array (String × String)) := do
  let kvs ← ((← o.get Lean.Json k).getObj?).mapError (s!"{o.what}.{k}: " ++ ·)
  kvs.toList.toArray.mapM fun (k', v) => return (k', ← v.getStr?.mapError (s!"{o.what}.{k}.{k'}: " ++ ·))

/-- Fail unless key `schema` is `id`. -/
def JsonObj.schema (o : JsonObj) (id : String) : Except String Unit := do
  let s ← o.get String "schema"
  unless s == id do throw s!"{o.what}: schema is `{s}`, expected `{id}`"

/-- The JSON object of `kvs`, a string to string map. -/
def stringsJson (kvs : Array (String × String)) : Lean.Json :=
  Lean.Json.mkObj (kvs.toList.map fun (k, v) => (k, Lean.Json.str v))

/-! Errors. -/

/-- A user-facing failure: printed without a stack, exit code 1. -/
def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)

/-! Processes. -/

/-- Run a command, copying its stdout to our stderr as it comes (our stdout carries results); fail
with `what` on a non-zero exit. Its stderr is ours; `env` is added to our environment. -/
partial def runToStderr (cmd : String) (args : Array String) (cwd : Option System.FilePath)
    (what : String) (env : Array (String × Option String) := #[]) : IO Unit := do
  let child ← IO.Process.spawn { cmd, args, cwd, env, stdin := .null, stdout := .piped }
  let out ← IO.getStderr
  let rec copy : IO Unit := do
    let chunk ← child.stdout.read (1024 * 1024)
    unless chunk.isEmpty do
      out.write chunk
      out.flush
      copy
  copy
  let code ← child.wait
  if code != 0 then fail s!"{what} failed (exit {code})"

/-! Files. -/

def readFileIfExists (p : System.FilePath) : IO (Option String) := do
  if ← p.pathExists then return some (← IO.FS.readFile p) else return none

/-- Write a file, creating parent directories. -/
def writeFileMkdirs (p : System.FilePath) (contents : String) : IO Unit := do
  Lake.createParentDirs p
  IO.FS.writeFile p contents

end LeanBlame
