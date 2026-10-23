/-
Small helpers shared by the commands: strings, hashes, JSON, files, processes.
-/
import Lean.Data.Json
import LeanBlame.Cli.Sha256

namespace LeanBlame

/-! Strings (Lean 4.35 returns slices from most `String` operations). -/

def strDrop (s : String) (n : Nat) : String := (s.drop n).copy

def strTrim (s : String) : String := s.trimAscii.copy

def strLines (s : String) : List String :=
  (s.splitOn "\n").map fun l => if l.endsWith "\r" then (l.dropEnd 1).copy else l

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
  s.startsWith hashPrefix && isHexDigest (strDrop s hashPrefix.length)

def mkHash (hex : String) : String := hashPrefix ++ hex

/-- The hex digest of a `sha256:` hash, or the argument itself if it is a bare digest. -/
def hashHex (s : String) : String :=
  if s.startsWith hashPrefix then strDrop s hashPrefix.length else s

def sha256OfString (s : String) : String := mkHash (Sha256.hexOfString s)

def sha256OfBytes (b : ByteArray) : String := mkHash (Sha256.hexOfBytes b)

/-! JSON. Key order is not part of any schema. -/

/-- The text the commands write: pretty-printed JSON and a final newline. -/
def jsonText [Lean.ToJson α] (a : α) : String := (Lean.toJson a).pretty ++ "\n"

/-! Errors. -/

/-- A user-facing failure: printed without a stack, exit code 1. -/
def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)

/-! Processes. -/

/-- Run a command, copying its stdout to our stderr as it comes (our stdout carries results); fail
with `what` on a non-zero exit. Its stderr is ours. -/
partial def runToStderr (cmd : String) (args : Array String) (cwd : Option System.FilePath)
    (what : String) : IO Unit := do
  let child ← IO.Process.spawn { cmd, args, cwd, stdin := .null, stdout := .piped }
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
  if let some dir := p.parent then IO.FS.createDirAll dir
  IO.FS.writeFile p contents

end LeanBlame
