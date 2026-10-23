/-
Small helpers shared by the commands: strings, hashes, files, processes.
-/
import LeanBlame.Cli.Sha256

namespace LeanBlame

/-! Strings (Lean 4.35 returns slices from most `String` operations). -/

def strDrop (s : String) (n : Nat) : String := (s.drop n).copy

def strTrim (s : String) : String := s.trimAscii.copy

def strLines (s : String) : List String :=
  (s.splitOn "\n").map fun l => if l.endsWith "\r" then (l.dropEnd 1).copy else l

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

/-! Errors. -/

/-- A user-facing failure: printed without a stack, exit code 1. -/
def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)

/-! Processes. -/

/-- Run a command, capture stdout, fail with its stderr on a non-zero exit. -/
def runCapture (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO String := do
  let out ← IO.Process.output { cmd, args, cwd, env }
  if out.exitCode != 0 then
    fail s!"`{cmd} {" ".intercalate args.toList}` failed (exit {out.exitCode}):\n{out.stderr}"
  return out.stdout

/-- Run a command, its stdout copied to our stderr (our stdout stays for results); fail on a
non-zero exit. -/
partial def runToStderr (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    IO Unit := do
  let child ← IO.Process.spawn { cmd, args, cwd, stdin := .null, stdout := .piped }
  let err ← IO.getStderr
  let rec copy : IO Unit := do
    let chunk ← child.stdout.read 4096
    unless chunk.isEmpty do
      err.write chunk
      err.flush
      copy
  copy
  let code ← child.wait
  if code != 0 then
    fail s!"`{cmd} {" ".intercalate args.toList}` failed (exit {code})"

/-- Run a command and stream its stdout into `outFile`; stderr is inherited. -/
partial def runToFile (cmd : String) (args : Array String) (outFile : System.FilePath)
    (cwd : Option System.FilePath := none) (env : Array (String × Option String) := #[]) :
    IO Unit := do
  let child ← IO.Process.spawn { cmd, args, cwd, env, stdin := .null, stdout := .piped }
  let h ← IO.FS.Handle.mk outFile .write
  let rec copy : IO Unit := do
    let chunk ← child.stdout.read (1024 * 1024)
    unless chunk.isEmpty do
      h.write chunk
      copy
  copy
  h.flush
  let code ← child.wait
  if code != 0 then
    fail s!"`{cmd}` failed (exit {code})"

/-! Files. -/

def readFileIfExists (p : System.FilePath) : IO (Option String) := do
  if ← p.pathExists then return some (← IO.FS.readFile p) else return none

/-- Write a file, creating parent directories. -/
def writeFileMkdirs (p : System.FilePath) (contents : String) : IO Unit := do
  if let some dir := p.parent then IO.FS.createDirAll dir
  IO.FS.writeFile p contents

end LeanBlame
