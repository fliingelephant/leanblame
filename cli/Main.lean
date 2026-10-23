/-
`leanblame`: command-line entry point (docs/04-architecture.md, eight commands).
-/
import LeanBlame.Cli.Export

open LeanBlame

def usage : String :=
  "usage: leanblame <command> [options]

commands:
  init                                   create leanblame.toml, records/ and the CI job
  export [--boundary FILE] [--lib NAME]  build, export, write the boundary list
  status [--base EXPORT] [--json]        state of every tagged declaration
  blame NAME                             who signed NAME, when, at which claim hash
  equiv                                  (not implemented)
  sign [--signer local:NAME] [--module M] [--note TEXT] [NAME...]
  sign --withdraw RECORD [--signer local:NAME] [--constants A,B] [--note TEXT]
  validate [--base-ref REF]              check records/ (schema, authority, append-only)
  release                                (not implemented)"

/-- Parsed command line: flags with values, boolean switches, positional arguments. -/
structure Args where
  flags : Array (String × String) := #[]
  switches : Array String := #[]
  positional : Array String := #[]

def Args.get? (a : Args) (k : String) : Option String :=
  (a.flags.find? (·.1 == k)).map (·.2)

def Args.getAll (a : Args) (k : String) : Array String :=
  (a.flags.filter (·.1 == k)).map (·.2)

def Args.has (a : Args) (k : String) : Bool := a.switches.contains k

/-- Split `args` given which options take a value. -/
def parseArgs (valued switches : Array String) (args : List String) : Except String Args :=
  go args {}
where
  go : List String → Args → Except String Args
    | [], acc => .ok acc
    | a :: rest, acc =>
      if valued.contains a then
        match rest with
        | v :: rest' => go rest' { acc with flags := acc.flags.push (a, v) }
        | [] => .error s!"{a} needs a value"
      else if switches.contains a then
        go rest { acc with switches := acc.switches.push a }
      else if a.startsWith "--" then
        .error s!"unknown option {a}"
      else
        go rest { acc with positional := acc.positional.push a }

def notImplemented (cmd : String) : IO UInt32 := do
  IO.eprintln s!"leanblame {cmd}: not implemented"
  return 2

def cmdExport (args : List String) : IO UInt32 := do
  let a ← IO.ofExcept (parseArgs #["--boundary", "--lib"] #[] args)
  unless a.positional.isEmpty do throw (IO.userError "export takes no positional arguments")
  let root ← IO.currentDir
  let r ← Export.run root (a.get? "--boundary" |>.map System.FilePath.mk) (a.getAll "--lib")
  IO.eprintln s!"leanblame: {r.boundaryList.declarations.size} tagged declarations, {r.hashed} constants hashed"
  IO.println s!"export {r.exportHash}"
  IO.println s!"boundary {r.boundary}"
  return 0

def dispatch : List String → IO UInt32
  | [] | ["--help"] | ["-h"] | ["help"] => do IO.println usage; return 0
  | "export" :: args => cmdExport args
  | cmd :: _ =>
    if #["init", "status", "blame", "equiv", "sign", "validate", "release"].contains cmd then
      notImplemented cmd
    else do
      IO.eprintln s!"leanblame: unknown command {cmd}\n{usage}"
      return 2

def main (args : List String) : IO UInt32 := do
  try
    dispatch args
  catch e =>
    IO.eprintln s!"leanblame: {e}"
    return 1
