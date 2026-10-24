/-
`leanblame`: command-line entry point (docs/04-architecture.md, eight commands).
-/
import LeanBlame.Cli.Equiv
import LeanBlame.Cli.Release
import LeanBlame.Cli.Status
import LeanBlame.Cli.Validate
import LeanBlame.Cli.Sign

open LeanBlame

def usage : String :=
  "usage: leanblame <command> [options]

commands:
  init                                   create leanblame.toml, records/ and the CI job
  export [--boundary FILE] [--lib NAME]  build, export, write the boundary list (FILE: a
                                         verso-blueprint blueprint-manifest.json or a
                                         leanblame.manual.1 TOML list)
  status [--json]                        state of every tagged declaration
  blame NAME                             who signed NAME, when, at which claim hash
  equiv [NAME...]                        ask the kernel whether what changed under NAME (default:
                                         every declaration outdated by an untagged change only)
                                         is definitionally equal to what was approved
  sign [--signer local:NAME] [--module M] [--note TEXT] [NAME...]
  sign --withdraw RECORD [--signer local:NAME] [--constants A,B] [--note TEXT]
  validate [--base-ref REF]              check records/ (schema, authority, append-only)
  release --tag TAG [--out FILE]         signoff and kernel gates, axiom report, manifest"

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

def cmdExport (args : List String) : IO UInt32 := do
  let a ← IO.ofExcept (parseArgs #["--boundary", "--lib"] #[] args)
  unless a.positional.isEmpty do throw (IO.userError "export takes no positional arguments")
  let root ← IO.currentDir
  let r ← Export.run root (a.get? "--boundary" |>.map System.FilePath.mk) (a.getAll "--lib")
  IO.eprintln s!"leanblame: {r.boundaryList.declarations.size} tagged declarations, {r.hashed} constants hashed"
  IO.println s!"export {r.exportHash}"
  IO.println s!"boundary {r.boundary}"
  return 0

def cmdStatus (args : List String) : IO UInt32 := do
  let a ← IO.ofExcept (parseArgs #[] #["--json"] args)
  unless a.positional.isEmpty do throw (IO.userError "status takes no positional arguments")
  Status.run (← IO.currentDir) (a.has "--json")

def cmdBlame (args : List String) : IO UInt32 := do
  let a ← IO.ofExcept (parseArgs #[] #[] args)
  let #[name] := a.positional | throw (IO.userError "usage: leanblame blame NAME")
  Status.blame (← IO.currentDir) name

def cmdValidate (args : List String) : IO UInt32 := do
  let a ← IO.ofExcept (parseArgs #["--base-ref"] #[] args)
  unless a.positional.isEmpty do throw (IO.userError "validate takes no positional arguments")
  Validate.run (← IO.currentDir) (a.get? "--base-ref")

def cmdInit (args : List String) : IO UInt32 := do
  unless args.isEmpty do throw (IO.userError "init takes no arguments")
  Sign.init (← IO.currentDir)

def cmdSign (args : List String) : IO UInt32 := do
  let a ← IO.ofExcept (parseArgs #["--signer", "--module", "--note", "--withdraw", "--constants"] #[] args)
  let root ← IO.currentDir
  match a.get? "--withdraw" with
  | some ref =>
    unless a.positional.isEmpty && (a.get? "--module").isNone do
      throw (IO.userError "sign --withdraw RECORD takes --constants A,B instead of names or --module")
    let constants? := (a.get? "--constants").map fun s =>
      ((s.splitOn ",").map strTrim |>.filter (· != "")).toArray
    Sign.withdraw root (a.get? "--signer") ref constants? (a.get? "--note")
  | none =>
    if (a.get? "--constants").isSome then
      throw (IO.userError "--constants goes with --withdraw; to approve, list the names")
    Sign.approve root (a.get? "--signer") (a.get? "--module") a.positional (a.get? "--note")

def cmdEquiv (args : List String) : IO UInt32 := do
  let a ← IO.ofExcept (parseArgs #[] #[] args)
  Equiv.run (← IO.currentDir) a.positional

def cmdRelease (args : List String) : IO UInt32 := do
  let a ← IO.ofExcept (parseArgs #["--tag", "--out"] #[] args)
  unless a.positional.isEmpty do throw (IO.userError "release takes no positional arguments")
  let some tag := a.get? "--tag" | throw (IO.userError "usage: leanblame release --tag TAG [--out FILE]")
  Release.run (← IO.currentDir) tag ((a.get? "--out").map System.FilePath.mk)

def dispatch : List String → IO UInt32
  | [] | ["--help"] | ["-h"] | ["help"] => do IO.println usage; return 0
  | "init" :: args => cmdInit args
  | "export" :: args => cmdExport args
  | "status" :: args => cmdStatus args
  | "blame" :: args => cmdBlame args
  | "sign" :: args => cmdSign args
  | "validate" :: args => cmdValidate args
  | "release" :: args => cmdRelease args
  | "equiv" :: args => cmdEquiv args
  | cmd :: _ => do
    IO.eprintln s!"leanblame: unknown command {cmd}\n{usage}"
    return 2

def main (args : List String) : IO UInt32 := do
  try
    dispatch args
  catch e =>
    IO.eprintln s!"leanblame: {e}"
    return 1
