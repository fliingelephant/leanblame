/-
`leanblame`: command-line entry point (README.md, Commands). It passes
the Lean frontend's backend to the two commands that need one (docs/decisions.md, "Beyond Lean"):
`export` hashes with it, `release` runs its kernel check.
-/
import LeanBlame.Core.Diff
import LeanBlame.Core.Release
import LeanBlame.Core.Sign
import LeanBlame.Core.Status
import LeanBlame.Core.Validate
import LeanBlame.Lean.Challenge
import LeanBlame.Lean.Equiv
import LeanBlame.Lean.Ids
import LeanBlame.Lean.Source

open LeanBlame

def usage : String :=
  "usage: leanblame <command> [options]

commands:
  init                                   create leanblame.toml and records/
  export [--boundary FILE] [--lib NAME]  build, export, write the boundary list (FILE: a
                                         verso-blueprint blueprint-manifest.json, read
                                         instead of @[trusted])
  id [--lib NAME]                        write a new random id into each @[trusted] of the
                                         library that has none: @[trusted \"id\"]
  status [--json]                        state of every tagged declaration
  blame NAME|ID                          who signed it, when, at which claim hash
  diff --from RECORD [--to RECORD] [--json] [NAME|ID...]
                                         what changed between the export an approve record
                                         names and another's (default: the last export)
  equiv [NAME|ID...]                     ask the kernel whether what changed under it (default:
                                         every declaration outdated by an untagged change only)
                                         is definitionally equal to what was approved
  sign --signer local:NAME [--module M] [--note TEXT] [NAME|ID...]
  sign --withdraw RECORD --signer local:NAME [--constants NAME|ID,...] [--note TEXT]
  challenge NAME|ID... --out DIR         write the comparator challenge of the tagged declarations
                                         into the new directory DIR: Challenge.lean (the theorems,
                                         proofs sorry), ChallengeDeps.lean (the others and what
                                         all of them need),
                                         lakefile.toml, lean-toolchain
  challenge --graph                      print the piece graph challenges are cut from (JSON)
  challenge --check DIR                  build the challenge in DIR against the library and
                                         check that it means what the library means
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

/-- Split `args` given which options take a value; positional arguments only when `positional`. -/
def parseArgs (valued switches : Array String) (args : List String) (positional := false) :
    IO Args :=
  go args {}
where
  go : List String → Args → IO Args
    | [], acc => pure acc
    | a :: rest, acc =>
      if valued.contains a then
        match rest with
        | v :: rest' => go rest' { acc with flags := acc.flags.push (a, v) }
        | [] => fail s!"{a} needs a value"
      else if switches.contains a then
        go rest { acc with switches := acc.switches.push a }
      else if a.startsWith "--" then
        fail s!"unknown option {a}"
      else if positional then
        go rest { acc with positional := acc.positional.push a }
      else
        fail s!"unexpected argument {a}"

def cmdExport (args : List String) : IO UInt32 := do
  let a ← parseArgs #["--boundary", "--lib"] #[] args
  let root ← IO.currentDir
  let r ← Export.run Source.backend root (a.get? "--boundary" |>.map System.FilePath.mk) (a.getAll "--lib")
  IO.eprintln s!"leanblame: {r.boundaryList.declarations.size} tagged declarations, {r.hashed} constants hashed"
  IO.println s!"export {r.exportHash}"
  IO.println s!"boundary {r.boundary}"
  return 0

def cmdId (args : List String) : IO UInt32 := do
  let a ← parseArgs #["--lib"] #[] args
  Ids.run (← IO.currentDir) (a.getAll "--lib")

def cmdStatus (args : List String) : IO UInt32 := do
  let a ← parseArgs #[] #["--json"] args
  Status.run (← IO.currentDir) (a.has "--json")

def cmdBlame (args : List String) : IO UInt32 := do
  let a ← parseArgs #[] #[] args (positional := true)
  let #[name] := a.positional | fail "usage: leanblame blame NAME|ID"
  Status.blame (← IO.currentDir) name

def cmdDiff (args : List String) : IO UInt32 := do
  let a ← parseArgs #["--from", "--to"] #["--json"] args (positional := true)
  let some fromRef := a.get? "--from"
    | fail "usage: leanblame diff --from RECORD [--to RECORD] [--json] [NAME|ID...]"
  Diff.run (← IO.currentDir) fromRef (a.get? "--to") a.positional (a.has "--json")

def cmdValidate (args : List String) : IO UInt32 := do
  let a ← parseArgs #["--base-ref"] #[] args
  Validate.run (← IO.currentDir) (a.get? "--base-ref")

def cmdInit (args : List String) : IO UInt32 := do
  discard <| parseArgs #[] #[] args
  Sign.init (← IO.currentDir)

def cmdSign (args : List String) : IO UInt32 := do
  let a ← parseArgs #["--signer", "--module", "--note", "--withdraw", "--constants"] #[] args (positional := true)
  let root ← IO.currentDir
  match a.get? "--withdraw" with
  | some ref =>
    unless a.positional.isEmpty && (a.get? "--module").isNone do
      fail "sign --withdraw RECORD takes --constants A,B instead of names or --module"
    let constants? := (a.get? "--constants").map fun s =>
      ((s.splitOn ",").map strTrim |>.filter (· != "")).toArray
    Sign.withdraw root (a.get? "--signer") ref constants? (a.get? "--note")
  | none =>
    if (a.get? "--constants").isSome then
      fail "--constants goes with --withdraw; to approve, list the names"
    Sign.approve root (a.get? "--signer") (a.get? "--module") a.positional (a.get? "--note")

def cmdChallenge (args : List String) : IO UInt32 := do
  let a ← parseArgs #["--out", "--check"] #["--graph"] args (positional := true)
  let root ← IO.currentDir
  match a.get? "--out", a.get? "--check", a.has "--graph" with
  | some dir, none, false =>
    Challenge.write root dir a.positional
    return 0
  | none, some dir, false =>
    unless a.positional.isEmpty do fail "challenge --check DIR takes no names"
    let (n, k) ← Challenge.check root dir
    IO.println (s!"challenge {dir}: the {n} tagged declarations it holds mean what the library's do" ++
      if k == 0 then "" else s!", {k} of them by definitional equality")
    return 0
  | none, none, true =>
    unless a.positional.isEmpty do fail "challenge --graph takes no names"
    IO.print (jsonText (← Challenge.graph root))
    return 0
  | _, _, _ => fail "usage: leanblame challenge NAME|ID... --out DIR, leanblame challenge --graph, or leanblame challenge --check DIR"

def cmdEquiv (args : List String) : IO UInt32 := do
  let a ← parseArgs #[] #[] args (positional := true)
  Equiv.run (← IO.currentDir) a.positional

def cmdRelease (args : List String) : IO UInt32 := do
  let a ← parseArgs #["--tag", "--out"] #[] args
  let some tag := a.get? "--tag" | fail "usage: leanblame release --tag TAG [--out FILE]"
  Release.run Source.backend (← IO.currentDir) tag ((a.get? "--out").map System.FilePath.mk)

def dispatch : List String → IO UInt32
  | [] | ["--help"] | ["-h"] | ["help"] => do IO.println usage; return 0
  | "init" :: args => cmdInit args
  | "export" :: args => cmdExport args
  | "id" :: args => cmdId args
  | "status" :: args => cmdStatus args
  | "blame" :: args => cmdBlame args
  | "diff" :: args => cmdDiff args
  | "sign" :: args => cmdSign args
  | "validate" :: args => cmdValidate args
  | "release" :: args => cmdRelease args
  | "equiv" :: args => cmdEquiv args
  | "challenge" :: args => cmdChallenge args
  | cmd :: _ => do
    IO.eprintln s!"leanblame: unknown command {cmd}\n{usage}"
    return 2

/-- Importing a library runs its initializers, as `lean` does for a file it compiles: `export` and
`id` load the library's environment extensions. -/
unsafe def main (args : List String) : IO UInt32 := do
  Lean.enableInitializersExecution
  try
    dispatch args
  catch e =>
    IO.eprintln s!"leanblame: {e}"
    return 1
