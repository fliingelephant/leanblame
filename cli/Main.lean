/-
`leanblame`: command-line entry point (docs/design/04-architecture.md, ten commands). It passes
the Lean frontend's backend to the two commands that need one (docs/design/15-generic-core.md):
`export` hashes with it, `release` runs its kernel check.
-/
import LeanBlame.Core.Release
import LeanBlame.Core.Sign
import LeanBlame.Core.Status
import LeanBlame.Core.Validate
import LeanBlame.Lean.Equiv
import LeanBlame.Lean.Ids
import LeanBlame.Lean.Sorried
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
  equiv [NAME|ID...]                     ask the kernel whether what changed under it (default:
                                         every declaration outdated by an untagged change only)
                                         is definitionally equal to what was approved
  sign --signer local:NAME [--module M] [--note TEXT] [NAME|ID...]
  sign --withdraw RECORD --signer local:NAME [--constants NAME|ID,...] [--note TEXT]
  sorried HASH...                        print the library's modules with proofs replaced by
                                         sorry, in pieces, by the hashes `status --json` lists
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

def cmdSorried (args : List String) : IO UInt32 := do
  let a ← parseArgs #[] #[] args (positional := true)
  if a.positional.isEmpty then fail "usage: leanblame sorried HASH..."
  let root ← IO.currentDir
  let cur ← Store.readCurrent root
  let copies ← a.positional.mapM fun h => do
    let some m := cur.modules.find? (·.copy == h)
      | fail s!"{h} is no module copy of the last export (`leanblame status --json` lists them)"
    let c ← Sorried.read root m.key
    unless c.hash == h do fail s!"{Sorried.path root m.key}: its pieces do not hash to {h}"
    return (h, Lean.toJson c.pieces)
  IO.println (Lean.Json.mkObj copies.toList).pretty
  return 0

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
  | "sign" :: args => cmdSign args
  | "validate" :: args => cmdValidate args
  | "release" :: args => cmdRelease args
  | "equiv" :: args => cmdEquiv args
  | "sorried" :: args => cmdSorried args
  | cmd :: _ => do
    IO.eprintln s!"leanblame: unknown command {cmd}\n{usage}"
    return 2

def main (args : List String) : IO UInt32 := do
  try
    dispatch args
  catch e =>
    IO.eprintln s!"leanblame: {e}"
    return 1
