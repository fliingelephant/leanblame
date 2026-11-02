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
  export                                 build, export, write the boundary list (leanblame.toml
                                         names the libraries and any blueprint manifest)
  id                                     tag every declaration of the library, each with a new
                                         random id: @[trusted \"id\"], or attribute [trusted \"id\"]
                                         Name at the end of its module (of the library of tags,
                                         when a listed library declares nothing)
  status [--json]                        state of every tagged declaration
  blame NAME|ID                          who signed it, when, at which claim hash
  diff --from RECORD [--to RECORD] [--json] [NAME|ID...]
                                         what changed between the export an approve record
                                         names and another's (default: the last export)
  equiv [NAME|ID...]                     ask the kernel whether what changed under it (default:
                                         every declaration outdated by an untagged change only)
                                         is definitionally equal to what was approved
  sign --signer local:NAME [--note TEXT] (NAME|ID... | --module M | --all)
                                         approve the declarations named, a module's tagged
                                         declarations, or all of the library's
  withdraw RECORD --signer local:NAME [--note TEXT] [NAME|ID...]
                                         withdraw your approve record, or only the declarations
                                         named
  challenge write NAME|ID... --out DIR   write the comparator challenge of the tagged declarations
                                         into the new directory DIR: Challenge.lean (the theorems,
                                         proofs sorry), ChallengeDeps.lean (the others and what
                                         all of them need),
                                         lakefile.toml, lean-toolchain
  challenge graph                        print the piece graph challenges are cut from (JSON)
  challenge check DIR                    build the challenge in DIR against the library and
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
  discard <| parseArgs #[] #[] args
  let root ← IO.currentDir
  let cfg ← Config.load root
  let r ← Export.run Source.backend root (cfg.boundary.map (root / ·)) cfg.libraries cfg.trusted
  IO.eprintln s!"leanblame: {r.boundaryList.declarations.size} tagged declarations, {r.hashed} constants hashed"
  IO.println s!"export {r.exportHash}"
  IO.println s!"boundary {r.boundary}"
  return 0

def cmdId (args : List String) : IO UInt32 := do
  discard <| parseArgs #[] #[] args
  let root ← IO.currentDir
  Ids.run root (← Config.load root).libraries

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
  let a ← parseArgs #["--signer", "--module", "--note"] #["--all"] args (positional := true)
  let selection : Sign.Selection ← match a.positional.isEmpty, a.get? "--module", a.has "--all" with
    | false, none, false => pure (.keys a.positional)
    | true, some m, false => pure (.module m)
    | true, none, true => pure .all
    | _, _, _ => fail "usage: leanblame sign --signer local:NAME [--note TEXT] (NAME|ID... | --module M | --all)"
  Sign.approve (← IO.currentDir) (a.get? "--signer") selection (a.get? "--note")

def cmdWithdraw (args : List String) : IO UInt32 := do
  let a ← parseArgs #["--signer", "--note"] #[] args (positional := true)
  let some ref := a.positional[0]?
    | fail "usage: leanblame withdraw RECORD --signer local:NAME [--note TEXT] [NAME|ID...]"
  Sign.withdraw (← IO.currentDir) (a.get? "--signer") ref (a.positional.extract 1) (a.get? "--note")

def cmdChallenge : List String → IO UInt32
  | "write" :: args => do
    let a ← parseArgs #["--out"] #[] args (positional := true)
    let some dir := a.get? "--out" | fail "usage: leanblame challenge write NAME|ID... --out DIR"
    Challenge.write (← IO.currentDir) dir a.positional
    return 0
  | "check" :: args => do
    let a ← parseArgs #[] #[] args (positional := true)
    let #[dir] := a.positional | fail "usage: leanblame challenge check DIR"
    let (n, k) ← Challenge.check (← IO.currentDir) dir
    IO.println (s!"challenge {dir}: the {n} tagged declarations it holds mean what the library's do" ++
      if k == 0 then "" else s!", {k} of them by definitional equality")
    return 0
  | ["graph"] => do
    IO.print (jsonText (← Challenge.graph (← IO.currentDir)))
    return 0
  | _ => fail "usage: leanblame challenge write NAME|ID... --out DIR, leanblame challenge check DIR, or leanblame challenge graph"

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
  | "withdraw" :: args => cmdWithdraw args
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
