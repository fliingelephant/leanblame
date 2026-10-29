/-
`leanblame validate [--base-ref REF]` (trust-model.md, "Records"; docs/schemas.md §2).

Checks every entry of the records directories:
* it is a record: a file named by the SHA-256 of its bytes (`<hex>.toml`) that
  passes the record schema (strict: unknown keys, wrong types, non-UTC dates,
  malformed hashes and signer ids are errors);
* authority: `refers_to` names an approve record, the withdraw's signer equals that
  record's signer, and listed declarations are in that record; `exclude` in
  `leanblame.toml` names approve records only (a withdrawal cannot be excluded);
  no record is in two records directories;
* with `--base-ref REF`: every record of the merge base of REF and HEAD, in the
  records directories its `leanblame.toml` names, is still a record. Records are
  compared by id, so moving them passes; editing or deleting one does not.
-/
import Lake.Util.Git
import LeanBlame.Core.Records

namespace LeanBlame.Validate

/-- Append-only: the records of revision `base` that are not among the records `loaded` now. -/
def appendOnlyErrors (root : System.FilePath) (base : String) (loaded : Array LoadedRecord) :
    IO (Array String) := do
  let some text ← (root : Lake.GitRepo).captureGit? #["show", s!"{base}:./{Config.fileName}"]
    | return #[]
  let cfg ← match ← Config.parse text s!"{base}:{Config.fileName}" with
    | .ok cfg => pure cfg
    | .error e => return #[s!"{Config.fileName} at the merge base {base} does not parse: {e}"]
  let dirs := cfg.records
  if dirs.isEmpty then return #[]
  let ids : Std.HashSet String := loaded.foldl (·.insert ·.hash) {}
  let mut errors := #[]
  let out ← IO.Process.run
    { cmd := "git", args := #["ls-tree", "-r", "--name-only", base, "--"] ++ dirs, cwd := root }
  for path in out.lines do
    let p := System.FilePath.mk path.copy
    let id := mkHash (p.fileStem.getD "")
    if p.extension == some "toml" && isHash id && !ids.contains id then
      errors := errors.push s!"{p}: record {id} of the merge base is missing (records are append-only)"
  return errors

def run (root : System.FilePath) (baseRef? : Option String) : IO UInt32 := do
  let cfg ← Config.load root
  let (loaded, bad) ← loadAllRecords root cfg
  let mut errors : Array String := #[]
  for (p, es) in bad do
    for msg in es do errors := errors.push s!"{p}: {msg}"
  -- Authority: the withdraw rule; `exclude` names approve records only.
  errors := errors ++ (Ledger.build cfg loaded).problems
  if let some baseRef := baseRef? then
    let mb := strTrim (← IO.Process.run
      { cmd := "git", args := #["merge-base", baseRef, "HEAD"], cwd := root })
    errors := errors ++ (← appendOnlyErrors root mb loaded)
  if errors.isEmpty then
    IO.println s!"{loaded.size} records valid"
    return 0
  else
    for e in errors do IO.eprintln e
    IO.eprintln s!"validate: {errors.size} problems"
    return 1

end LeanBlame.Validate
