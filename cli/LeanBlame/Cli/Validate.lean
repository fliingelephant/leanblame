/-
`leanblame validate [--base-ref REF]` (docs/05-records.md, docs/14-schemas.md §2).

Checks every file in the records directories:
* the record schema (strict: unknown keys, wrong types, non-UTC dates, malformed
  hashes and signer ids are errors);
* the file name is the SHA-256 of the file bytes (`<hex>.toml`);
* authority: `refers_to` names an approve record, the withdraw's signer equals that
  record's signer, and listed constants are in that record;
* with `--base-ref REF`: no file under the records directories was modified or
  deleted relative to the merge base of REF and the work tree. Only additions pass.
-/
import LeanBlame.Cli.Records

namespace LeanBlame.Validate

def run (root : System.FilePath) (baseRef? : Option String) : IO UInt32 := do
  let cfg ← Config.load root
  let dirs ← recordDirs root cfg
  let mut errors : Array String := #[]
  let mut loaded : Array LoadedRecord := #[]
  for dir in dirs do
    unless ← dir.isDir do
      errors := errors.push s!"{dir}: records directory missing"
      continue
    -- Every visible file in a records directory must be a record named by its hash.
    for e in (← dir.readDir).qsort (fun a b => a.fileName < b.fileName) do
      if e.fileName.startsWith "." then continue
      if ← e.path.isDir then
        errors := errors.push s!"{e.path}: unexpected directory in a records directory"
      else if e.path.extension != some "toml" then
        errors := errors.push s!"{e.path}: not a record file (expected <sha256>.toml)"
      else
        let expected := Sha256.hexOfBytes (← IO.FS.readBinFile e.path) ++ ".toml"
        if e.fileName != expected then
          errors := errors.push s!"{e.path}: file name must be the sha256 of its bytes, {expected}"
    let (good, bad) ← loadRecordDir dir
    for (p, es) in bad do
      for msg in es do errors := errors.push s!"{p}: {msg}"
    loaded := loaded ++ good
  -- Authority rules.
  let byHash : Std.HashMap String LoadedRecord := loaded.foldl (fun m r => m.insert r.hash r) {}
  for r in loaded do
    if let .withdraw w := r.record then
      match byHash[w.refersTo]? with
      | none => errors := errors.push s!"{r.path}: refers_to {w.refersTo} names no record"
      | some target =>
        match target.record with
        | .withdraw _ =>
          errors := errors.push s!"{r.path}: refers_to must name an approve record, not a withdraw"
        | .approve a =>
          if a.signer != w.signer then
            errors := errors.push s!"{r.path}: withdraw signer {w.signer} is not the approve record's signer {a.signer}"
          if let some cs := w.constants then
            for c in cs do
              unless a.constants.any (·.1 == c) do
                errors := errors.push s!"{r.path}: {c} is not in the withdrawn record"
  -- Append-only.
  if let some baseRef := baseRef? then
    let mb := strTrim (← runCapture "git" #["merge-base", baseRef, "HEAD"] root)
    let rel := cfg.records.filterMap localRecordDir?
    let out ← runCapture "git" (#["diff", "--name-status", "--no-renames", mb, "--"] ++ rel) root
    for line in strLines out do
      let line := strTrim line
      if line.isEmpty then continue
      let status := line.take 1 |>.copy
      let path := strTrim (strDrop line 1)
      -- Only record files are append-only; `.gitkeep` may go.
      unless isRecordFile ((System.FilePath.mk path).fileName.getD "") do continue
      match status with
      | "A" => pure ()
      | "D" => errors := errors.push s!"{path}: existing record deleted (records are append-only)"
      | "M" => errors := errors.push s!"{path}: existing record modified (records are append-only)"
      | _ => errors := errors.push s!"{path}: existing record changed ({status}) (records are append-only)"
  if errors.isEmpty then
    IO.println s!"{loaded.size} records valid"
    return 0
  else
    for e in errors do IO.eprintln e
    IO.eprintln s!"validate: {errors.size} problems"
    return 1

end LeanBlame.Validate
