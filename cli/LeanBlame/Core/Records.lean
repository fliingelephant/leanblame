/-
Loading records and deciding liveness (docs/design/05-records.md).

A record is a file of a records directory named `<sha256 of its bytes>.toml` that parses; that hash
is its id. Records name declarations by id. A withdraw counts only if it refers to an approve record
and is signed by that record's signer; it kills the listed declarations of that record, or all of
them. An approve record is live for a declaration if no counting withdraw covers it, `exclude` does
not list it and `leanblame.toml` allows its signer. A withdrawal cannot be excluded: a signer's word
about their own record stands. A withdraw that breaks this rule, an `exclude` entry that names no
approve record and a record in two directories are problems: `validate` lists them, the other
commands stop.
-/
import LeanBlame.Core.Config

namespace LeanBlame

/-- The records directories of the configuration, relative to the library root. -/
def recordDirs (cfg : Config) : Array System.FilePath := cfg.records.map (⟨·⟩)

/-- Load the records directory `dir` of the library at `root`. An entry is a record iff it is a file
named `<sha256 of its bytes>.toml` that parses (docs/design/05); every other entry is a problem,
returned with its path. Paths are relative to `root`. A missing directory holds no records (git
keeps no empty directory). -/
def loadRecordDir (root dir : System.FilePath) :
    IO (Array LoadedRecord × Array (System.FilePath × Array String)) := do
  unless ← (root / dir).isDir do return (#[], #[])
  let entries := (← (root / dir).readDir).qsort (fun a b => a.fileName < b.fileName)
  let mut good := #[]
  let mut bad := #[]
  for e in entries do
    let path := dir / e.fileName
    if ← e.path.isDir then
      bad := bad.push (path, #["a directory, not a record"]); continue
    let bytes ← IO.FS.readBinFile e.path
    let hex := Sha256.hexOfBytes bytes
    unless e.fileName == hex ++ ".toml" do
      bad := bad.push (path, #[s!"not a record: the file name must be the sha256 of its bytes, {hex}.toml"])
      continue
    let some text := String.fromUTF8? bytes
      | bad := bad.push (path, #["not UTF-8"]); continue
    match ← Record.parse text path.toString with
    | .ok r => good := good.push { hash := mkHash hex, path, record := r }
    | .error es => bad := bad.push (path, es)
  return (good, bad)

/-- A record id from `sha256:<hex>`, `<hex>` or the path of a record file. -/
def recordId (ref : String) : IO String := do
  if isHash ref then return ref
  if isHexDigest ref then return mkHash ref
  if ← (System.FilePath.mk ref).pathExists then return sha256OfBytes (← IO.FS.readBinFile ref)
  fail s!"{ref}: not a record id or file"

def loadAllRecords (root : System.FilePath) (cfg : Config) :
    IO (Array LoadedRecord × Array (System.FilePath × Array String)) := do
  let mut good := #[]
  let mut bad := #[]
  for d in recordDirs cfg do
    let (g, b) ← loadRecordDir root d
    good := good ++ g
    bad := bad ++ b
  return (good, bad)

/--
The withdraw rule (docs/design/05): `w` refers to an approve record, is signed by that record's
signer, and lists only declarations of it. Returns the declarations it withdraws, as that record
lists them (all of them when it lists none), or every problem. `byId` holds the records by id.
-/
def withdrawCovers (byId : Std.HashMap String LoadedRecord) (w : WithdrawRecord) :
    Except (Array String) (Array ApprovedConstant) := do
  let some target := byId[w.refersTo]? | throw #[s!"refers_to {w.refersTo} names no record"]
  let .approve a := target.record
    | throw #[s!"refers_to {w.refersTo} names a withdraw; only approve records can be withdrawn"]
  let problems :=
    (if a.signer == w.signer then #[] else
      #[s!"signer {w.signer} is not {a.signer}, who signed {w.refersTo}; only its signer can withdraw it"]) ++
    ((w.constants.getD #[]).filter (fun i => !a.constants.any (·.id == i)) |>.map
      (s!"{·} is not in record {w.refersTo}"))
  unless problems.isEmpty do throw problems
  return match w.constants with
    | some ids => a.constants.filter (ids.contains ·.id)
    | none => a.constants

/-- A record in the history of one declaration. -/
inductive Ledger.Entry where
  /-- An approve record listing the declaration, with its entry there. -/
  | approve (r : LoadedRecord) (a : ApproveRecord) (c : ApprovedConstant)
  /-- A counting withdraw covering it, with its entry in the withdrawn record. -/
  | withdraw (r : LoadedRecord) (w : WithdrawRecord) (c : ApprovedConstant)

/-- The records with withdrawals resolved. -/
structure Ledger where
  cfg : Config
  /-- Every record loaded, in (date, id) order. -/
  records : Array LoadedRecord
  /-- The same, by id. -/
  byId : Std.HashMap String LoadedRecord
  /-- (approve record id, declaration id) pairs that a counting withdraw covers. -/
  withdrawn : Std.HashSet (String × String)
  /-- Per declaration id: the approve records listing it, excluded ones too, and the counting
  withdraws covering it, in (date, record id) order. -/
  entries : Std.HashMap String (Array Ledger.Entry)
  /-- Withdraws that break the withdraw rule, `exclude` entries that name no approve record, and
  records found in two directories. -/
  problems : Array String

def Ledger.build (cfg : Config) (all : Array LoadedRecord) : Ledger := Id.run do
  let all := all.qsort fun a b =>
    ((compare a.record.date b.record.date).then (compare a.hash b.hash)) == .lt
  let mut byId : Std.HashMap String LoadedRecord := {}
  let mut problems := #[]
  for r in all do
    if let some other := byId[r.hash]? then
      problems := problems.push s!"{r.path}: the same record as {other.path}"
    byId := byId.insert r.hash r
  let mut withdrawn := {}
  let mut entries : Std.HashMap String (Array Entry) := {}
  for r in all do
    match r.record with
    | .approve a =>
      for c in a.constants do
        entries := entries.alter c.id fun es => (es.getD #[]).push (.approve r a c)
    | .withdraw w =>
      match withdrawCovers byId w with
      | .error ps => problems := problems ++ ps.map (s!"{r.path}: " ++ ·)
      | .ok covered =>
        for c in covered do
          withdrawn := withdrawn.insert (w.refersTo, c.id)
          entries := entries.alter c.id fun es => (es.getD #[]).push (.withdraw r w c)
  for x in cfg.exclude do
    match byId[x]? with
    | some { record := .approve _, .. } => pure ()
    | some { path, .. } =>
      problems := problems.push
        s!"{Config.fileName}: exclude lists {x}, the withdraw record {path}; withdrawals cannot be excluded"
    | none =>
      problems := problems.push s!"{Config.fileName}: exclude lists {x}, which is no record here"
  return { cfg, records := all, byId, withdrawn, entries, problems }

/-- `leanblame.toml` and its records; a problem of any record stops the command. -/
def Ledger.load (root : System.FilePath) : IO Ledger := do
  let cfg ← Config.load root
  let (all, bad) ← loadAllRecords root cfg
  let ledger := Ledger.build cfg all
  let problems := bad.map (fun (p, es) => s!"{p}: {"; ".intercalate es.toList}") ++ ledger.problems
  unless problems.isEmpty do
    fail ("records with problems (see `leanblame validate`):\n" ++
      "\n".intercalate (problems.toList.map ("  " ++ ·)))
  return ledger

def Ledger.entriesOf (l : Ledger) (id : String) : Array Ledger.Entry :=
  l.entries.getD id #[]

/-- Approve records listing declaration `id`, with its entry there. -/
def Ledger.approvalsOf (l : Ledger) (id : String) : Array (LoadedRecord × ApproveRecord × ApprovedConstant) :=
  (l.entriesOf id).filterMap fun | .approve r a c => some (r, a, c) | .withdraw .. => none

/-- Whether approve record `r` by `signer` is live for declaration `id`. -/
def Ledger.isLive (l : Ledger) (r : LoadedRecord) (signer id : String) : Bool :=
  !l.withdrawn.contains (r.hash, id) && !l.cfg.exclude.contains r.hash && l.cfg.allows signer

/-- What approve record `r` by `signer` of declaration `id` at `claim` is worth, given the
declaration's current claim (`none`: it is not on the current boundary list). -/
def Ledger.standing (l : Ledger) (r : LoadedRecord) (signer id claim : String)
    (current : Option String) : Standing :=
  if l.withdrawn.contains (r.hash, id) then .withdrawn
  else if l.cfg.exclude.contains r.hash then .excluded
  else if !l.cfg.allows signer then .notAllowed
  else if current == some claim then .current
  else .superseded

end LeanBlame
