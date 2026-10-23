/-
Loading records and deciding liveness (docs/05-records.md).

A record is a file of a records directory named `<sha256 of its bytes>.toml`
that parses; that hash is its id. `exclude` drops records before anything else. A withdraw counts only if it refers to an approve record and is
signed by that record's signer; it kills the listed constants of that record,
or all of them. An approve record is live for a constant if no counting
withdraw covers it and its signer is allowed by `leanblame.toml`.
-/
import LeanBlame.Cli.Config

namespace LeanBlame

/-- A record as loaded from a records directory. -/
structure LoadedRecord where
  /-- `sha256:` of the file bytes: the record's id. -/
  hash : String
  path : System.FilePath
  record : Record
  deriving Inhabited

/-- A local records directory of `leanblame.toml`, without trailing slash (`records/` and
`records` name the same directory); `none` for a remote repository. -/
def localRecordDir? (r : String) : Option String :=
  if r.startsWith "http://" || r.startsWith "https://" || r.startsWith "git@" then none
  else some (if r.endsWith "/" && r.length > 1 then (r.dropEnd 1).copy else r)

/-- The records directories of the configuration. Remote repositories are not supported yet. -/
def recordDirs (root : System.FilePath) (cfg : Config) : IO (Array System.FilePath) := do
  let mut out := #[]
  for r in cfg.records do
    match localRecordDir? r with
    | some d => out := out.push (root / d)
    | none => IO.eprintln s!"warning: records repository {r} skipped: only local directories are supported"
  return out

/-- Load a records directory. An entry is a record iff it is a file named `<sha256 of its
bytes>.toml` that parses (docs/05); every other entry is a problem, returned with its path. A
missing directory holds no records. -/
def loadRecordDir (dir : System.FilePath) :
    IO (Array LoadedRecord × Array (System.FilePath × Array String)) := do
  unless ← dir.isDir do return (#[], #[])
  let entries := (← dir.readDir).qsort (fun a b => a.fileName < b.fileName)
  let mut good := #[]
  let mut bad := #[]
  for e in entries do
    if ← e.path.isDir then
      bad := bad.push (e.path, #["a directory, not a record"]); continue
    let bytes ← IO.FS.readBinFile e.path
    let hex := Sha256.hexOfBytes bytes
    unless e.fileName == hex ++ ".toml" do
      bad := bad.push (e.path, #[s!"not a record: the file name must be the sha256 of its bytes, {hex}.toml"])
      continue
    let some text := String.fromUTF8? bytes
      | bad := bad.push (e.path, #["not UTF-8"]); continue
    match ← Record.parse text e.path.toString with
    | .ok r => good := good.push { hash := mkHash hex, path := e.path, record := r }
    | .error es => bad := bad.push (e.path, es)
  return (good, bad)

def loadAllRecords (root : System.FilePath) (cfg : Config) :
    IO (Array LoadedRecord × Array (System.FilePath × Array String)) := do
  let mut good := #[]
  let mut bad := #[]
  for d in ← recordDirs root cfg do
    let (g, b) ← loadRecordDir d
    good := good ++ g
    bad := bad ++ b
  return (good, bad)

/--
The withdraw rule (docs/05): `w` refers to an approve record, is signed by that record's signer,
and lists only constants of it. Returns the constants it withdraws (all of the record's when it
lists none), or every problem. `byId` holds the records by id.
-/
def withdrawCovers (byId : Std.HashMap String LoadedRecord) (w : WithdrawRecord) :
    Except (Array String) (Array String) := do
  let some target := byId[w.refersTo]? | throw #[s!"refers_to {w.refersTo} names no record"]
  let .approve a := target.record
    | throw #[s!"refers_to {w.refersTo} names a withdraw; only approve records can be withdrawn"]
  let names := a.constants.map (·.1)
  let problems :=
    (if a.signer == w.signer then #[] else
      #[s!"signer {w.signer} is not {a.signer}, who signed {w.refersTo}; only its signer can withdraw it"]) ++
    ((w.constants.getD #[]).filter (!names.contains ·) |>.map (s!"{·} is not in record {w.refersTo}"))
  unless problems.isEmpty do throw problems
  return w.constants.getD names

/-- A withdraw that counts, with the constants it covers. -/
structure CountingWithdraw where
  loaded : LoadedRecord
  withdraw : WithdrawRecord
  constants : Array String

/-- A record in the history of one constant. -/
inductive Ledger.Entry where
  /-- An approve record listing the constant, with the claim hash it carries for it. -/
  | approve (r : LoadedRecord) (a : ApproveRecord) (claim : String)
  /-- A counting withdraw covering the constant. -/
  | withdraw (w : CountingWithdraw)

/-- Records after `exclude`, with withdrawals resolved. -/
structure Ledger where
  cfg : Config
  /-- Every record loaded, excluded or not, by id. -/
  byId : Std.HashMap String LoadedRecord
  /-- The records not excluded, in (date, id) order. -/
  records : Array LoadedRecord
  approves : Std.HashMap String (LoadedRecord × ApproveRecord)
  /-- (approve record id, constant) pairs that a counting withdraw covers. -/
  withdrawn : Std.HashSet (String × String)
  /-- Per constant: the approve records listing it and the counting withdraws covering it, in
  (date, id) order. -/
  entries : Std.HashMap String (Array Ledger.Entry)
  /-- Withdraws that break the withdraw rule, excluded or not, with the problems. -/
  problems : Array (LoadedRecord × Array String)

/-- A withdraw counts iff it is not excluded and keeps the withdraw rule. -/
def Ledger.build (cfg : Config) (all : Array LoadedRecord) : Ledger := Id.run do
  let all := all.qsort fun a b =>
    ((compare a.record.date b.record.date).then (compare a.hash b.hash)) == .lt
  let byId : Std.HashMap String LoadedRecord := all.foldl (fun m r => m.insert r.hash r) {}
  let mut approves := {}
  let mut withdrawn := {}
  let mut entries : Std.HashMap String (Array Entry) := {}
  let mut problems := #[]
  for r in all do
    let excluded := cfg.exclude.contains r.hash
    match r.record with
    | .approve a =>
      if excluded then continue
      approves := approves.insert r.hash (r, a)
      for (c, claim) in a.constants do
        entries := entries.alter c fun es => (es.getD #[]).push (.approve r a claim)
    | .withdraw w =>
      match withdrawCovers byId w with
      | .error ps => problems := problems.push (r, ps)
      | .ok covered =>
        if excluded then continue
        let cw : CountingWithdraw := { loaded := r, withdraw := w, constants := covered }
        for c in covered do
          withdrawn := withdrawn.insert (w.refersTo, c)
          entries := entries.alter c fun es => (es.getD #[]).push (.withdraw cw)
  let records := all.filter fun r => !cfg.exclude.contains r.hash
  return { cfg, byId, records, approves, withdrawn, entries, problems }

def Ledger.entriesOf (l : Ledger) (name : String) : Array Ledger.Entry :=
  l.entries.getD name #[]

/-- Approve records listing `name`, with the claim hash they carry for it. -/
def Ledger.approvalsOf (l : Ledger) (name : String) : Array (LoadedRecord × ApproveRecord × String) :=
  (l.entriesOf name).filterMap fun | .approve r a claim => some (r, a, claim) | .withdraw _ => none

def Ledger.isLive (l : Ledger) (recordHash : String) (signer : String) (name : String) : Bool :=
  l.cfg.allows signer && !l.withdrawn.contains (recordHash, name)

/-- Counting withdraws that cover `name`. -/
def Ledger.withdrawalsOf (l : Ledger) (name : String) : Array CountingWithdraw :=
  (l.entriesOf name).filterMap fun | .withdraw w => some w | .approve .. => none

end LeanBlame
