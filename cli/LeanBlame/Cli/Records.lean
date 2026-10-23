/-
Loading records and deciding liveness (docs/05-records.md).

A record's id is the SHA-256 of its file bytes. `exclude` drops records before
anything else. A withdraw counts only if it refers to an approve record and is
signed by that record's signer; it kills the listed constants of that record,
or all of them. An approve record is live for a constant if no counting
withdraw covers it and its signer is allowed by `leanblame.toml`.
-/
import LeanBlame.Cli.Config

namespace LeanBlame

/-- A record file as loaded from a records directory. -/
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

/-- The files of a records directory that hold records: visible `*.toml` files. Hidden files,
such as the `.gitkeep` that `init` writes, are not records, for `status` and `validate` alike. -/
def isRecordFile (fileName : String) : Bool :=
  !fileName.startsWith "." && fileName.endsWith ".toml"

/-- Parse every `*.toml` file of `dir`. Returns the records and, per bad file, its problems. -/
def loadRecordDir (dir : System.FilePath) :
    IO (Array LoadedRecord × Array (System.FilePath × Array String)) := do
  unless ← dir.isDir do return (#[], #[])
  let entries := (← dir.readDir).qsort (fun a b => a.fileName < b.fileName)
  let mut good := #[]
  let mut bad := #[]
  for e in entries do
    unless isRecordFile e.fileName do continue
    let bytes ← IO.FS.readBinFile e.path
    let hash := sha256OfBytes bytes
    let some text := String.fromUTF8? bytes
      | bad := bad.push (e.path, #["not UTF-8"]); continue
    match ← Record.parse text e.path.toString with
    | .ok r => good := good.push { hash, path := e.path, record := r }
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

/-- A withdraw that counts, with the constants it covers. -/
structure CountingWithdraw where
  loaded : LoadedRecord
  withdraw : WithdrawRecord
  constants : Array String

/-- Records after `exclude`, with withdrawals resolved. -/
structure Ledger where
  cfg : Config
  records : Array LoadedRecord
  approves : Std.HashMap String (LoadedRecord × ApproveRecord)
  withdraws : Array CountingWithdraw
  /-- (approve record id, constant) pairs that a counting withdraw covers. -/
  withdrawn : Std.HashSet (String × String)

def Ledger.build (cfg : Config) (all : Array LoadedRecord) : Ledger := Id.run do
  let records := all.filter fun r => !cfg.exclude.contains r.hash
  let mut approves : Std.HashMap String (LoadedRecord × ApproveRecord) := {}
  for r in records do
    if let .approve a := r.record then approves := approves.insert r.hash (r, a)
  let mut withdraws := #[]
  let mut withdrawn : Std.HashSet (String × String) := {}
  for r in records do
    if let .withdraw w := r.record then
      let some (_, a) := approves[w.refersTo]? | continue
      unless a.signer == w.signer do continue
      let names := a.constants.map (·.1)
      let covered := (w.constants.getD names).filter names.contains
      withdraws := withdraws.push { loaded := r, withdraw := w, constants := covered }
      for c in covered do withdrawn := withdrawn.insert (w.refersTo, c)
  return { cfg, records, approves, withdraws, withdrawn }

/-- Approve records listing `name`, with the claim hash they carry for it. -/
def Ledger.approvalsOf (l : Ledger) (name : String) : Array (LoadedRecord × ApproveRecord × String) :=
  l.records.filterMap fun r => do
    let .approve a := r.record | none
    let (_, claim) ← a.constants.find? (·.1 == name)
    return (r, a, claim)

def Ledger.isLive (l : Ledger) (recordHash : String) (signer : String) (name : String) : Bool :=
  l.cfg.allows signer && !l.withdrawn.contains (recordHash, name)

/-- Counting withdraws that cover `name`, with the approve record they withdraw. -/
def Ledger.withdrawalsOf (l : Ledger) (name : String) : Array CountingWithdraw :=
  l.withdraws.filter (·.constants.contains name)

end LeanBlame
