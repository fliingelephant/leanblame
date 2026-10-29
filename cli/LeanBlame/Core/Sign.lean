/-
`leanblame init` and `leanblame sign` (docs/design/04-architecture.md, docs/design/05-records.md).

`sign` is the terminal dev path: it writes `local:` records only. Provider
logins (OpenReview, ORCID, GitHub) belong to the sign server.
-/
import LeanBlame.Core.Status

namespace LeanBlame.Sign

def init (root : System.FilePath) : IO UInt32 := do
  -- Create `path` unless it exists; `what` names it in the report.
  let ensure (path : System.FilePath) (what : String) (create : IO Unit) : IO Unit := do
    if ← path.pathExists then IO.println s!"exists   {what}"
    else
      create
      IO.println s!"created  {what}"
  ensure (root / Config.fileName) Config.fileName (IO.FS.writeFile (root / Config.fileName) Config.defaultText)
  ensure (root / "records") "records/" (IO.FS.createDirAll (root / "records"))
  -- The object store is local and large; keep it out of git.
  let gi := root / ".gitignore"
  let old := (← readFileIfExists gi).getD ""
  unless old.lines.any (fun l => l.trimAscii == ".leanblame/".toSlice || l.trimAscii == "/.leanblame/".toSlice) do
    let sep := if old.isEmpty || old.endsWith "\n" then "" else "\n"
    IO.FS.writeFile gi (old ++ sep ++ ".leanblame/\n")
    IO.println "updated  .gitignore (.leanblame/)"
  return 0

/-- The signer `--signer` names; there is no default. Only `local:` ids in this slice. -/
def resolveSigner (given? : Option String) : IO String := do
  let some s := given? | fail "sign needs --signer local:NAME: a record names who signs"
  unless isSignerId s do fail s!"signer must be provider:id, got `{s}`"
  unless s.startsWith "local:" do
    fail s!"{s}: the terminal writes local: records only; provider logins go through the sign server"
  return s

/-- The first records directory, relative to the library root: where new records go. -/
def recordsDir (cfg : Config) : IO System.FilePath := do
  let some d := (recordDirs cfg)[0]? | fail "leanblame.toml lists no records directory"
  return d

/-- Write a record under its hash into directory `dir` of the library at `root`; returns the record
id and its path relative to `root`. -/
def writeRecord (root dir : System.FilePath) (r : Record) : IO (String × System.FilePath) := do
  let text := r.toToml
  let hex := Sha256.hexOfString text
  let path := dir / (hex ++ ".toml")
  IO.FS.createDirAll (root / dir)
  -- A record is never overwritten: `writeNew` fails if the file exists.
  IO.FS.withFile (root / path) .writeNew (·.putStr text)
  return (mkHash hex, path)

/-- Approve: one record per module, at the claim hashes of the current export. `keys` name
declarations by name or id. -/
def approve (root : System.FilePath) (signer? : Option String) (module? : Option String)
    (keys : Array String) (note? : Option String) : IO UInt32 := do
  let ledger ← Ledger.load root
  let signer ← resolveSigner signer?
  let cur ← Store.readCurrent root
  let graph ← Status.currentGraph root cur
  let boundary := graph.boundary
  let some commit := cur.commit
    | fail "the current export has uncommitted changes; commit them and export again: a record names the commit it signs"
  let selected ← if !keys.isEmpty then
      keys.mapM fun k => do
        let some d ← IO.ofExcept (boundary.find? k) | fail s!"{k} is not on the boundary list"
        pure d
    else if let some m := module? then do
      let ds := boundary.declarations.filter (·.module == m)
      if ds.isEmpty then fail s!"no tagged declarations in module {m}"
      pure ds
    else
      -- Default: every tagged declaration of the library's own modules.
      pure <| boundary.declarations.filter fun d => cur.modules.contains d.module
  if selected.isEmpty then fail "nothing to sign"
  let modules := dedup (selected.map (·.module))
  let dir ← recordsDir ledger.cfg
  let date ← Std.Time.Timestamp.nowSeconds
  for m in modules.qsort (· < ·) do
    let mut constants : Array ApprovedConstant := #[]
    for d in selected.filter (·.module == m) do
      if constants.any (·.id == d.id) then continue
      let some node := graph.nodes[d.name]? | fail s!"the current graph has no node for {d.name}"
      -- The `equiv` proof the signer relies on, if there is one.
      let evidence ← Status.evidenceFor root ledger d.id node.claim
      constants := constants.push { id := d.id, name := d.name, claim := node.claim, evidence }
    let r : Record := .approve {
      signer, date, module := m, commit, toolchain := cur.toolchain, deps := cur.deps
      exportHash := cur.exportHash, boundary := cur.boundary
      constants := constants.qsort (·.name < ·.name), note := note? }
    let (id, path) ← writeRecord root dir r
    IO.println s!"approve {id} {path} ({constants.size} declarations of {m})"
  return 0

/-- Withdraw some or all declarations of one of your approve records; `keys?` names them by name or
id. -/
def withdraw (root : System.FilePath) (signer? : Option String) (ref : String)
    (keys? : Option (Array String)) (note? : Option String) : IO UInt32 := do
  let ledger ← Ledger.load root
  let signer ← resolveSigner signer?
  let refersTo ← recordId ref
  let constants? ← keys?.mapM fun keys => do
    if keys.isEmpty then fail "--constants lists no declaration; leave it out to withdraw all"
    let some { record := .approve a, .. } := ledger.byId[refersTo]?
      | fail s!"cannot withdraw: {refersTo} is no approve record"
    keys.mapM fun k => match a.constants.filter fun c => c.id == k || c.name == k with
      | #[c] => pure c.id
      | #[] => fail s!"cannot withdraw: {k} is not in record {refersTo}"
      | _ => fail s!"{k} is the name of one declaration of record {refersTo} and the id of another"
  let w : WithdrawRecord := { signer, date := ← Std.Time.Timestamp.nowSeconds, refersTo, constants := constants?, note := note? }
  if let .error ps := withdrawCovers ledger.byId w then
    fail s!"cannot withdraw: {"; ".intercalate ps.toList}"
  let (id, path) ← writeRecord root (← recordsDir ledger.cfg) (.withdraw w)
  IO.println s!"withdraw {id} {path} (refers to {refersTo})"
  return 0

end LeanBlame.Sign
