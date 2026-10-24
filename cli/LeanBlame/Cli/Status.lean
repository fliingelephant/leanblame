/-
`leanblame status [--json]` and `leanblame blame NAME`
(docs/design/03-trust-model.md "Validity", docs/design/06-versioning.md, docs/design/14-schemas.md §4).

Per tagged declaration X of the current boundary list:
* state: `valid` if at least `required_signers` distinct signers have live approve
  records carrying X's current claim hash; else `outdated` if live records for X
  exist; else `unsigned`;
* change: for a declaration that is not valid, the causes of the move since the
  last live approval, found by hashing the export and boundary list that record
  names (from the object store) and comparing hash parts;
* evidence: the `equiv` proof that X's current claim means what its last live
  approval meant, if `equiv` wrote one;
* blocked_by: tagged dependencies, followed transitively, that are not valid;
* proof: for a theorem, the axioms it rests on (computed by `export`): `proven` when each is
  standard or a tagged `axiom` that is valid, `open` otherwise (`sorryAx`, or an axiom that is
  neither, which also gets a warning); `n/a` for the rest.
-/
import LeanBlame.Cli.Cache
import LeanBlame.Cli.Records

namespace LeanBlame.Status

open Lean

def loadBoundary (root : System.FilePath) (hash : String) : IO BoundaryList := do
  match BoundaryList.parse (← Store.readString root hash) with
  | .ok b => return b
  | .error e => fail s!"boundary list {hash}: {e}"

def loadExported (root : System.FilePath) (hash : String) : IO LeanExport.ExportedEnv := do
  let p := Store.objectPath root hash
  unless ← p.pathExists do fail s!"export {hash} is not in the store"
  LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk p .read))

/-- Export `exportHash` hashed against boundary list `boundary`, from the local cache or else from
the object store (and then cached). -/
def hashed (root : System.FilePath) (exportHash boundary : String) : IO Walk.Hashed := do
  let b ← loadBoundary root boundary
  if let some h ← Cache.load? root exportHash b then return h
  let h ← try Walk.hashExport (← loadExported root exportHash) b
    catch e => fail s!"cannot hash export {exportHash}: {e}"
  Cache.save root exportHash h
  return h

/-- Whether the toolchain's `leanchecker` replays the export file `path` without error: the
kernel check `release` and `equiv` run on what they store. -/
def kernelAccepts (path : System.FilePath) : IO Bool := do
  unless ← path.pathExists do fail s!"{path} is not in the store"
  let leanchecker := (← findSysroot) / "bin" / "leanchecker" |>.addExtension System.FilePath.exeExtension
  let child ← IO.Process.spawn { cmd := leanchecker.toString, stdin := .null, stdout := .null
                                 args := #["--silent", "--from-export", path.toString] }
  return (← child.wait) == 0

/-- The approve records listing `name` and the counting withdraws covering it, in (date, id)
order. -/
def historyOf (ledger : Ledger) (name : String) : Array HistoryEntry :=
  (ledger.entriesOf name).map fun
    | .approve r a claim =>
      { record := r.hash, action := .approve, signer := a.signer, date := a.date, claim
        note := a.note }
    | .withdraw r w =>
      let claim := match ((ledger.byId[w.refersTo]?).map (·.record) : Option Record) with
        | some (.approve a) => (a.constants.find? (·.1 == name)).map (·.2)
        | _ => none
      { record := r.hash, action := .withdraw, signer := w.signer, date := w.date, claim
        note := w.note }

/-- The live approve records listing `name`, in (date, id) order, with the claim each carries. -/
def liveApprovals (ledger : Ledger) (name : String) : Array (LoadedRecord × ApproveRecord × String) :=
  (ledger.approvalsOf name).filter fun (r, a, _) => ledger.isLive r.hash a.signer name

/-- The `equiv` proof that `name` at `claim` means what a live approval of it meant, if any. -/
def evidenceFor (root : System.FilePath) (ledger : Ledger) (name claim : String) : IO (Option String) := do
  let some (proof, record) ← Store.evidence? root name claim | return none
  return if (liveApprovals ledger name).any (·.1.hash == record) then some proof else none

/-- Everything `status` computes. -/
structure Result where
  /-- The last `export`, hashed. -/
  cur : Store.Current
  new : Walk.Hashed
  report : StatusReport
  /-- Untagged declarations of this library used by tagged ones (docs/design/03), and theorems resting on
  axioms that are not permitted. -/
  warnings : Array String := #[]
  /-- Live approve records carrying the current claim of some tagged declaration, sorted. -/
  validRecords : Array String := #[]
  /-- (theorem, axiom) pairs where the axiom is neither standard nor a valid tagged axiom. -/
  unpermitted : Array (Name × Name) := #[]

/-- A theorem's axioms against the permitted ones (docs/design/07): `proven` when each is standard or
`signed`, `open` otherwise; and the axioms that are neither `sorryAx` nor permitted. -/
def classifyAxioms (axioms : Array Name) (signed : Name → Bool) : ProofStatus × Array Name :=
  let permitted (a : Name) := Walk.standardAxioms.contains a || signed a
  (if axioms.all permitted then .proven else .«open»,
   axioms.filter fun a => a != ``sorryAx && !permitted a)

/-- `status` warns when a tagged declaration of this library uses an untagged one of it that could
be tagged: `owned` lists the library's taggable constants, from `export`. `closures` holds
`Walk.closureOf` of each tagged declaration. -/
def untaggedWarnings (h : Walk.Hashed) (closures : Std.HashMap Name (Array Name × Array Name))
    (modules : Array String) (owned : Std.HashSet String) : Array String := Id.run do
  let mut users : Std.HashMap Name (Array Name) := {}
  for (x, d) in h.declarations do
    unless modules.contains d.module do continue
    for u in (closures[x]?.map (·.2)).getD #[] do
      users := users.alter u fun xs => some ((xs.getD #[]).push x)
  let mut out := #[]
  for u in Walk.sortNames (users.fold (init := #[]) fun acc u _ =>
      if owned.contains u.toString then acc.push u else acc) do
    let xs := Walk.sortNames (users.getD u #[])
    out := out.push s!"warning: untagged {u} of this library is used by tagged {", ".intercalate (xs.toList.map toString)}; tag it so it gets its own signer"
  return out

/-- The status report; `causes := false` leaves every `change` empty and hashes no other export, and
`warn := false` skips the untagged-dependency warnings. -/
def compute (root : System.FilePath) (ledger : Ledger) (causes := true) (warn := true) :
    IO Result := do
  let cur ← Store.readCurrent root
  let new ← hashed root cur.exportHash cur.boundary
  -- Exports of last live approvals, hashed; `none` remembers a failure, warned about once.
  let mut olds : Std.HashMap (String × String) (Option Walk.Hashed) := {}
  -- Pass 1: state, change, signers, history.
  let mut states : Std.HashMap Name State := {}
  let mut validRecords : Array String := #[]
  let mut entries : Array (Name × BoundaryDecl × StatusDecl) := #[]
  -- Each tagged declaration's closure, walked once: (cut, untagged constants).
  let mut closures : Std.HashMap Name (Array Name × Array Name) := {}
  for (n, d) in new.declarations do
    let node := new.nodes[n]!
    let claim := node.claim
    let live := liveApprovals ledger d.name
    let matching := live.filter fun (_, _, c) => c == claim
    let signers := ((matching.map fun (_, a, _) => a.signer).qsort (· < ·)).eraseReps
    validRecords := validRecords ++ matching.map (·.1.hash)
    let state :=
      if signers.size ≥ ledger.cfg.requiredSigners then State.valid
      else if live.isEmpty then .unsigned else .outdated
    let evidence ← evidenceFor root ledger d.name claim
    let closure := Walk.closureOf new n
    -- Causes: against the export of the last live approval (the ledger is in (date, id) order).
    let mut change : Array Change := #[]
    if let some (lastRec, last, lastClaim) := live.back? then
      if causes && state != .valid && lastClaim != claim then
        -- A record from elsewhere may name objects this store lacks, or that do not hash.
        let key := (last.exportHash, last.boundary)
        unless olds.contains key do
          let old? ← try some <$> hashed root last.exportHash last.boundary catch e => do
            IO.eprintln s!"warning: record {lastRec.hash}: {e}; causes unknown"
            pure none
          olds := olds.insert key old?
        if let some (some old) := olds[key]? then change := Walk.changes old new n closure
    let (cut, untagged) := closure
    closures := closures.insert n closure
    states := states.insert n state
    entries := entries.push (n, d, {
      module := d.module, kind := d.kind, informal := d.informal, informalSource := d.informalSource
      claim, state, change, signers, history := historyOf ledger d.name
      blockedBy := #[]
      proof := { status := .na }
      evidence
      taggedDeps := cut.map (·.toString)
      -- Constants hashed into the claim, proofs excluded: X, its untagged closure, its cut.
      closureSize := 1 + cut.size + untagged.size })
  -- Pass 2: blocked_by, following tagged dependencies transitively; the axiom report.
  let cutOf (n : Name) : Array Name := (closures[n]?.map (·.1)).getD #[]
  let signed (a : Name) : Bool := states[a]? == some .valid &&
    match new.nodes[a]? with | some nd => nd.fields.kind == .«axiom» | none => false
  let mut decls := #[]
  let mut warnings := #[]
  let mut unpermitted := #[]
  for (n, d, sd) in entries do
    let proof : ProofReport ← if d.kind != .«theorem» then pure sd.proof else do
      let some axioms := new.axioms[n]? | fail s!"internal: no axiom data for {n}"
      let (status, bad) := classifyAxioms axioms signed
      for a in bad do
        warnings := warnings.push s!"warning: theorem {n} rests on axiom {a}, which is neither standard nor tagged and signed"
        unpermitted := unpermitted.push (n, a)
      pure { status, axioms := axioms.map toString }
    let mut seen : Std.HashSet Name := {}
    let mut blocked : Array Name := #[]
    let mut stack := cutOf n
    while h : stack.size > 0 do
      let y := stack[stack.size - 1]
      stack := stack.pop
      if seen.contains y || y == n then continue
      seen := seen.insert y
      if states[y]?.getD .unsigned != .valid then blocked := blocked.push y
      stack := stack ++ cutOf y
    decls := decls.push (n.toString,
      { sd with blockedBy := (Walk.sortNames blocked).map (·.toString), proof })
  let report : StatusReport := {
    library := new.boundary.library, commit := new.boundary.commit, exportHash := cur.exportHash
    generated := ← Std.Time.Timestamp.nowSeconds, declarations := decls }
  let untagged ← if !warn then pure #[] else do
    let owned : Std.HashSet String := (← Store.readString root cur.owned).lines.fold (·.insert ·.copy) {}
    pure (untaggedWarnings new closures cur.modules owned)
  return { cur, new, report, warnings := untagged ++ warnings
           validRecords := (validRecords.qsort (· < ·)).eraseReps, unpermitted }

/-- One line per declaration: `NAME STATE [evidence=..] [blocked-by=..] [change=cause:names;..]`;
the evidence is shown while there is something to sign. -/
def textLine (name : String) (d : StatusDecl) : String :=
  let parts := #[name, toString d.state] ++
    (if d.state == .valid then #[] else (d.evidence.toList.map fun e => s!"evidence={e}").toArray) ++
    (if d.blockedBy.isEmpty then #[] else #[s!"blocked-by={",".intercalate d.blockedBy.toList}"]) ++
    (if d.change.isEmpty then #[] else
      #["change=" ++ ";".intercalate (d.change.toList.map fun c =>
        toString c.cause ++ ":" ++ ",".intercalate c.names.toList)])
  " ".intercalate parts.toList

def run (root : System.FilePath) (json : Bool) : IO UInt32 := do
  let r ← compute root (← Ledger.load root)
  for w in r.warnings do IO.eprintln w
  let text := jsonText r.report
  -- Every run leaves a log in the object store.
  let logHash ← Store.putString root text
  IO.eprintln s!"leanblame: status log {logHash}"
  if json then
    IO.print text
  else
    let decls := r.report.declarations
    for (n, d) in decls do IO.println (textLine n d)
    let count (s : State) := (decls.filter (·.2.state == s)).size
    let blocked := (decls.filter (!·.2.blockedBy.isEmpty)).size
    IO.println s!"{decls.size} tagged: {count .valid} valid, {count .outdated} outdated, {count .unsigned} unsigned; {blocked} blocked"
  return 0

/-- `blame NAME`: who signed it, when, at which claim hash. -/
def blame (root : System.FilePath) (name : String) : IO UInt32 := do
  let ledger ← Ledger.load root
  let current? ← if (← (Store.currentPath root).pathExists) then
      some <$> compute root ledger (causes := false) (warn := false)
    else pure none
  let decl? := current?.bind fun r => (r.report.declarations.find? (·.1 == name)).map (·.2)
  let history := historyOf ledger name
  if decl?.isNone && history.isEmpty then
    fail s!"{name} is not on the boundary list and no record mentions it"
  match decl? with
  | some d =>
    IO.println s!"{name}  {d.kind}  {d.state}  claim {d.claim}"
    unless d.signers.isEmpty do IO.println s!"  signed by: {", ".intercalate d.signers.toList}"
    unless d.blockedBy.isEmpty do IO.println s!"  blocked by: {", ".intercalate d.blockedBy.toList}"
  | none => IO.println s!"{name}  (not on the current boundary list)"
  for h in history do
    let current := match decl?, h.claim with
      | some d, some c => if c == d.claim then " (current)" else ""
      | _, _ => ""
    let live := match h.action with
      | .approve =>
        let withdrawn := ledger.withdrawn.contains (h.record, name)
        if withdrawn then " withdrawn" else if ledger.cfg.allows h.signer then " live" else " signer-not-allowed"
      | .withdraw => ""
    IO.println s!"  {h.date.toIso}  {h.action}  {h.signer}  claim {h.claim.getD "-"}{current}  record {h.record}{live}"
    if let some note := h.note then IO.println s!"      note: {note}"
  return 0

end LeanBlame.Status
