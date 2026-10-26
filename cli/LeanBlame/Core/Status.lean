/-
`leanblame status [--json]` and `leanblame blame NAME`
(docs/design/03-trust-model.md "Validity", docs/design/06-versioning.md, docs/design/14-schemas.md §4).

Status reads the graphs `export` stored and never hashes (docs/design/15-generic-core.md, §9).
Per tagged declaration X of the current boundary list:
* state: `valid` if at least `required_signers` distinct signers have live approve
  records carrying X's current claim hash; else `outdated` if live records for X
  exist; else `unsigned`;
* change: for a declaration that is not valid, the causes of the move since the
  last live approval, found by comparing hash parts with the graph of the export
  and boundary list that record names (from the object store);
* evidence: the `equiv` proof that X's current claim means what its last live
  approval meant, if `equiv` wrote one;
* blocked_by: tagged dependencies, followed transitively, that are not valid;
* proof: for a declaration with role `proved`, the assumptions it rests on (computed by `export`):
  `proven` when each is standard or a tagged, `assumed` declaration that is valid, `open` otherwise
  (an incomplete proof such as `sorry`, or an assumption that is neither, which also gets a
  warning); `n/a` for the rest. Which assumptions are standard and which stand for a missing proof
  is recorded in the graph by `export`, from the proof assistant (`Core.Backend`).
-/
import LeanBlame.Core.Records
import LeanBlame.Core.Walk

namespace LeanBlame.Status

def loadBoundary (root : System.FilePath) (hash : String) : IO BoundaryList := do
  match BoundaryList.parse (← Store.readString root .boundaries hash) with
  | .ok b => return b
  | .error e => fail s!"boundary list {hash}: {e}"

/-- The graph of export `exportHash` against boundary list `boundary`, from the object store. -/
def graph? (root : System.FilePath) (exportHash boundary : String) : IO (Option Core.Hashed) := do
  Graph.load? root exportHash (← loadBoundary root boundary)

/-- The graph of an export a record names. -/
def graph (root : System.FilePath) (exportHash boundary : String) : IO Core.Hashed := do
  let some h ← graph? root exportHash boundary | fail s!"no graph for export {exportHash}"
  return h

/-- The graph of the last `export`. -/
def currentGraph (root : System.FilePath) (cur : Store.Current) : IO Core.Hashed := do
  let some h ← graph? root cur.exportHash cur.boundary
    | fail "no graph for the current export; run leanblame export"
  return h

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
  /-- The last `export`; `new` is its graph. -/
  cur : Store.Current
  new : Core.Hashed
  report : StatusReport
  /-- Untagged declarations of this library used by tagged ones (docs/design/03), and theorems resting on
  axioms that are not permitted. -/
  warnings : Array String := #[]
  /-- Live approve records carrying the current claim of some tagged declaration, sorted. -/
  validRecords : Array String := #[]
  /-- (theorem, axiom) pairs where the axiom is neither standard nor a valid tagged axiom. -/
  unpermitted : Array (String × String) := #[]

/-- A theorem's axioms against the permitted ones (docs/design/07): `proven` when each is in
`standard` or `signed`, `open` otherwise; and the axioms that are neither in `incomplete` nor
permitted. -/
def classifyAxioms (standard incomplete : Array String) (axioms : Array String)
    (signed : String → Bool) : ProofStatus × Array String :=
  let permitted (a : String) := standard.contains a || signed a
  (if axioms.all permitted then .proven else .«open»,
   axioms.filter fun a => !incomplete.contains a && !permitted a)

/-- `status` warns when a tagged declaration of this library uses an untagged one of it that could
be tagged: `owned` lists the library's taggable constants, from `export`. `closures` holds
`Walk.closureOf` of each tagged declaration. -/
def untaggedWarnings (h : Core.Hashed) (closures : Std.HashMap String (Array String × Array String))
    (modules : Array String) (owned : Std.HashSet String) : Array String := Id.run do
  let mut users : Std.HashMap String (Array String) := {}
  for d in h.boundary.declarations do
    unless modules.contains d.module do continue
    for u in (closures[d.name]?.map (·.2)).getD #[] do
      users := users.alter u fun xs => some ((xs.getD #[]).push d.name)
  let mut out := #[]
  for u in Core.sortNames (users.fold (init := #[]) fun acc u _ =>
      if owned.contains u then acc.push u else acc) do
    let xs := Core.sortNames (users.getD u #[])
    out := out.push s!"warning: untagged {u} of this library is used by tagged {", ".intercalate xs.toList}; tag it so it gets its own signer"
  return out

/-- The status report; `causes := false` leaves every `change` empty and reads no other graph, and
`warn := false` skips the untagged-dependency warnings. -/
def compute (root : System.FilePath) (ledger : Ledger) (causes := true) (warn := true) :
    IO Result := do
  let cur ← Store.readCurrent root
  let new ← currentGraph root cur
  -- Graphs of last live approvals; `none` remembers a failure, warned about once.
  let mut olds : Std.HashMap (String × String) (Option Core.Hashed) := {}
  -- Pass 1: state, change, signers, history.
  let mut states : Std.HashMap String State := {}
  let mut validRecords : Array String := #[]
  let mut entries : Array (BoundaryDecl × StatusDecl) := #[]
  -- Each tagged declaration's closure, walked once: (cut, untagged declarations).
  let mut closures : Std.HashMap String (Array String × Array String) := {}
  for d in new.boundary.declarations do
    let n := d.name
    let node := new.nodes[n]!
    let claim := node.claim
    let live := liveApprovals ledger n
    let matching := live.filter fun (_, _, c) => c == claim
    let signers := ((matching.map fun (_, a, _) => a.signer).qsort (· < ·)).eraseReps
    validRecords := validRecords ++ matching.map (·.1.hash)
    let state :=
      if signers.size ≥ ledger.cfg.requiredSigners then State.valid
      else if live.isEmpty then .unsigned else .outdated
    let evidence ← evidenceFor root ledger n claim
    let closure := Walk.closureOf new n
    -- Causes: against the graph of the last live approval (the ledger is in (date, id) order).
    let mut change : Array Change := #[]
    if let some (lastRec, last, lastClaim) := live.back? then
      if causes && state != .valid && lastClaim != claim then
        -- A record from elsewhere may name objects this store lacks.
        let key := (last.exportHash, last.boundary)
        unless olds.contains key do
          let old? ← try some <$> graph root last.exportHash last.boundary catch e => do
            IO.eprintln s!"warning: record {lastRec.hash}: {e}; causes unknown"
            pure none
          olds := olds.insert key old?
        if let some (some old) := olds[key]? then change := Walk.changes old new n closure
    let (cut, untagged) := closure
    closures := closures.insert n closure
    states := states.insert n state
    entries := entries.push (d, {
      id := d.id, module := d.module, kind := d.kind, role := d.role, informal := d.informal
      informalSource := d.informalSource, statement := d.statement
      claim, state, change, signers, history := historyOf ledger n
      blockedBy := #[]
      proof := { status := .na }
      evidence
      taggedDeps := cut
      -- Constants hashed into the claim, proofs excluded: X, its untagged closure, its cut.
      closureSize := 1 + cut.size + untagged.size })
  -- Pass 2: blocked_by, following tagged dependencies transitively; the axiom report.
  let cutOf (n : String) : Array String := (closures[n]?.map (·.1)).getD #[]
  let signed (a : String) : Bool := states[a]? == some .valid &&
    match new.nodes[a]? with | some nd => nd.decl.role == .assumed | none => false
  let mut decls := #[]
  let mut warnings := #[]
  let mut unpermitted := #[]
  for (d, sd) in entries do
    let n := d.name
    let proof : ProofReport ← if d.role != .proved then pure sd.proof else do
      let some axioms := new.axioms[n]? | fail s!"internal: no axiom data for {n}"
      let (status, bad) := classifyAxioms new.standard new.incomplete axioms signed
      for a in bad do
        warnings := warnings.push s!"warning: theorem {n} rests on axiom {a}, which is neither standard nor tagged and signed"
        unpermitted := unpermitted.push (n, a)
      pure { status, axioms }
    let mut seen : Std.HashSet String := {}
    let mut blocked : Array String := #[]
    let mut stack := cutOf n
    while h : stack.size > 0 do
      let y := stack[stack.size - 1]
      stack := stack.pop
      if seen.contains y || y == n then continue
      seen := seen.insert y
      if states[y]?.getD .unsigned != .valid then blocked := blocked.push y
      stack := stack ++ cutOf y
    decls := decls.push (n, { sd with blockedBy := Core.sortNames blocked, proof })
  let report : StatusReport := {
    library := new.boundary.library, commit := new.boundary.commit, exportHash := cur.exportHash
    generated := ← Std.Time.Timestamp.nowSeconds, declarations := decls }
  let untagged ← if !warn then pure #[] else do
    let owned : Std.HashSet String := (← Store.readString root .owned cur.owned).lines.fold (·.insert ·.copy) {}
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
  if json then
    IO.print (jsonText r.report)
  else
    let decls := r.report.declarations
    for (n, d) in decls do IO.println (textLine n d)
    let count (s : State) := (decls.filter (·.2.state == s)).size
    let blocked := (decls.filter (!·.2.blockedBy.isEmpty)).size
    IO.println s!"{decls.size} tagged: {count .valid} valid, {count .outdated} outdated, {count .unsigned} unsigned; {blocked} blocked"
  return 0

/-- `blame NAME` or `blame ID`: who signed it, when, at which claim hash. An id stands for the
declaration that carries it now. -/
def blame (root : System.FilePath) (nameOrId : String) : IO UInt32 := do
  let ledger ← Ledger.load root
  let current? ← if (← (Store.currentPath root).pathExists) then
      some <$> compute root ledger (causes := false) (warn := false)
    else pure none
  let name := (current?.bind fun r =>
    (r.report.declarations.find? (·.2.id == some nameOrId)).map (·.1)).getD nameOrId
  let decl? := current?.bind fun r => (r.report.declarations.find? (·.1 == name)).map (·.2)
  let history := historyOf ledger name
  if decl?.isNone && history.isEmpty then
    fail s!"{name} is not on the boundary list and no record mentions it"
  match decl? with
  | some d =>
    IO.println s!"{name}  {d.kind}  {d.state}  claim {d.claim}"
    if let some id := d.id then IO.println s!"  id: {id}"
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
