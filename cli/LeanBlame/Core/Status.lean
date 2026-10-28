/-
`leanblame status [--json]` and `leanblame blame NAME|ID`
(docs/design/03-trust-model.md "Validity", docs/design/06-versioning.md, docs/design/14-schemas.md §4).

Status reads the graphs `export` stored and never hashes (docs/design/04-architecture.md, "Storage").
Records name declarations by id, so an approval follows its declaration through a rename. Per
tagged declaration X of the current boundary list:
* state: `valid` if at least `required_signers` distinct signers have live approve records carrying
  X's current claim hash; else `outdated` if live records for X exist; else `unsigned`;
* change: for a declaration that is not valid, the causes of the move since the last live approval,
  found by comparing hash parts with the graph of the export and boundary list that record names
  (from the object store); unknown when this store lacks them;
* history: every record about X, each approval with what it is worth now (`Ledger.standing`);
* evidence: the `equiv` proof that X's current claim means what a live approval of it meant, if
  `equiv` wrote one;
* blocked_by: tagged dependencies, followed transitively, that are not valid;
* proof: for a declaration with role `proved`, the assumptions it rests on (computed by `export`):
  `proven` when each is standard or a tagged, `assumed` declaration that is valid, `open` otherwise
  (an incomplete proof such as `sorry`, or an assumption that is neither, which is `unpermitted`);
  `n/a` for the rest. Which assumptions are standard and which stand for a missing proof is
  recorded in the graph by `export`, from the proof assistant (`Core.Backend`);
* tagged_deps, untagged_deps: the tagged declarations at the cut, and the untagged declarations X
  uses directly, with their modules.
Besides: every record, and the untagged declarations of this library that tagged ones use. `--json`
prints all of it and nothing else; the text form prints one line per declaration, after warnings
about those untagged declarations and the unpermitted axioms.
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
  Graph.load? root exportHash boundary (← loadBoundary root boundary)

def graph (root : System.FilePath) (exportHash boundary : String) : IO Core.Hashed := do
  let some h ← graph? root exportHash boundary
    | fail s!"no graph for export {exportHash} and boundary list {boundary}"
  return h

/-- The graph of the export and boundary list approve record `r` names: `none` when this store lacks
them (the record was made in another store). An error when the store has them but no graph of
them, which `export` always writes, or when a declaration of the record does not have its id and
claim there. -/
def recordGraph? (root : System.FilePath) (r : LoadedRecord) (a : ApproveRecord) :
    IO (Option Core.Hashed) := do
  unless (← (Store.objectPath root .exports a.exportHash).pathExists) &&
      (← (Store.objectPath root .boundaries a.boundary).pathExists) do
    return none
  let some h ← graph? root a.exportHash a.boundary
    | fail s!"record {r.path}: the store has its export and boundary list but no graph of them"
  let ids : Std.HashMap String String := h.boundary.declarations.foldl (init := {}) fun m d => m.insert d.name d.id
  for c in a.constants do
    unless ids[c.name]? == some c.id && (h.nodes[c.name]?.map (·.claim)) == some c.claim do
      fail s!"record {r.path}: {c.name} does not have id {c.id} and claim {c.claim} in the export it names"
  return some h

/-- The graph of the last `export`. -/
def currentGraph (root : System.FilePath) (cur : Store.Current) : IO Core.Hashed := do
  let some h ← graph? root cur.exportHash cur.boundary
    | fail "no graph for the current export; run `leanblame export`"
  return h

/-- The records about declaration `id`, in (date, record id) order; `current` is its claim now,
`none` when it is not on the current boundary list. -/
def historyOf (ledger : Ledger) (id : String) (current : Option String) : Array HistoryEntry :=
  (ledger.entriesOf id).map fun
    | .approve r a c =>
      { record := r.hash, action := .approve, signer := a.signer, date := a.date, name := c.name
        claim := c.claim, note := a.note
        standing := some (ledger.standing r a.signer id c.claim current) }
    | .withdraw r w c =>
      { record := r.hash, action := .withdraw, signer := w.signer, date := w.date, name := c.name
        claim := c.claim, note := w.note, standing := none }

/-- The live approve records of declaration `id`, in (date, id) order, with its entry in each. -/
def liveApprovals (ledger : Ledger) (id : String) : Array (LoadedRecord × ApproveRecord × ApprovedConstant) :=
  (ledger.approvalsOf id).filter fun (r, a, _) => ledger.isLive r a.signer id

/-- The `equiv` proof that declaration `id` at `claim` means what a live approval of it meant. -/
def evidenceFor (root : System.FilePath) (ledger : Ledger) (id claim : String) : IO (Option String) := do
  let some e ← Store.evidence? root claim | return none
  unless e.id == id do
    fail s!"{Store.evidencePath root claim}: the evidence is for declaration {e.id}, not {id}"
  return if (liveApprovals ledger id).any (·.1.hash == e.oldRecord) then some e.proof else none

/-- Everything `status` computes. -/
structure Result where
  /-- The last `export`; `new` is its graph. -/
  cur : Store.Current
  new : Core.Hashed
  report : StatusReport
  /-- Live approve records carrying the current claim of some tagged declaration, sorted. -/
  validRecords : Array String

/-- A theorem's axioms against the permitted ones (docs/design/07): `proven` when each is in
`standard` or `signed`, `open` otherwise; and the axioms that are neither in `incomplete` nor
permitted. -/
def classifyAxioms (standard incomplete : Array String) (axioms : Array String)
    (signed : String → Bool) : ProofStatus × Array String :=
  let permitted (a : String) := standard.contains a || signed a
  (if axioms.all permitted then .proven else .«open»,
   axioms.filter fun a => !incomplete.contains a && !permitted a)

/-- The untagged declarations of this library that tagged declarations of it use, each with those
users: `owned` lists the library's taggable constants, from `export`. `closures` holds
`Walk.closureOf` of each tagged declaration. -/
def untaggedInLibrary (h : Core.Hashed) (closures : Std.HashMap String (Array String × Array String))
    (modules : Array String) (owned : Std.HashSet String) : Array (String × Array String) := Id.run do
  let mut users : Std.HashMap String (Array String) := {}
  for d in h.boundary.declarations do
    unless modules.contains d.module do continue
    for u in (closures[d.name]?.map (·.2)).getD #[] do
      if owned.contains u then users := users.alter u fun xs => some ((xs.getD #[]).push d.name)
  return (Core.sortNames (users.fold (init := #[]) fun acc u _ => acc.push u)).map fun u =>
    (u, Core.sortNames (users.getD u #[]))

/-- The status report of the last `export` against `ledger`. -/
def compute (root : System.FilePath) (ledger : Ledger) : IO Result := do
  let cur ← Store.readCurrent root
  let new ← currentGraph root cur
  -- Graphs of the exports approvals name, by (export, boundary list); `none`: not in this store.
  let mut olds : Std.HashMap (String × String) (Option Core.Hashed) := {}
  -- Pass 1: state, change, signers, history, dependencies.
  let mut states : Std.HashMap String State := {}
  let mut validRecords : Array String := #[]
  let mut entries : Array StatusDecl := #[]
  -- Each tagged declaration's closure, walked once: (cut, untagged declarations).
  let mut closures : Std.HashMap String (Array String × Array String) := {}
  for d in new.boundary.declarations do
    let some node := new.nodes[d.name]? | fail s!"the current graph has no node for {d.name}"
    let claim := node.claim
    let live := liveApprovals ledger d.id
    let matching := live.filter fun (_, _, c) => c.claim == claim
    let signers := ((matching.map fun (_, a, _) => a.signer).qsort (· < ·)).eraseReps
    validRecords := validRecords ++ matching.map (·.1.hash)
    let state :=
      if signers.size ≥ ledger.cfg.requiredSigners then State.valid
      else if live.isEmpty then .unsigned else .outdated
    let evidence ← evidenceFor root ledger d.id claim
    let closure := Walk.closureOf new d.name
    -- Causes: against the graph of the last live approval (the ledger is in (date, id) order).
    let mut change : Option (Array Change) := some #[]
    if let some (lastRec, last, c) := live.back? then
      if state != .valid && c.claim != claim then
        let key := (last.exportHash, last.boundary)
        unless olds.contains key do olds := olds.insert key (← recordGraph? root lastRec last)
        change := none
        if let some (some old) := olds[key]? then
          match Walk.compare old new c.name d.name closure with
          | .ok cmp => change := some (cmp.changes d.name)
          | .error e => fail s!"record {lastRec.path}: {e}"
    let (cut, untagged) := closure
    let mut untaggedDeps := #[]
    for u in node.decl.deps do
      if new.isTagged u then continue
      let some un := new.nodes[u]? | fail s!"the current graph has no node for {u}"
      untaggedDeps := untaggedDeps.push { name := u, module := un.decl.module }
    closures := closures.insert d.name closure
    states := states.insert d.name state
    entries := entries.push {
      decl := d, claim, state, change, signers, history := historyOf ledger d.id claim
      blockedBy := #[]
      proof := { status := .na }
      evidence
      taggedDeps := cut
      untaggedDeps
      -- Constants hashed into the claim, proofs excluded: X, its untagged closure, its cut.
      closureSize := 1 + cut.size + untagged.size }
  -- Pass 2: blocked_by, following tagged dependencies transitively; the axiom report.
  let cutOf (n : String) : IO (Array String) := do
    let some (cut, _) := closures[n]? | fail s!"{n} is not on the current boundary list"
    return cut
  let signed (a : String) : Bool := states[a]? == some .valid &&
    match new.nodes[a]? with | some nd => nd.decl.role == .assumed | none => false
  let mut decls := #[]
  for sd in entries do
    let d := sd.decl
    let proof : ProofReport ← if d.role != .proved then pure sd.proof else do
      let some axioms := new.axioms[d.name]? | fail s!"the current graph has no axioms for {d.name}"
      let (status, unpermitted) := classifyAxioms new.standard new.incomplete axioms signed
      pure { status, axioms, unpermitted }
    let mut seen : Std.HashSet String := {}
    let mut blocked : Array String := #[]
    let mut stack ← cutOf d.name
    while h : stack.size > 0 do
      let y := stack[stack.size - 1]
      stack := stack.pop
      if seen.contains y || y == d.name then continue
      seen := seen.insert y
      let some s := states[y]? | fail s!"{y} is not on the current boundary list"
      if s != .valid then blocked := blocked.push y
      stack := stack ++ (← cutOf y)
    decls := decls.push { sd with blockedBy := Core.sortNames blocked, proof }
  let owned : Std.HashSet String :=
    (← Store.readString root .owned cur.owned).lines.fold (·.insert ·.copy) {}
  let report : StatusReport := {
    library := new.boundary.library, commit := cur.commit, toolchain := cur.toolchain, deps := cur.deps
    exportHash := cur.exportHash, boundary := cur.boundary, generated := ← Std.Time.Timestamp.nowSeconds
    standard := new.standard, declarations := decls, records := ledger.records
    untaggedInLibrary := untaggedInLibrary new closures (cur.modules.map (·.name)) owned }
  return { cur, new, report, validRecords := (validRecords.qsort (· < ·)).eraseReps }

/-- The warnings the text form prints: untagged declarations of this library that tagged ones use,
and theorems resting on unpermitted axioms. -/
def warnings (r : StatusReport) : Array String :=
  r.untaggedInLibrary.map (fun (u, users) =>
    s!"warning: untagged {u} of this library is used by tagged {", ".intercalate users.toList}; tag it so it gets its own signer") ++
  r.declarations.flatMap fun d => d.proof.unpermitted.map fun a =>
    s!"warning: theorem {d.decl.name} rests on axiom {a}, which is neither standard nor tagged and signed"

/-- `change=cause:names;..`, as `status` and `diff` print causes. -/
def changeText (cs : Array Change) : String :=
  "change=" ++ ";".intercalate (cs.toList.map fun c => toString c.cause ++ ":" ++ ",".intercalate c.names.toList)

/-- One line per declaration: `NAME STATE [evidence=..] [blocked-by=..] [change=cause:names;..]`;
the evidence is shown while there is something to sign. -/
def textLine (d : StatusDecl) : String :=
  let parts := #[d.decl.name, toString d.state] ++
    (if d.state == .valid then #[] else (d.evidence.toList.map fun e => s!"evidence={e}").toArray) ++
    (if d.blockedBy.isEmpty then #[] else #[s!"blocked-by={",".intercalate d.blockedBy.toList}"]) ++
    (match d.change with
      | none => #["change=unknown"]
      | some cs => if cs.isEmpty then #[] else #[changeText cs])
  " ".intercalate parts.toList

def run (root : System.FilePath) (json : Bool) : IO UInt32 := do
  let r ← compute root (← Ledger.load root)
  if json then
    IO.print (jsonText r.report)
  else
    for w in warnings r.report do IO.eprintln w
    let decls := r.report.declarations
    for d in decls do IO.println (textLine d)
    let count (s : State) := (decls.filter (·.state == s)).size
    let blocked := (decls.filter (!·.blockedBy.isEmpty)).size
    IO.println s!"{decls.size} tagged: {count .valid} valid, {count .outdated} outdated, {count .unsigned} unsigned; {blocked} blocked"
  return 0

/-- The id of the declaration records name `key`: an id, or a name a record gives it. -/
def recordedId (ledger : Ledger) (key : String) : IO String := do
  if ledger.entries.contains key then return key
  let ids := ledger.entries.fold (init := #[]) fun acc id es =>
    if es.any (fun | .approve _ _ c | .withdraw _ _ c => c.name == key) then acc.push id else acc
  match ids with
  | #[id] => return id
  | #[] => fail s!"{key} is not on the current boundary list and no record mentions it"
  | _ => fail s!"records name several declarations {key}: {", ".intercalate ids.toList}"

/-- `blame NAME` or `blame ID`: who signed it, when, at which claim hash, and what each approval is
worth now. -/
def blame (root : System.FilePath) (key : String) : IO UInt32 := do
  let ledger ← Ledger.load root
  let current? ← if (← (Store.currentPath root).pathExists) then
      some <$> compute root ledger
    else pure none
  let decls := (current?.map (·.report.declarations)).getD #[]
  let (id, decl?) ← match decls.filter fun d => d.decl.name == key || d.decl.id == key with
    | #[d] => pure (d.decl.id, some d)
    | #[] => pure (← recordedId ledger key, none)
    | _ => fail s!"{key} is the name of one declaration and the id of another"
  match decl? with
  | some d =>
    IO.println s!"{d.decl.name}  {d.decl.kind}  {d.state}  claim {d.claim}"
    IO.println s!"  id: {d.decl.id}"
    unless d.signers.isEmpty do IO.println s!"  signed by: {", ".intercalate d.signers.toList}"
    unless d.blockedBy.isEmpty do IO.println s!"  blocked by: {", ".intercalate d.blockedBy.toList}"
  | none => IO.println s!"{id}  (not on the current boundary list)"
  for h in historyOf ledger id (decl?.map (·.claim)) do
    let renamed := if decl?.any (·.decl.name == h.name) then "" else s!"  as {h.name}"
    let standing := (h.standing.map (s!" {·}")).getD ""
    IO.println s!"  {h.date.toIso}  {h.action}  {h.signer}{renamed}  claim {h.claim}  record {h.record}{standing}"
    if let some note := h.note then IO.println s!"      note: {note}"
  return 0

end LeanBlame.Status
