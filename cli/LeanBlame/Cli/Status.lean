/-
`leanblame status [--base EXPORT] [--json]` and `leanblame blame NAME`
(docs/03-trust-model.md "Validity", docs/06-versioning.md, docs/14-schemas.md §4).

Per tagged declaration X of the current boundary list:
* state: `valid` if at least `required_signers` distinct signers have live approve
  records carrying X's current claim hash; else `outdated` if live records for X
  exist; else `unsigned`;
* flags: `withdrawn` if a counting withdraw ever covered X (`equiv-proven` needs
  `equiv`, not in this slice);
* change: for a declaration that is not valid, the causes of the move since the
  last live approval, found by hashing the export and boundary list that record
  names (from the object store) and comparing hash parts; with `--base A`, the
  causes since export A, for every declaration whose claim differs from A's;
* blocked_by: tagged dependencies, followed transitively, that are not valid;
* proof: `unchecked` for theorems (no axiom report in this slice), `n/a` otherwise.
-/
import LeanBlame.Cli.Records
import LeanBlame.Cli.Store
import LeanBlame.Cli.Walk

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

/-- Hashed exports, by (export, boundary list). -/
abbrev Cache := IO.Ref (Std.HashMap (String × String) Walk.Hashed)

def hashed (root : System.FilePath) (cache : Cache) (exportHash boundary : String) :
    IO Walk.Hashed := do
  if let some h := (← cache.get)[(exportHash, boundary)]? then return h
  let b ← loadBoundary root boundary
  let exported ← loadExported root exportHash
  let h ← try Walk.hashExport exported b
    catch e => fail s!"cannot hash export {exportHash}: {e}"
  cache.modify (·.insert (exportHash, boundary) h)
  return h

/--
The boundary list to compare with for `--base A`: the one of the latest local `export` of `A`,
else the one of the latest record naming `A`. A docstring edit leaves the export unchanged, so
several lists can pair with one export; `status` then says which one it took.
-/
def boundaryForExport (root : System.FilePath) (ledger : Ledger) (exportHash : String) :
    IO String := do
  let fromLog ← Store.boundariesForExport root exportHash
  let named := ledger.records.filterMap fun r => match r.record with
    | .approve a => if a.exportHash == exportHash then some (a.date, r.hash, a.boundary) else none
    | .withdraw _ => none
  let fromRecords := (named.qsort fun x y => x.1 > y.1 || (x.1 == y.1 && x.2.1 > y.2.1)).map (·.2.2)
  let candidates := (fromLog ++ fromRecords).foldl
    (fun acc b => if acc.contains b then acc else acc.push b) #[]
  let some b := candidates[0]? | fail s!"no boundary list known for export {exportHash}"
  if candidates.size > 1 then
    let source := if fromLog.contains b then "the latest local export" else "the latest record"
    IO.eprintln s!"warning: export {exportHash} pairs with {candidates.size} boundary lists (docstring edits); comparing with {b}, from {source}"
  return b

def historyOf (ledger : Ledger) (name : String) : Array HistoryEntry :=
  let approvals := (ledger.approvalsOf name).map fun (r, a, claim) =>
    { record := r.hash, action := "approve", signer := a.signer, date := a.date
      claim := some claim, note := a.note : HistoryEntry }
  let withdrawals := (ledger.withdrawalsOf name).map fun w =>
    let claim := (ledger.approves[w.withdraw.refersTo]?).bind fun (_, a) =>
      (a.constants.find? (·.1 == name)).map (·.2)
    { record := w.loaded.hash, action := "withdraw", signer := w.withdraw.signer
      date := w.withdraw.date, claim, note := w.withdraw.note : HistoryEntry }
  (approvals ++ withdrawals).qsort fun x y =>
    x.date < y.date || (x.date == y.date && x.record < y.record)

/-- Everything `status` computes. -/
structure Result where
  report : StatusReport
  /-- Records that did not parse: path and problems. -/
  badRecords : Array (System.FilePath × Array String)
  /-- Untagged declarations of this library used by tagged ones (docs/03). -/
  warnings : Array String := #[]

/--
Constants Lean generates, which are never tagged and never warned about (docs/03): compiler
auxiliaries (`match_n`, `_proof_n`, `_unary`, …), recursors, constructors, and everything
derived from a tagged declaration (`T.casesOn`, `T.mk.injEq`, `f.match_1`, …).
-/
def isGenerated (h : Walk.Hashed) (u : Name) : Bool :=
  let suffixes := #["rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow",
    "noConfusion", "noConfusionType", "injEq", "inj", "sizeOf_spec", "ctorIdx", "toCtorIdx",
    "eq_def", "induct", "mutual_induct", "elim"]
  let lastIsAux := match u with
    | .str _ s => s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
        suffixes.contains s
    | _ => true
  let rec taggedPrefix : Name → Bool
    | .anonymous => false
    | p@(.str q _) | p@(.num q _) => h.isTagged p || taggedPrefix q
  u.isInternal || lastIsAux || taggedPrefix u.getPrefix ||
    (h.nodes[u]?.any fun n => n.fields.kind == "rec" || n.fields.kind == "ctor")

/-- `status` warns when a tagged declaration of this library uses an untagged one of it.
`closures` holds `Walk.closureOf` of each tagged declaration. -/
def untaggedWarnings (h : Walk.Hashed) (closures : Std.HashMap Name (Array Name × Array Name))
    (boundary : BoundaryList) (modules : Array String) (owned : Std.HashSet String) :
    Array String := Id.run do
  let mut users : Std.HashMap Name (Array Name) := {}
  for (x, d) in h.boundary.zip boundary.declarations do
    unless modules.contains d.module do continue
    for u in (closures[x]?.map (·.2)).getD #[] do
      if owned.contains u.toString && !isGenerated h u then
        users := users.insert u ((users.getD u #[]).push x)
  let mut out := #[]
  for u in Walk.sortNames (users.fold (init := #[]) fun acc u _ => acc.push u) do
    let xs := Walk.sortNames (users.getD u #[])
    out := out.push s!"warning: untagged {u} of this library is used by tagged {", ".intercalate (xs.toList.map toString)}; tag it so it gets its own signer"
  return out

def compute (root : System.FilePath) (base? : Option String) : IO Result := do
  let cfg ← Config.load root
  let cur ← Store.readCurrent root
  let cache : Cache ← IO.mkRef {}
  let boundary ← loadBoundary root cur.boundary
  let new ← hashed root cache cur.exportHash cur.boundary
  let (all, bad) ← loadAllRecords root cfg
  let ledger := Ledger.build cfg all
  let base ← match base? with
    | some a =>
      let a := if isHash a then a else mkHash a
      let b ← boundaryForExport root ledger a
      some <$> hashed root cache a b
    | none => pure none
  let names := new.boundary
  -- Pass 1: state, flags, change, signers, history.
  let mut states : Std.HashMap Name String := {}
  let mut entries : Array (Name × BoundaryDecl × StatusDecl) := #[]
  -- (export, boundary list) pairs of records whose causes cannot be computed.
  let mut unknown : Std.HashSet (String × String) := {}
  -- Each tagged declaration's closure, walked once: (cut, untagged constants).
  let mut closures : Std.HashMap Name (Array Name × Array Name) := {}
  for (n, d) in names.zip boundary.declarations do
    let node := new.nodes[n]!
    let claim := node.claim
    let approvals := ledger.approvalsOf d.name
    let live := approvals.filter fun (r, a, _) => ledger.isLive r.hash a.signer d.name
    let matching := live.filter fun (_, _, c) => c == claim
    let signers := (matching.map fun (_, a, _) => a.signer).foldl
      (fun acc s => if acc.contains s then acc else acc.push s) #[] |>.qsort (· < ·)
    let state :=
      if signers.size ≥ cfg.requiredSigners then "valid"
      else if live.isEmpty then "unsigned" else "outdated"
    let flags := if (ledger.withdrawalsOf d.name).isEmpty then #[] else #["withdrawn"]
    -- Causes: against --base, or against the export of the last live approval.
    let mut change : Array Change := #[]
    match base with
    | some old =>
      if (old.nodes[n]?.map (·.claim)) != some claim then change := Walk.changes old new n
    | none =>
      if state != "valid" && !live.isEmpty then
        let (lastRec, last, lastClaim) := live.foldl (init := live[0]!) fun best x =>
          let (br, b, _) := best
          let (xr, xa, _) := x
          if b.date < xa.date || (b.date == xa.date && br.hash < xr.hash) then x else best
        let key := (last.exportHash, last.boundary)
        if lastClaim != claim && !unknown.contains key then
          -- A record from elsewhere may name objects this store lacks, or that do not hash.
          let old? ← try
              if (← Store.has root last.exportHash) && (← Store.has root last.boundary) then
                some <$> hashed root cache last.exportHash last.boundary
              else
                IO.eprintln s!"warning: export {last.exportHash} of record {lastRec.hash} is not in the store; causes unknown"
                pure none
            catch e =>
              IO.eprintln s!"warning: export {last.exportHash} of record {lastRec.hash}: {e}; causes unknown"
              pure none
          match old? with
          | some old => change := Walk.changes old new n
          | none => unknown := unknown.insert key
    let isThm := d.kind == "theorem"
    let (cut, untagged) := Walk.closureOf new n
    closures := closures.insert n (cut, untagged)
    states := states.insert n state
    entries := entries.push (n, d, {
      module := d.module, kind := d.kind, informal := d.informal, informalSource := d.informalSource
      claim, state, flags, change, signers, history := historyOf ledger d.name
      blockedBy := #[]
      proof := { status := if isThm then "unchecked" else "n/a" }
      evidence := none
      taggedDeps := cut.map (·.toString)
      -- Constants hashed into the claim, proofs excluded: X, its untagged closure, its cut.
      closureSize := 1 + cut.size + untagged.size })
  -- Pass 2: blocked_by, following tagged dependencies transitively.
  let cutOf (n : Name) : Array Name := (closures[n]?.map (·.1)).getD #[]
  let mut decls := #[]
  for (n, _, sd) in entries do
    let mut seen : Std.HashSet Name := {}
    let mut blocked : Array Name := #[]
    let mut stack := cutOf n
    while h : stack.size > 0 do
      let y := stack[stack.size - 1]
      stack := stack.pop
      if seen.contains y || y == n then continue
      seen := seen.insert y
      if states[y]?.getD "unsigned" != "valid" then blocked := blocked.push y
      stack := stack ++ cutOf y
    decls := decls.push (n.toString, { sd with blockedBy := (Walk.sortNames blocked).map (·.toString) })
  let report : StatusReport := {
    library := boundary.library, commit := boundary.commit, exportHash := cur.exportHash
    generated := ← UtcTime.now, declarations := decls }
  let owned : Std.HashSet String := (strLines (← Store.readString root cur.owned)).foldl (·.insert ·) {}
  let warnings := untaggedWarnings new closures boundary cur.modules owned
  return { report, badRecords := bad, warnings }

/-- One line per declaration: `NAME STATE [flags=..] [blocked-by=..] [change=cause:names;..]`. -/
def textLine (name : String) (d : StatusDecl) : String :=
  let parts := #[name, d.state] ++
    (if d.flags.isEmpty then #[] else #[s!"flags={",".intercalate d.flags.toList}"]) ++
    (if d.blockedBy.isEmpty then #[] else #[s!"blocked-by={",".intercalate d.blockedBy.toList}"]) ++
    (if d.change.isEmpty then #[] else
      #["change=" ++ ";".intercalate (d.change.toList.map fun c =>
        c.cause ++ ":" ++ ",".intercalate c.names.toList)])
  " ".intercalate parts.toList

def run (root : System.FilePath) (base? : Option String) (json : Bool) : IO UInt32 := do
  let r ← compute root base?
  for (p, _) in r.badRecords do
    IO.eprintln s!"warning: {p} is not a valid record and was ignored (see `leanblame validate`)"
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
    let count (s : String) := (decls.filter (·.2.state == s)).size
    let blocked := (decls.filter (!·.2.blockedBy.isEmpty)).size
    IO.println s!"{decls.size} tagged: {count "valid"} valid, {count "outdated"} outdated, {count "unsigned"} unsigned; {blocked} blocked"
  return 0

/-- `blame NAME`: who signed it, when, at which claim hash. -/
def blame (root : System.FilePath) (name : String) : IO UInt32 := do
  let cfg ← Config.load root
  let current? ← if (← (Store.currentPath root).pathExists) then
      some <$> compute root none
    else pure none
  let decl? := current?.bind fun r => (r.report.declarations.find? (·.1 == name)).map (·.2)
  let (all, _) ← loadAllRecords root cfg
  let ledger := Ledger.build cfg all
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
      | "approve" =>
        let withdrawn := ledger.withdrawn.contains (h.record, name)
        if withdrawn then " withdrawn" else if cfg.allows h.signer then " live" else " signer-not-allowed"
      | _ => ""
    IO.println s!"  {h.date}  {h.action}  {h.signer}  claim {h.claim.getD "-"}{current}  record {h.record}{live}"
    if let some note := h.note then IO.println s!"      note: {note}"
  return 0

end LeanBlame.Status
