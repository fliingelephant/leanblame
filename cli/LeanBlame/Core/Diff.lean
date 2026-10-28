/-
`leanblame diff --from RECORD [--to RECORD] [--json] [NAME|ID...]` (docs/design/14-schemas.md §5):
what changed between the export an approve record names and another approve record's, or the last
`export`. `status` compares each declaration with its last live approval; `diff` compares two points
the caller picks, with the same comparison (`Walk.compare`), and gives both readable versions. It
reads graphs from the object store and never hashes. Declarations are matched by id, so a renamed
declaration is one declaration. A declaration with the same claim at both points has nothing to show:
its claim covers every part `Walk.compare` looks at, so it is not walked.
-/
import LeanBlame.Core.Status

namespace LeanBlame.Diff

open Lean (Json toJson)

/-- One end of a diff: the graph of the export an approve record names, or of the last `export`. -/
structure Point where
  /-- `none`: the last `export`. -/
  record : Option String
  /-- `none` when that export has uncommitted changes. -/
  commit : Option String
  graph : Core.Hashed

/-- The point of approve record `ref`: its id, hex digest or file. -/
def recordPoint (root : System.FilePath) (ledger : Ledger) (ref : String) : IO Point := do
  let id ← recordId ref
  let some r := ledger.byId[id]? | fail s!"{ref}: no record of this library has id {id}"
  match r.record with
  | .withdraw w =>
    fail s!"{r.path} is a withdraw; compare with the approve record it withdraws, {w.refersTo}"
  | .approve a =>
    let some graph ← Status.recordGraph? root r a
      | fail s!"{r.path} names export {a.exportHash} and boundary list {a.boundary}, which this store lacks; run `leanblame export` at commit {a.commit}"
    return { record := some r.hash, commit := some a.commit, graph }

/-- The point of the last `export`. -/
def currentPoint (root : System.FilePath) : IO Point := do
  let cur ← Store.readCurrent root
  return { record := none, commit := cur.commit, graph := ← Status.currentGraph root cur }

/-- A declaration at one point, with its claim there. -/
structure Side where
  decl : BoundaryDecl
  claim : String

/-- One declaration of a diff, by id. -/
structure Entry where
  id : String
  /-- `none`: added. -/
  old : Option Side
  /-- `none`: removed. -/
  new : Option Side
  /-- `none` when one side lacks the declaration. -/
  comparison : Option Walk.Comparison

def Entry.name (e : Entry) : String :=
  match e.new, e.old with
  | some s, _ | none, some s => s.decl.name
  | none, none => e.id

/-- The declarations `keys` name (a name or an id, looked up at `new`, then at `old`); without keys,
every declaration of either point whose claim differs. Sorted by name. -/
def compute (old new : Point) (keys : Array String) : IO (Array Entry) := do
  let index (p : Point) : Std.HashMap String BoundaryDecl :=
    p.graph.boundary.declarations.foldl (init := {}) fun m d => m.insert d.id d
  let (olds, news) := (index old, index new)
  let find (p : Point) (k : String) : IO (Option BoundaryDecl) :=
    match p.graph.boundary.find? k with
    | .ok d => pure d
    | .error e => fail e
  let ids ← if keys.isEmpty then pure (olds.keys ++ news.keys).toArray else
    keys.mapM fun k => do
      if let some d ← find new k then return d.id
      if let some d ← find old k then return d.id
      fail s!"{k} is on neither boundary list"
  let ids := (ids.qsort (· < ·)).eraseReps
  let side (p : Point) (d : BoundaryDecl) : IO Side := do
    let some n := p.graph.nodes[d.name]?
      | fail s!"the graph of export {p.graph.exportHash} has no node for {d.name}"
    return { decl := d, claim := n.claim }
  let mut entries : Array Entry := #[]
  for id in ids do
    match olds[id]?, news[id]? with
    | some o, some n =>
      let (os, ns) := (← side old o, ← side new n)
      if os.claim == ns.claim then
        unless keys.isEmpty do entries := entries.push { id, old := os, new := ns, comparison := some {} }
      else
        match Walk.compare old.graph new.graph o.name n.name with
        | .ok c => entries := entries.push { id, old := os, new := ns, comparison := some c }
        | .error e => fail e
    | some o, none => entries := entries.push { id, old := ← side old o, new := none, comparison := none }
    | none, some n => entries := entries.push { id, old := none, new := ← side new n, comparison := none }
    | none, none => fail s!"no declaration has id {id}"
  return entries.qsort (·.name < ·.name)

def sideJson : Option Side → Json
  | none => .null
  | some s => Json.mkObj [("name", s.decl.name), ("module", s.decl.module), ("kind", s.decl.kind),
      ("claim", s.claim), ("informal", s.decl.informal), ("statement", toJson s.decl.statement)]

def comparisonJson (c : Walk.Comparison) : Json :=
  Json.mkObj [("informal", toJson c.informal), ("statement", toJson c.statement),
    ("body", toJson c.body),
    ("relies_on", Json.mkObj [("added", toJson c.added), ("removed", toJson c.removed),
      ("changed", toJson c.depSpec)]),
    ("cut_moved", toJson c.cutMoved), ("untagged", toJson c.untagged)]

def pointJson (p : Point) : Json :=
  Json.mkObj [("record", toJson p.record), ("commit", toJson p.commit),
    ("export", p.graph.exportHash), ("boundary", p.graph.boundaryHash)]

def report (old new : Point) (entries : Array Entry) : Json :=
  Json.mkObj [("library", new.graph.boundary.library),
    ("from", pointJson old), ("to", pointJson new),
    ("declarations", Json.arr (entries.map fun e => Json.mkObj [("id", e.id),
      ("from", sideJson e.old), ("to", sideJson e.new),
      ("changes", (e.comparison.map comparisonJson).getD .null)]))]

/-- The old and the new text, one indented line each, under `what`. -/
def textDiff (what old new : String) : Array String :=
  #[s!"  {what}:"] ++ ((old.splitOn "\n").map (s!"  - {·}")).toArray ++
    ((new.splitOn "\n").map (s!"  + {·}")).toArray

def statementText (segments : Array Segment) : String :=
  String.join (segments.toList.map (·.text))

/-- `NAME added`, `NAME removed`, `NAME unchanged`, or
`NAME [renamed-from=OLD] change=cause:names;.. [relies-on=+ADDED,-REMOVED]`, then the old and new
informal text and statement where they differ. -/
def textLines (e : Entry) : Array String :=
  match e.old, e.new, e.comparison with
  | some o, some n, some c =>
    let causes := c.changes n.decl.name
    if causes.isEmpty then #[s!"{n.decl.name} unchanged"] else
    let deps := c.added.map ("+" ++ ·) ++ c.removed.map ("-" ++ ·)
    let head := #[n.decl.name] ++ (if c.renamed then #[s!"renamed-from={o.decl.name}"] else #[]) ++
      #[Status.changeText causes] ++ (if deps.isEmpty then #[] else #[s!"relies-on={",".intercalate deps.toList}"])
    #[" ".intercalate head.toList] ++
      (if c.informal then textDiff "informal" o.decl.informal n.decl.informal else #[]) ++
      (if c.statement || c.renamed then
        textDiff "statement" (statementText o.decl.statement) (statementText n.decl.statement)
       else #[])
  | none, some n, _ => #[s!"{n.decl.name} added"]
  | some o, none, _ => #[s!"{o.decl.name} removed"]
  | _, _, _ => #[]

def run (root : System.FilePath) (fromRef : String) (toRef : Option String) (keys : Array String)
    (json : Bool) : IO UInt32 := do
  let ledger ← Ledger.load root
  let old ← recordPoint root ledger fromRef
  let new ← match toRef with
    | some r => recordPoint root ledger r
    | none => currentPoint root
  let entries ← compute old new keys
  if json then
    IO.print ((report old new entries).pretty ++ "\n")
  else
    for e in entries do
      for l in textLines e do IO.println l
    let count (p : Entry → Bool) := (entries.filter p).size
    let changed (e : Entry) := e.comparison.any fun c => !(c.changes e.name).isEmpty
    let unchanged := count fun e => e.comparison.isSome && !changed e
    IO.println <| s!"{count changed} changed, {count (·.old.isNone)} added, {count (·.new.isNone)} removed" ++
      (if unchanged == 0 then "" else s!", {unchanged} unchanged")
  return 0

end LeanBlame.Diff
