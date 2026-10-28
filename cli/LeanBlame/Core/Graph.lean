/-
The graph (docs/design/04-architecture.md, "Beyond Lean"): what a frontend reports about one declaration
(`Decl`), what it serves to the core (`Source` for one export, `Backend` for the proof assistant),
and every declaration reached from a boundary list, hashed (`Node`, `Hashed`). Declarations are
keyed by their printed name; the core never sees a term.

`export` stores each graph in the object store, `.leanblame/store/graphs/<hex>-<hex>.json`, keyed by
the export and the boundary list, with what the commands need from the proof assistant
(`Backend.standard`, `incomplete`, `checker`); the other commands read it and never hash. A graph
file that does not read back, or that is not complete, is an error.
-/
import LeanBlame.Core.Schema
import LeanBlame.Core.Store

namespace LeanBlame

namespace Core

/-- The raw facts about one declaration, as a frontend reports them. -/
structure Decl where
  /-- The printed name; the key within one export. -/
  name : String
  /-- Where it is defined (Lean: its module); never hashed. -/
  module : String
  /-- The assistant's own label. Lean: `def`, `theorem`, `axiom`, `inductive`, `ctor`, `opaque`,
  `quot`, `rec`. Never interpreted by the core. -/
  kind : String
  role : Role
  /-- Universe (level) parameters; 0 for an assistant without them. -/
  uparams : Nat
  /-- Hex SHA-256 of the canonical statement, proofs erased. -/
  typeHash : String
  /-- Hex SHA-256 of the canonical body, proofs erased. `none` when the role is not `defined` or
  the body is not visible. -/
  bodyHash : Option String
  /-- The direct dependencies the hash follows: every constant of the statement and, when
  `bodyHash` is `some`, of the body; the frontend adds what the signer relies on through this
  declaration (Lean: the constructors of an inductive, the inductive of a constructor). Sorted by
  name, without the declaration itself, no repetitions. -/
  deps : Array String
  deriving Inhabited

/-- One export, as a frontend serves it to the core. -/
structure Source where
  /-- The facts about a constant. Throws when the export lacks it or it cannot be hashed (Lean:
  `unsafe`). Called once per constant the hash walk reaches. -/
  decl : String → IO Decl
  /-- Every constant the statement and the body of a constant rest on, proofs included; `#[]` for a
  constant the footprint ignores (unknown; Lean: `unsafe` or `partial`). The core walks this
  transitively for the assumption footprint. -/
  uses : String → Array String
  /-- Whether a constant is an assumption. `false` for unknown constants. -/
  isAssumed : String → Bool

/-- What a proof assistant contributes to the tool besides the `Source` of each export. -/
structure Backend where
  /-- Whether the assistant's own checker replays the export at a path. -/
  kernelAccepts : System.FilePath → IO Bool
  /-- The name of that checker, for the release manifest. Lean: `leanchecker`. -/
  checker : String
  /-- Assumptions that are part of the logic itself. Lean: `propext`, `Classical.choice`,
  `Quot.sound`. -/
  standard : Array String
  /-- Assumptions standing for a missing proof. Lean: `sorryAx`. -/
  incomplete : Array String

/-- One hashed declaration. -/
structure Node where
  decl : Decl
  /-- Tagged declarations only. -/
  informal : Option String
  own : String
  /-- Tagged declarations only. -/
  spec : Option String
  claim : String
  deriving Inhabited

/-- Every constant reached from the boundary list, hashed. -/
structure Hashed where
  nodes : Std.HashMap String Node
  /-- Per tagged declaration, the assumptions its statement and body rest on, proofs included,
  sorted. A function of the export alone. -/
  axioms : Std.HashMap String (Array String)
  /-- The boundary list it was hashed with. -/
  boundary : BoundaryList
  /-- The store hashes of the export and the boundary list: the graph's key. -/
  exportHash : String
  boundaryHash : String
  /-- `Backend.standard` of the proof assistant that hashed it. -/
  standard : Array String
  /-- `Backend.incomplete` of the proof assistant that hashed it. -/
  incomplete : Array String
  /-- `Backend.checker` of the proof assistant that hashed it. -/
  checker : String

/-- Tagged nodes are the ones with informal text. -/
def Hashed.isTagged (h : Hashed) (n : String) : Bool := (h.nodes[n]?.bind (·.informal)).isSome

/-- Names sorted as the hashes list them. -/
def sortNames (xs : Array String) : Array String := xs.qsort (· < ·)

end Core

namespace Graph

open Lean (Json ToJson toJson FromJson)

def dir (root : System.FilePath) : System.FilePath := Store.kindDir root .graphs

/-- Keyed by what the hashing reads: the export (first, so `sweep` can tell an export's graphs by
name) and the boundary list. -/
def path (root : System.FilePath) (exportHash boundaryHash : String) : System.FilePath :=
  dir root / s!"{hashHex exportHash}-{hashHex boundaryHash}.json"

/-- Delete the graphs of every export whose hex digest is not in `keep`. -/
def sweep (root : System.FilePath) (keep : Std.HashSet String) : IO Unit := do
  unless ← (dir root).isDir do return
  for e in ← (dir root).readDir do
    unless keep.contains (e.fileName.takeWhile (· != '-')).copy do IO.FS.removeFile e.path

def nodeToJson (n : Core.Node) : Json :=
  let d := n.decl
  Json.mkObj [("name", d.name), ("module", d.module), ("kind", d.kind), ("role", toJson d.role),
    ("uparams", d.uparams), ("type", d.typeHash), ("body", toJson d.bodyHash),
    ("informal", toJson n.informal), ("deps", toJson d.deps), ("own", n.own), ("spec", toJson n.spec),
    ("claim", n.claim)]

def nodeFromJson? (j : Json) : Except String Core.Node := do
  let o ← JsonObj.read j "graph node" ["name", "module", "kind", "role", "uparams", "type", "body",
    "informal", "deps", "own", "spec", "claim"]
  let name ← o.get String "name"
  let o := { o with what := s!"graph node {name}" }
  return {
    decl := {
      name, module := ← o.get String "module", kind := ← o.get String "kind", role := ← o.get Role "role"
      uparams := ← o.get Nat "uparams", typeHash := ← o.get String "type"
      bodyHash := ← o.get (Option String) "body", deps := ← o.get (Array String) "deps" }
    informal := ← o.get (Option String) "informal"
    own := ← o.get String "own", spec := ← o.get (Option String) "spec", claim := ← o.get String "claim" }

/-- Store graph `h`. -/
def save (root : System.FilePath) (h : Core.Hashed) : IO Unit :=
  writeFileMkdirs (path root h.exportHash h.boundaryHash) <| Json.compress <| Json.mkObj [
    ("export", h.exportHash), ("boundary", h.boundaryHash),
    ("nodes", .arr (h.nodes.fold (init := #[]) fun acc _ n => acc.push (nodeToJson n))),
    ("axioms", Json.mkObj (h.axioms.toList.map fun (n, axs) => (n, toJson axs))),
    ("standard", toJson h.standard), ("incomplete", toJson h.incomplete), ("checker", h.checker)]

/-- A graph is complete: its tagged nodes are exactly the declarations of its boundary list, with
their informal text and their axioms, and every dependency of a node is a node. -/
def check (h : Core.Hashed) : Except String Unit := do
  for d in h.boundary.declarations do
    let some n := h.nodes[d.name]? | throw s!"no node for {d.name}"
    unless n.informal == some d.informal do throw s!"the node of {d.name} lacks its informal text"
    unless h.axioms.contains d.name do throw s!"no axioms for {d.name}"
  let tagged := h.nodes.fold (init := 0) fun k _ n => if n.informal.isSome then k + 1 else k
  unless tagged == h.boundary.declarations.size do throw "a node with informal text is not on the boundary list"
  unless h.axioms.size == h.boundary.declarations.size do throw "axioms of a declaration not on the boundary list"
  for (_, n) in h.nodes do
    for d in n.decl.deps do
      unless h.nodes.contains d do throw s!"{n.decl.name} depends on {d}, which has no node"

/-- The graph of export `exportHash` against boundary list `b`, stored as `boundaryHash`: `none` when
the store has no file for them, an error when the file does not read as their complete graph. -/
def load? (root : System.FilePath) (exportHash boundaryHash : String) (b : BoundaryList) :
    IO (Option Core.Hashed) := do
  let p := path root exportHash boundaryHash
  let some text ← readFileIfExists p | return none
  let parsed : Except String Core.Hashed := do
    let o ← JsonObj.read (← Json.parse text) "graph"
      ["export", "boundary", "nodes", "axioms", "standard", "incomplete", "checker"]
    unless (← o.get String "export") == exportHash && (← o.get String "boundary") == boundaryHash do
      throw "the graph of another export or boundary list"
    let mut nodes : Std.HashMap String Core.Node := {}
    for j in ← o.get (Array Json) "nodes" do
      let n ← nodeFromJson? j
      if nodes.contains n.decl.name then throw s!"two nodes for {n.decl.name}"
      nodes := nodes.insert n.decl.name n
    let mut axioms : Std.HashMap String (Array String) := {}
    for (n, axs) in ← (← o.get Json "axioms").getObj? do
      axioms := axioms.insert n (← (Lean.fromJson? axs : Except String (Array String)))
    let h : Core.Hashed := {
      nodes, axioms, boundary := b, exportHash, boundaryHash
      standard := ← o.get (Array String) "standard", incomplete := ← o.get (Array String) "incomplete"
      checker := ← o.get String "checker" }
    check h
    return h
  match parsed with
  | .ok h => return some h
  | .error e => fail s!"{p}: not the graph of export {exportHash} and boundary list {boundaryHash}: {e}"

end Graph

end LeanBlame
