/-
The graph of docs/design/15-generic-core.md: what a frontend reports about one declaration
(`Decl`), what it serves to the core (`Source` for one export, `Backend` for the proof assistant),
and every declaration reached from a boundary list, hashed (`Node`, `Hashed`). Declarations are
keyed by their printed name; the core never sees a term.

`export` stores each graph in the object store, `.leanblame/store/graphs/<hex>-<hex>.json`, keyed by
the export and the boundary list's declarations, with what the commands need from the proof
assistant (`Backend.standard`, `incomplete`, `checker`); the other commands read it and never hash.
A file that does not read back counts as missing.
-/
import LeanBlame.Core.Schema
import LeanBlame.Core.Store

namespace LeanBlame

namespace Core

/-- The raw facts about one declaration, as a frontend reports them. -/
structure Decl where
  /-- The printed name; the key everywhere. -/
  name : String
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

/-- What a proof assistant contributes to the tool. -/
structure Backend where
  /-- The source of the export object stored at a path. -/
  source : System.FilePath → IO Source
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

def schema : String := "leanblame.graph.1"

def dir (root : System.FilePath) : System.FilePath := Store.kindDir root .graphs

/-- Keyed by what the hashing reads: the export (first, so `sweep` can tell an export's graphs by
name) and the boundary list's declarations (not its `commit`, `toolchain` or `deps`). -/
def path (root : System.FilePath) (exportHash : String) (b : BoundaryList) : System.FilePath :=
  dir root / s!"{hashHex exportHash}-{Sha256.hexOfString (toJson b.declarations).compress}.json"

/-- Delete the graphs of every export whose hex digest is not in `keep`. -/
def sweep (root : System.FilePath) (keep : Std.HashSet String) : IO Unit := do
  unless ← (dir root).isDir do return
  for e in ← (dir root).readDir do
    unless keep.contains (e.fileName.takeWhile (· != '-')).copy do IO.FS.removeFile e.path

def nodeToJson (n : Core.Node) : Json :=
  let d := n.decl
  Json.mkObj [("name", d.name), ("kind", d.kind), ("role", toJson d.role), ("uparams", d.uparams),
    ("type", d.typeHash), ("body", toJson d.bodyHash), ("informal", toJson n.informal),
    ("deps", toJson d.deps), ("own", n.own), ("spec", toJson n.spec), ("claim", n.claim)]

def nodeFromJson? (j : Json) : Except String Core.Node := do
  let get (α) [FromJson α] (k : String) := j.getObjValAs? α k
  let some role := ofString? Role.all (← get String "role") | throw "unknown role"
  return {
    decl := {
      name := ← get String "name", kind := ← get String "kind", role
      uparams := ← get Nat "uparams", typeHash := ← get String "type"
      bodyHash := ← get (Option String) "body", deps := ← get (Array String) "deps" }
    informal := ← get (Option String) "informal"
    own := ← get String "own", spec := ← get (Option String) "spec", claim := ← get String "claim" }

/-- Store `h`, the graph of export `exportHash` against its boundary list. -/
def save (root : System.FilePath) (exportHash : String) (h : Core.Hashed) : IO Unit :=
  writeFileMkdirs (path root exportHash h.boundary) <| Json.compress <| Json.mkObj [
    ("schema", schema),
    ("declarations", toJson (h.boundary.declarations.map (·.name))),
    ("nodes", .arr (h.nodes.fold (init := #[]) fun acc _ n => acc.push (nodeToJson n))),
    ("axioms", .arr (h.axioms.fold (init := #[]) fun acc n axs => acc.push (.arr #[toJson n, toJson axs]))),
    ("standard", toJson h.standard), ("incomplete", toJson h.incomplete), ("checker", h.checker)]

/-- The graph of export `exportHash` against boundary list `b`: `none` when the store has no file for
them, an error when the file does not read as their graph. -/
def load? (root : System.FilePath) (exportHash : String) (b : BoundaryList) :
    IO (Option Core.Hashed) := do
  let p := path root exportHash b
  let some text ← readFileIfExists p | return none
  let parsed : Except String Core.Hashed := do
    let j ← Json.parse text
    unless (← j.getObjValAs? String "schema") == schema do throw "another schema"
    unless (← j.getObjValAs? (Array String) "declarations") == b.declarations.map (·.name) do
      throw "another boundary list"
    let nodes ← (← j.getObjValAs? (Array Json) "nodes").foldlM (init := {}) fun m j => do
      let n ← nodeFromJson? j
      return m.insert n.decl.name n
    let axioms ← (← j.getObjValAs? (Array Json) "axioms").foldlM (init := {}) fun m j => do
      let #[n, axs] ← j.getArr? | throw "malformed axioms"
      return m.insert (← n.getStr?) (← (← axs.getArr?).mapM (·.getStr?))
    return {
      nodes, axioms, boundary := b, standard := ← j.getObjValAs? (Array String) "standard"
      incomplete := ← j.getObjValAs? (Array String) "incomplete"
      checker := ← j.getObjValAs? String "checker" }
  match parsed with
  | .ok h => return some h
  | .error e => fail s!"{p}: not the graph of export {exportHash} and its boundary list: {e}"

end Graph

end LeanBlame
