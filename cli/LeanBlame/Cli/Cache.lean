/-
The local cache of hashed exports: `.leanblame/cache/<hex>.json`, `<hex>` the SHA-256 of
`<export> <boundary list>`, holds what `Walk.hashExport` computed for that pair, so that `status`
does not hash an export again. `export` writes it; a file that does not read back is a miss.
-/
import LeanBlame.Cli.Store
import LeanBlame.Cli.Walk

namespace LeanBlame.Cache

open Lean

def schema : String := "leanblame.cache.2"

def path (root : System.FilePath) (exportHash boundary : String) : System.FilePath :=
  Store.dir root / "cache" / (Sha256.hexOfString s!"{exportHash} {boundary}" ++ ".json")

/-- A name as its array of components: printed names do not always read back. -/
def nameToJson (n : Name) : Json :=
  .arr <| n.components.toArray.map fun
    | .str _ s => .str s
    | .num _ k => toJson k
    | .anonymous => .null

def nameFromJson? (j : Json) : Except String Name := do
  (← j.getArr?).foldlM (init := .anonymous) fun n c => match c with
    | .str s => pure (n.str s)
    | c => n.num <$> c.getNat?

def nodeToJson (n : Walk.Node) : Json :=
  let f := n.fields
  Json.mkObj [("name", nameToJson f.name), ("kind", f.kind), ("uparams", f.uparams),
    ("type", f.typeHash), ("body", toJson f.bodyHash), ("safety", f.safety),
    ("informal", toJson n.informal), ("deps", .arr (n.deps.map nameToJson)), ("own", n.own),
    ("spec", toJson n.spec), ("claim", n.claim)]

def nodeFromJson? (j : Json) : Except String Walk.Node := do
  let get (α) [FromJson α] (k : String) := j.getObjValAs? α k
  return {
    fields := {
      kind := ← get String "kind", name := ← nameFromJson? (← j.getObjVal? "name")
      uparams := ← get Nat "uparams", typeHash := ← get String "type"
      bodyHash := ← get (Option String) "body", safety := ← get String "safety" }
    informal := ← get (Option String) "informal"
    deps := ← (← get (Array Json) "deps").mapM nameFromJson?
    own := ← get String "own", spec := ← get (Option String) "spec", claim := ← get String "claim" }

/-- Cache `h`, the hashing of export `exportHash` against boundary list `boundary`. -/
def save (root : System.FilePath) (exportHash boundary : String) (h : Walk.Hashed) : IO Unit :=
  writeFileMkdirs (path root exportHash boundary) <| Json.compress <| Json.mkObj [
    ("schema", schema),
    ("declarations", .arr (h.declarations.map (nameToJson ·.1))),
    ("nodes", .arr (h.nodes.fold (init := #[]) fun acc _ n => acc.push (nodeToJson n))),
    ("axioms", .arr (h.axioms.fold (init := #[]) fun acc n axs =>
      acc.push (.arr #[nameToJson n, .arr (axs.map nameToJson)])))]

/-- The cached hashing of export `exportHash` against boundary list `b`, whose hash is
`boundary`. -/
def load? (root : System.FilePath) (exportHash boundary : String) (b : BoundaryList) :
    IO (Option Walk.Hashed) := do
  let some text ← readFileIfExists (path root exportHash boundary) | return none
  return Except.toOption do
    let j ← Json.parse text
    unless (← j.getObjValAs? String "schema") == schema do throw "another schema"
    let names ← (← j.getObjValAs? (Array Json) "declarations").mapM nameFromJson?
    unless names.size == b.declarations.size do throw "another boundary list"
    let nodes ← (← j.getObjValAs? (Array Json) "nodes").foldlM (init := {}) fun m j => do
      let n ← nodeFromJson? j
      return m.insert n.fields.name n
    let axioms ← (← j.getObjValAs? (Array Json) "axioms").foldlM (init := {}) fun m j => do
      let #[n, axs] ← j.getArr? | throw "malformed axioms"
      return m.insert (← nameFromJson? n) (← (← axs.getArr?).mapM nameFromJson?)
    return { nodes, tagged := names.foldl (·.insert ·) {}, axioms, boundary := b
             declarations := names.zip b.declarations }

end LeanBlame.Cache
