/-
The blueprint parser of `export --boundary FILE` (docs/decisions.md, "Blueprints"):
verso-blueprint's `blueprint-manifest.json`. Each statement entry of a blueprint node names its Lean
declarations in `codeData` (the `canonical` of `externalDecls`, the `name` of
`literateDeclarations.definedDefs` and `definedTheorems`); its text is the `raw` of the
`externalMarkup` in slot `statement`, or else the entry's fragment in the `blueprint-html-cache.json`
next to the manifest. Other fields are not read.
-/
import LeanBlame.Core.Schema
import LeanBlame.Lean.Names

namespace LeanBlame.Blueprint

open Lean

/-- A blueprint label as its authors write it: a label of one component without the quotes Lean
puts around it (verso-blueprint's `labelString`). -/
def labelString (label : String) : String :=
  match constName? label with
  | some (.str .anonymous s) => s
  | _ => label

/-- A blueprint node with Lean declarations: its label, their names in the order the blueprint
gives them, and its statement text. -/
structure Node where
  label : String
  names : Array Name
  text : String

/-- Field `k` of object `j`. verso-blueprint writes `null` for an absent value, or leaves the key
out; both read as absent. -/
def field? (j : Json) (k : String) : Option Json := match j.getObjVal? k with
  | .ok .null | .error _ => none
  | .ok v => some v

/-- Array field `k` of `j`, empty when absent. -/
def arr (j : Json) (k : String) : Except String (Array Json) := match field? j k with
  | none => pure #[]
  | some (.arr xs) => pure xs
  | some _ => throw s!"`{k}` is not an array"

/-- String field `k` of `j`, if present. -/
def str? (j : Json) (k : String) : Except String (Option String) := match field? j k with
  | none => pure none
  | some (.str s) => pure (some s)
  | some _ => throw s!"`{k}` is not a string"

/-- Object field `k` of `j`, empty when absent. -/
def obj (j : Json) (k : String) : Except String Json := match field? j k with
  | none => pure (Json.mkObj [])
  | some v@(.obj _) => pure v
  | some _ => throw s!"`{k}` is not an object"

/-- The statement texts of the `blueprint-html-cache.json` at `cache`, by key; none when there is
no such file. -/
def fragments (cache : System.FilePath) : IO (Std.HashMap String String) := do
  unless ← cache.pathExists do return {}
  readJson cache fun j => do
    let mut m : Std.HashMap String String := {}
    for f in ← arr j "entries" do
      let (some k, some h) := (← str? f "key", ← str? f "html") | throw "an entry without `key` or `html`"
      m := m.insert k h
    return m

/-- The nodes of the verso-blueprint manifest `j`, read from `path`, and the problems. Entries are
statements of blueprint nodes (`facet` statement, `targetKind` block or externalMarkup, as in
verso-blueprint's `isQueryableStatement`). A node without Lean names is not formalized yet and is
left out. A statement entry without a label or without text and a Lean name claimed by two labels
are problems; a value of an unexpected type, and an HTML cache that does not parse, are errors.
-/
def nodes (path : System.FilePath) (j : Json) : IO (Array Node × Array String) := do
  -- The fields of the manifest: an error names it.
  let inManifest {α : Type} (x : Except String α) : IO α := IO.ofExcept (x.mapError (s!"{path}: {·}"))
  let arr (j : Json) (k : String) := inManifest (Blueprint.arr j k)
  let str? (j : Json) (k : String) := inManifest (Blueprint.str? j k)
  let obj (j : Json) (k : String) := inManifest (Blueprint.obj j k)
  let nonEmpty? (s : String) : Option String := if strTrim s == "" then none else some s
  let cache := path.parent.getD "." / "blueprint-html-cache.json"
  let mut fragments? : Option (Std.HashMap String String) := none
  let mut owner : Std.HashMap Name String := {}
  let mut out : Array Node := #[]
  let mut index : Std.HashMap String Nat := {}
  let mut errors := #[]
  for e in ← arr j "previews" do
    unless e matches .obj _ do fail s!"{path}: an entry of `previews` is not an object"
    unless (← str? e "facet") == some "statement" &&
        (← str? e "targetKind").all (· ∈ ["block", "externalMarkup"]) do continue
    let code ← obj e "codeData"
    let lit ← obj code "literateDeclarations"
    let mut written := #[]
    for d in ← arr code "externalDecls" do
      if let some n ← str? d "canonical" then written := written.push n
    for d in (← arr lit "definedDefs") ++ (← arr lit "definedTheorems") do
      if let some n ← str? d "name" then written := written.push n
    if written.isEmpty then continue
    let some label := (← str? e "label").map labelString
      | errors := errors.push s!"a statement entry for {written.toList} has no label"; continue
    let mut text? := none
    for m in ← arr e "externalMarkup" do
      if (← str? m "slot") == some "statement" && text?.isNone then
        text? := (← str? m "raw").bind nonEmpty?
    if text?.isNone then
      if fragments?.isNone then fragments? := some (← fragments cache)
      text? := ((← str? e "key").bind fun k => fragments?.bind (·[k]?)).bind nonEmpty?
    let some text := text? | errors := errors.push s!"no statement text for label {label}"; continue
    let mut names := #[]
    for s in dedup written do
      let some name := constName? s | errors := errors.push s!"label {label}: `{s}` is not a constant name"; continue
      match owner[name]? with
      | some other =>
        if other != label then errors := errors.push s!"{name} is claimed by labels {other} and {label}"
      | none =>
        owner := owner.insert name label
        names := names.push name
    match index[label]? with
    | some i => out := out.modify i fun n => { n with names := n.names ++ names }
    | none =>
      index := index.insert label out.size
      out := out.push { label, names, text }
  return (out.filter (!·.names.isEmpty), errors)

end LeanBlame.Blueprint
