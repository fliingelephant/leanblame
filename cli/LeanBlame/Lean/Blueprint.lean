/-
The blueprint reader of `export --boundary FILE` (docs/design/04-architecture.md, "Blueprints"):
verso-blueprint's `blueprint-manifest.json`. Each statement entry of a blueprint node names its Lean
declarations in `codeData` (the `canonical` of `externalDecls`, the `name` of
`literateDeclarations.definedDefs` and `definedTheorems`); its text is the `raw` of the
`externalMarkup` in slot `statement`, or else the entry's fragment in the `blueprint-html-cache.json`
next to the manifest. Other fields are not read.
-/
import LeanBlame.Core.Schema

namespace LeanBlame.Blueprint

open Lean

/-- A constant name as boundary lists write it (`Lean.Name.toString`), read back. -/
def constName? (s : String) : Option Name := Syntax.decodeNameLit ("`" ++ s)

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

/-- The nodes of the verso-blueprint manifest `j`, read from `path`, and the problems. Entries are
statements of blueprint nodes (`facet` statement, `targetKind` block or externalMarkup, as in
verso-blueprint's `isQueryableStatement`). A node without Lean names is not formalized yet and is
left out. A statement entry without a label or without text, an HTML cache that does not parse, and
a Lean name claimed by two labels are errors. -/
def nodes (path : System.FilePath) (j : Json) : IO (Array Node × Array String) := do
  let arr (j : Json) (k : String) : Array Json := (j.getObjValAs? (Array Json) k).toOption.getD #[]
  let str? (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption
  let nonEmpty? (s : String) : Option String := if strTrim s == "" then none else some s
  let cache := path.parent.getD "." / "blueprint-html-cache.json"
  let mut fragments? : Option (Std.HashMap String String) := none
  let mut owner : Std.HashMap Name String := {}
  let mut out : Array Node := #[]
  let mut index : Std.HashMap String Nat := {}
  let mut errors := #[]
  for e in arr j "previews" do
    unless str? e "facet" == some "statement" &&
        (str? e "targetKind").all (· ∈ ["block", "externalMarkup"]) do continue
    let code := e.getObjValD "codeData"
    let lit := code.getObjValD "literateDeclarations"
    let written := (arr code "externalDecls").filterMap (str? · "canonical") ++
      (arr lit "definedDefs" ++ arr lit "definedTheorems").filterMap (str? · "name")
    if written.isEmpty then continue
    let some label := (str? e "label").map labelString
      | errors := errors.push s!"a statement entry for {written.toList} has no label"; continue
    let markup := (arr e "externalMarkup").find? (str? · "slot" == some "statement")
    let mut text? := (markup.bind (str? · "raw")).bind nonEmpty?
    if text?.isNone then
      if fragments?.isNone then
        let entries ← match ← readFileIfExists cache with
          | none => pure #[]
          | some s => match Json.parse s with
            | .ok c => pure (arr c "entries")
            | .error err => fail s!"{cache}: {err}"
        fragments? := some <| entries.foldl (init := {}) fun m f =>
          match str? f "key", str? f "html" with
          | some k, some h => m.insert k h
          | _, _ => m
      text? := ((str? e "key").bind fun k => fragments?.bind (·[k]?)).bind nonEmpty?
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
