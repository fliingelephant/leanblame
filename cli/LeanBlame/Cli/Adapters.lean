/-
Input adapters (docs/design/04-architecture.md, "Adapters"): the declarations a boundary-list file puts on
the boundary, with their informal text. `export --boundary FILE` checks them against the library
and expands them like `@[trusted]` tags. Two formats:

* a hand-written TOML list, `schema = "leanblame.manual.1"`, whose `[declarations]` table maps
  constant names to their text (`informal_source = "manual"`);
* verso-blueprint's `blueprint-manifest.json`: each statement entry of a blueprint node names its
  Lean declarations in `codeData` (the `canonical` of `externalDecls`, the `name` of
  `literateDeclarations.definedDefs` and `definedTheorems`); its text is the `raw` of the
  `externalMarkup` in slot `statement`, or else the entry's fragment in the
  `blueprint-html-cache.json` next to the manifest (`informal_source = "blueprint:<label>"`).
  Other fields are not read.
-/
import Lake.Toml
import LeanBlame.Cli.Schema

namespace LeanBlame.Export

open Lean

/-- A declaration put on the boundary, by `@[trusted]` or by a boundary-list file. -/
structure Tag where
  name : Name
  informal : String
  informalSource : String

/-- The informal text of a docstring or list entry, as docs/design/03 hashes it: ASCII whitespace trimmed,
line endings normalized, no Unicode normalization (Lean core has none). -/
def normalizeInformal (s : String) : String := strTrim s.crlfToLf

/-- A constant name as boundary lists write it. -/
def constName? (s : String) : Option Name := Syntax.decodeNameLit ("`" ++ s)

def manualSchemaId : String := "leanblame.manual.1"

open Lake.Toml (DecodeM Table logDecodeErrorAt) in
/-- Decode a `leanblame.manual.1` list, logging every problem: unknown keys, a name that is not a
constant name, empty text. -/
def decodeManual (t : Table) : DecodeM (Array Tag) := do
  checkKeys t #["schema", "declarations"] "a manual list"
  discard <| decodeStr t `schema (· == manualSchemaId) (s!"is `{·}`, expected `{manualSchemaId}`")
  let ds ← decodeTable t `declarations
  if ds.items.isEmpty then logDecodeErrorAt (refOf t `declarations) "`declarations` lists nothing"
  ds.items.filterMapM fun (k, v) => do
    let text := normalizeInformal (← decodeStr ds k)
    let some name := constName? (keyString k)
      | logDecodeErrorAt v.ref s!"`{keyString k}` is not a constant name"; return none
    if text.isEmpty then
      logDecodeErrorAt v.ref s!"`{keyString k}`: the informal text is empty"; return none
    return some { name, informal := text, informalSource := "manual" }

/-- A blueprint label as its authors write it: a label of one component without the quotes Lean
puts around it (verso-blueprint's `labelString`). -/
def labelString (label : String) : String :=
  match constName? label with
  | some (.str .anonymous s) => s
  | _ => label

/-- The tags of verso-blueprint manifest `j`, read from `path`, and the problems. Entries are
statements of blueprint nodes (`facet` statement, `targetKind` block or externalMarkup, as in
verso-blueprint's `isQueryableStatement`); one without Lean names is skipped; a Lean name claimed by
two labels is an error. -/
def blueprintTags (path : System.FilePath) (j : Json) : IO (Array Tag × Array String) := do
  let arr (j : Json) (k : String) : Array Json := (j.getObjValAs? (Array Json) k).toOption.getD #[]
  let str? (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption
  let nonEmpty? (s : String) : Option String := if strTrim s == "" then none else some s
  let mut fragments? : Option (Std.HashMap String String) := none
  let mut owner : Std.HashMap Name String := {}
  let mut tags := #[]
  let mut errors := #[]
  for e in arr j "previews" do
    unless str? e "facet" == some "statement" &&
        (str? e "targetKind").all (· ∈ ["block", "externalMarkup"]) do continue
    let label := labelString ((str? e "label").getD "")
    let code := e.getObjValD "codeData"
    let lit := code.getObjValD "literateDeclarations"
    let written := (arr code "externalDecls").filterMap (str? · "canonical") ++
      (arr lit "definedDefs" ++ arr lit "definedTheorems").filterMap (str? · "name")
    if written.isEmpty then continue
    let markup := (arr e "externalMarkup").find? (str? · "slot" == some "statement")
    let mut text? := (markup.bind (str? · "raw")).bind nonEmpty?
    if text?.isNone then
      if fragments?.isNone then
        let cache := path.parent.getD "." / "blueprint-html-cache.json"
        let entries := match (← readFileIfExists cache).map Json.parse with
          | some (.ok c) => arr c "entries"
          | _ => #[]
        fragments? := some <| entries.foldl (init := {}) fun m f =>
          match str? f "key", str? f "html" with
          | some k, some h => m.insert k h
          | _, _ => m
      text? := ((str? e "key").bind fun k => fragments?.bind (·[k]?)).bind nonEmpty?
    let some text := text? | errors := errors.push s!"no statement text for label {label}"; continue
    for s in dedup written do
      let some name := constName? s | errors := errors.push s!"label {label}: `{s}` is not a constant name"; continue
      match owner[name]? with
      | some other =>
        if other != label then errors := errors.push s!"{name} is claimed by labels {other} and {label}"
      | none =>
        owner := owner.insert name label
        tags := tags.push { name, informal := normalizeInformal text, informalSource := s!"blueprint:{label}" }
  return (tags, errors)

end LeanBlame.Export
