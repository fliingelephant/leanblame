/-
The `@[trusted]` attribute: `@[trusted]` or `@[trusted "id"]` on a declaration, or written after the
fact, `attribute [trusted "id"] Name`, in any module, also for a declaration of another library.
-/
module

public import Lean.Attributes
public import Lean.Linter.Deprecated

public section

open Lean

namespace LeanBlame

/--
`@[trusted]` puts a declaration on the trusted boundary: a human must read it,
with its docstring, for results that use it to mean anything. Tagging a
`structure` or `inductive` also tags its constructors and projections.

`@[trusted "id"]` also gives the declaration its id: a random UUID, which
`leanblame id` writes. The id stays when the declaration is renamed or edited;
cite the declaration by it. (The syntax is `LeanBlame.Attr.trusted`, so that
`open LeanBlame` leaves the name `trusted` free.)

A declaration of another module, also of a library you do not own, is tagged
after the fact, as `attribute [simp]` does: `attribute [trusted "id"] Name`.
A tag on a deprecated alias (`@[deprecated] alias old := new`, a rename) is
on its target.
-/
syntax (name := Attr.trusted) "trusted" (ppSpace str)? : attr

/-- Whether `s` is an id as `leanblame id` writes one: a UUID, 32 lowercase hex digits in groups of
8, 4, 4, 4 and 12, joined by `-`. -/
def isId (s : String) : Bool :=
  let groups := s.splitOn "-"
  groups.map String.length == [8, 4, 4, 4, 12] &&
    groups.all (·.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

/-- A tag: the declaration it puts on the boundary, its id if written, and where `trusted` ends in
the module that wrote it, which is where `leanblame id` writes the id. -/
structure Tag where
  decl : Name
  id : Option String
  pos : Option Position
  deriving Inhabited

/-- The tags of the imported modules and of this one, by declaration; and this module's, in order. -/
structure Tags where
  byDecl : NameMap Tag := {}
  here : Array Tag := #[]
  deriving Inhabited

initialize tagsExt : PersistentEnvExtension Tag Tag Tags ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun mods => pure {
      byDecl := mods.foldl (init := {}) fun m ts => ts.foldl (init := m) fun m t => m.insert t.decl t }
    addEntryFn := fun s t => { byDecl := s.byDecl.insert t.decl t, here := s.here.push t }
    exportEntriesFnEx := fun env s =>
      let exported := s.here.filter fun t => env.contains (skipRealize := false) t.decl
      { exported, server := exported, «private» := s.here }
  }

/-- The declaration a tag on `decl` stands for: `decl`, or, when `decl` is a deprecated alias (its
value is another constant: a rename), what the alias stands for. -/
partial def renamed (env : Environment) (decl : Name) : Name :=
  let value? := match env.find? decl with
    | some (.defnInfo d) => some d.value
    | some (.thmInfo t) => some t.value
    | _ => none
  match Linter.isDeprecated env decl, value? with
  | true, some (.const new _) => renamed env new
  | _, _ => decl

initialize registerBuiltinAttribute {
  name := `trusted
  descr := "Puts a declaration on the LeanBlame trusted boundary; `@[trusted \"id\"]` gives its id."
  add := fun decl stx kind => do
    unless kind == AttributeKind.global do throwAttrMustBeGlobal `trusted kind
    let id ← match stx[1].getOptional? with
      | none => pure none
      | some s =>
        let some id := s.isStrLit? | throwErrorAt s "`trusted` takes an id in quotes"
        unless isId id do
          throwErrorAt s "the id must be a UUID such as \"3f2b8c1e-5a7d-4e9f-8b6a-0c1d2e3f4a5b\"; \
            remove it and run `leanblame id` to write a new one"
        pure (some id)
    let env ← getEnv
    let target := renamed env decl
    if target != decl then
      logWarning m!"`{.ofConstName decl}` is a deprecated alias of `{.ofConstName target}`: the tag \
        is on `{.ofConstName target}`; write that name here"
    if (tagsExt.getState env).byDecl.contains target then
      throwError "`{.ofConstName target}` is already tagged `trusted`; a declaration has one tag"
    let pos := stx[0].getTailPos?.map (← getFileMap).toPosition
    -- `attribute [trusted] a b` would give two declarations one place for their ids.
    if pos.isSome && (tagsExt.getState env).here.any (·.pos == pos) then
      throwError "a `trusted` tag names one declaration; write `attribute [trusted] Name` for each"
    modifyEnv (tagsExt.addEntry · { decl := target, id, pos })
}

/-- Every tag, with the module that wrote it: the imported ones, then the current module's. -/
def tags (env : Environment) : Array (Name × Tag) := Id.run do
  -- `moduleNames` copies the module list on every call.
  let names := env.header.moduleNames
  let mut out := #[]
  for h : i in [:names.size] do
    out := out ++ (tagsExt.getModuleEntries env i).map (names[i], ·)
  return out ++ (tagsExt.getState env).here.map (env.mainModule, ·)

end LeanBlame
