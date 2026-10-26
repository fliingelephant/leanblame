/-
The `@[trusted]` attribute, a parametric attribute of Lean core: `@[trusted]` or `@[trusted "id"]`.
-/
module

public import Lean.Attributes

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
-/
syntax (name := Attr.trusted) "trusted" (ppSpace str)? : attr

/-- Whether `s` is an id as `leanblame id` writes one: a UUID, 32 lowercase hex digits in groups of
8, 4, 4, 4 and 12, joined by `-`. -/
def isId (s : String) : Bool :=
  let groups := s.splitOn "-"
  groups.map String.length == [8, 4, 4, 4, 12] &&
    groups.all (·.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

initialize trustedAttr : ParametricAttribute (Option String) ←
  registerParametricAttribute {
    name := `trusted
    descr := "Puts a declaration on the LeanBlame trusted boundary; `@[trusted \"id\"]` gives its id."
    getParam := fun _ stx => do
      let some s := stx[1].getOptional? | return none
      let some id := s.isStrLit? | throwErrorAt s "`trusted` takes an id in quotes"
      unless isId id do
        throwErrorAt s "the id must be a UUID such as \"3f2b8c1e-5a7d-4e9f-8b6a-0c1d2e3f4a5b\"; \
          remove it and run `leanblame id` to write a new one"
      return some id }

/-- The id written in `@[trusted "id"]` on `declName`, if any. -/
def trustedId? (env : Environment) (declName : Name) : Option String :=
  (trustedAttr.getParam? env declName).join

/-- Every declaration tagged `@[trusted]`, with its id: the imported ones, then the current
module's. -/
def trustedDecls (env : Environment) : Array (Name × Option String) := Id.run do
  let mut out := #[]
  for i in [:env.header.moduleNames.size] do
    out := out ++ trustedAttr.ext.getModuleEntries env i
  for n in (trustedAttr.ext.getState env).1.reverse do
    out := out.push (n, trustedId? env n)
  return out

end LeanBlame
