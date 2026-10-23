/-
The `@[trusted]` attribute, a tag attribute of Lean core.
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
-/
initialize trustedAttr : TagAttribute ←
  registerTagAttribute `trusted "Puts a declaration on the LeanBlame trusted boundary."

/-- Whether `declName` carries `@[trusted]`, in this module or an imported one. -/
def hasTrustedTag (env : Environment) (declName : Name) : Bool :=
  trustedAttr.hasTag env declName

/-- Every declaration tagged `@[trusted]`: the imported ones, then the current module's. -/
def trustedDecls (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for i in [:env.header.moduleNames.size] do
    out := out ++ trustedAttr.ext.getModuleEntries env i
  for n in trustedAttr.ext.getState env do
    out := out.push n
  return out

end LeanBlame
