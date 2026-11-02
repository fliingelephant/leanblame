/-
The imported modules of an environment: the one that declares a constant, and a module's data.
`EnvironmentHeader.moduleNames` makes a new array on every call, so these index the header.
-/
import Lean.Environment

namespace LeanBlame

open Lean

/-- The imported module that declares `n`. -/
def moduleOf? (env : Environment) (n : Name) : Option Name := do
  env.header.modules[(← env.getModuleIdxFor? n).toNat]?.map (·.module)

/-- The data of the imported module `m`. -/
def moduleData? (env : Environment) (m : Name) : Option ModuleData := do
  env.header.moduleData[(← env.getModuleIdx? m).toNat]?

/-- What the imported module `m` imports. -/
def importsOf (env : Environment) (m : Name) : Array Name :=
  ((moduleData? env m).map (·.imports.map (·.module))).getD #[]

end LeanBlame
