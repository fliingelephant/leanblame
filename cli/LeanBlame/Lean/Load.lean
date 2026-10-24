/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
/-
Adapted for LeanBlame from Lean core's `Lean/Replay.lean` (Lean FRO, Apache 2.0; the licence text
is in `cli/LICENSES/Apache-2.0.txt`): each `Declaration` is rebuilt from the `ConstantInfo` as there.

Constants of a parsed export added to a kernel environment, in the order of the export file, which
`leanexport` writes dependency-first (`LeanExport/Basic.lean`, `dumpConstant`), so the kernel finds
what an inductive block, the `Quot` package or a checked declaration needs. For `Lean.Meta` to infer
types in (`Erase`), declarations are added with `addDeclWithoutChecking` (the kernel that wrote the
export checked them); for `equiv`'s `Old.` constants, which LeanBlame writes itself, the kernel checks
each one. Unlike `Replay`, the constructors and recursors the kernel generates for an inductive are
not compared with the exported ones.
-/
import Lean.AddDecl
import Lean.Message
import LeanExport.Parse

namespace LeanBlame.Load

open Lean

/-- The declaration that adds `ci`; for an inductive, its whole mutual block, at the block's first
member. `none` for what another declaration adds: constructors, recursors, the rest of a mutual block
or of the `Quot` package. -/
def declarationOf (consts : Std.HashMap Name ConstantInfo) (ci : ConstantInfo) :
    Except String (Option Declaration) := do
  match ci with
  | .defnInfo v => return some (.defnDecl v)
  | .thmInfo v => return some (.thmDecl v)
  | .axiomInfo v => return some (.axiomDecl v)
  | .opaqueInfo v => return some (.opaqueDecl v)
  | .quotInfo v => return if v.name == ``Quot then some .quotDecl else none
  | .inductInfo v =>
    unless v.all.head? == some v.name do return none
    let get (n : Name) : Except String ConstantInfo :=
      match consts[n]? with
      | some ci => pure ci
      | none => throw s!"'{n}' is not in the export"
    let types ← v.all.mapM fun n => do
      let t ← get n
      let ctors ← t.inductiveVal!.ctors.mapM get
      return { name := t.name, type := t.type
               ctors := ctors.map fun c => { name := c.name, type := c.type } : InductiveType }
    return some (.inductDecl v.levelParams v.numParams types false)
  | .ctorInfo _ | .recInfo _ => return none

/-- Add the constants `order` names among `consts` to `env`, in that order; with `check`, the kernel
checks each declaration. -/
def addConstants (env : Kernel.Environment) (consts : Std.HashMap Name ConstantInfo)
    (order : Array Name) (check : Bool) : IO Kernel.Environment := do
  let mut env := env
  for n in order do
    let some ci := consts[n]? | continue
    let some d ← IO.ofExcept (declarationOf consts ci) | continue
    match if check then env.addDecl {} d else env.addDeclWithoutChecking d with
    | .ok env' => env := env'
    | .error ex => throw <| .userError s!"{n}: {← (ex.toMessageData {}).toString}"
  return env

/-- The constants of an export in an `Environment`. Unsafe and partial constants are left out, as
`Kernel.Environment.replay` leaves them out. -/
def environmentOfExport (e : LeanExport.ExportedEnv) : IO Environment := do
  let order := e.constOrder.filter fun n =>
    match e.constMap[n]? with
    | some ci => !ci.isUnsafe && !ci.isPartial
    | none => false
  return .ofKernelEnv (← addConstants (← mkEmptyEnvironment).toKernelEnv e.constMap order (check := false))

end LeanBlame.Load
