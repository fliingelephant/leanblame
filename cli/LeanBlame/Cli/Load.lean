/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
/-
Adapted for LeanBlame from Lean core's `Lean/Replay.lean` (Lean FRO, Apache 2.0; the licence text
is in `cli/LICENSES/Apache-2.0.txt`).

Constants of a parsed export added to a kernel environment, each after the constants it uses:
for `Lean.Meta` to infer types in (`Erase`), declarations are added with `addDeclWithoutChecking`
(the kernel that wrote the export checked them); for `equiv`'s `Old.` constants, which LeanBlame
writes itself, the kernel checks each one. Changes from `Replay`: the constructors and recursors the
kernel generates for an inductive are not compared with the exported ones, and an error names the
constant it is about.
-/
import Lean.AddDecl
import Lean.Message
import Lean.Util.FoldConsts
import LeanExport.Parse

namespace LeanBlame.Load

open Lean

structure Context where
  /-- The constants that may be added. -/
  consts : Std.HashMap Name ConstantInfo
  /-- Whether the kernel checks each declaration. -/
  check : Bool

structure State where
  env : Kernel.Environment
  /-- Constants not added yet. -/
  remaining : NameSet
  /-- Constants whose dependencies are being added. -/
  pending : NameSet := {}

abbrev M := ReaderT Context <| StateRefT State IO

def getConst (n : Name) : M ConstantInfo := do
  let some ci := (← read).consts[n]? | throw <| .userError s!"'{n}' is not in the export"
  return ci

def addDecl (name : Name) (d : Declaration) : M Unit := do
  let env := (← get).env
  match if (← read).check then env.addDecl {} d else env.addDeclWithoutChecking d with
  | .ok env => modify ({ · with env })
  | .error ex => throw <| .userError s!"{name}: {← (ex.toMessageData {}).toString}"

/-- Add `name` after the constants it uses (`Replay.replayConstant`). -/
partial def addConst (name : Name) : M Unit := do
  unless (← get).remaining.contains name do return
  modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
  let ci ← getConst name
  for n in ci.getUsedConstantsAsSet do addConst n
  -- A mutual block may have taken care of it.
  unless (← get).pending.contains name do return
  match ci with
  | .defnInfo v => addDecl name (.defnDecl v)
  | .thmInfo v => addDecl name (.thmDecl v)
  | .axiomInfo v => addDecl name (.axiomDecl v)
  | .opaqueInfo v => addDecl name (.opaqueDecl v)
  | .quotInfo _ =>
    -- `Quot.lift` and `Quot.ind` mention `Eq`.
    addConst ``Eq
    addDecl name .quotDecl
  | .inductInfo v =>
    let all ← v.all.mapM getConst
    for t in all do
      modify fun s => { s with remaining := s.remaining.erase t.name, pending := s.pending.erase t.name }
    let types ← all.mapM fun t => do
      let ctors ← t.inductiveVal!.ctors.mapM getConst
      for c in ctors do
        for n in c.getUsedConstantsAsSet do addConst n
      return { name := t.name, type := t.type
               ctors := ctors.map fun c => { name := c.name, type := c.type } : InductiveType }
    addDecl name (.inductDecl v.levelParams v.numParams types false)
  -- The kernel generates them with their inductive.
  | .ctorInfo _ | .recInfo _ => pure ()
  modify fun s => { s with pending := s.pending.erase name }

/-- Add `names` to `env`, each after what it uses among `consts`; with `check`, the kernel checks
each declaration. -/
def addConstants (env : Kernel.Environment) (consts : Std.HashMap Name ConstantInfo)
    (names : NameSet) (check : Bool) : IO Kernel.Environment := do
  let ((), s) ← (do for n in names do addConst n).run { consts, check } |>.run { env, remaining := names }
  return s.env

/-- The constants of an export in an `Environment`. Unsafe and partial constants are left out, as
`Kernel.Environment.replay` leaves them out. -/
def environmentOfExport (e : LeanExport.ExportedEnv) : IO Environment := do
  let names := e.constMap.fold (init := {}) fun s n ci =>
    if ci.isUnsafe || ci.isPartial then s else s.insert n
  return .ofKernelEnv (← addConstants (← mkEmptyEnvironment).toKernelEnv e.constMap names (check := false))

end LeanBlame.Load
