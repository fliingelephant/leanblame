/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
/-
Adapted for LeanBlame from Lean core's `Lean/Replay.lean` (Lean FRO, Apache 2.0; the licence text
is in `cli/LICENSES/Apache-2.0.txt`).

An `Environment` holding the constants of a parsed export, so that `Lean.Meta` can infer types in
it (`Erase`). Changes: declarations are added with `addDeclWithoutChecking` instead of being sent
to the type checker (the kernel that wrote the export checked them), and the constructors and
recursors the kernel generates for an inductive are not compared with the exported ones.
-/
import Lean.Message
import Lean.Util.FoldConsts
import LeanExport.Parse

namespace LeanBlame.Load

open Lean

structure State where
  env : Kernel.Environment
  /-- Constants not added yet. -/
  remaining : NameSet
  /-- Constants whose dependencies are being added. -/
  pending : NameSet := {}

abbrev M := ReaderT (Std.HashMap Name ConstantInfo) <| StateRefT State IO

def getConst (n : Name) : M ConstantInfo := do
  let some ci := (← read)[n]? | throw <| .userError s!"'{n}' is not in the export"
  return ci

def addDecl (d : Declaration) : M Unit := do
  match (← get).env.addDeclWithoutChecking d with
  | .ok env => modify ({ · with env })
  | .error ex => throw <| .userError (← (ex.toMessageData {}).toString)

/-- Add `name` after the constants it uses (`Replay.replayConstant`). -/
partial def addConst (name : Name) : M Unit := do
  unless (← get).remaining.contains name do return
  modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
  let ci ← getConst name
  for n in ci.getUsedConstantsAsSet do addConst n
  -- A mutual block may have taken care of it.
  unless (← get).pending.contains name do return
  try
    match ci with
    | .defnInfo v => addDecl (.defnDecl v)
    | .thmInfo v => addDecl (.thmDecl v)
    | .axiomInfo v => addDecl (.axiomDecl v)
    | .opaqueInfo v => addDecl (.opaqueDecl v)
    | .quotInfo _ =>
      -- `Quot.lift` and `Quot.ind` mention `Eq`.
      addConst ``Eq
      addDecl .quotDecl
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
      addDecl (.inductDecl v.levelParams v.numParams types false)
    -- The kernel generates them with their inductive.
    | .ctorInfo _ | .recInfo _ => pure ()
    modify fun s => { s with pending := s.pending.erase name }
  catch ex => throw <| .userError s!"while adding '{name}' to the environment:\n{ex}"

/-- The constants of an export in an `Environment`. Unsafe and partial constants are left out, as
`Kernel.Environment.replay` leaves them out. -/
def environmentOfExport (e : LeanExport.ExportedEnv) : IO Environment := do
  let remaining := e.constMap.fold (init := {}) fun s n ci =>
    if ci.isUnsafe || ci.isPartial then s else s.insert n
  let env := (← mkEmptyEnvironment).toKernelEnv
  let ((), s) ← (do for n in remaining do addConst n).run e.constMap |>.run { env, remaining }
  return .ofKernelEnv s.env

end LeanBlame.Load
