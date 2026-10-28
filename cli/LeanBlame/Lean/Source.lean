/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
/-
The Lean frontend (docs/design/04-architecture.md, "Beyond Lean"): a parsed export served to the core as a
`Core.Source`, and `backend`, what Lean contributes to the commands. `declOf` is adapted from
comparator's `runForUsedConsts`, which ships in the Lean toolchain as `Lake/Check/Util.lean`; the
licence text is in `cli/LICENSES/Apache-2.0.txt`.

The core keys constants by their printed name (`Lean.Name.toString`); `nameMap` maps those back and
refuses an export in which two constants print the same. Per constant the core gets its kind label,
role, number of universe parameters, the hashes of its canonical type and body with proofs erased
(`Erase`, `Canon`; docs/design/03-trust-model.md, "The hash, precisely") and the dependencies the
claim follows. All constants of one export are hashed in one `Meta` state, so that its caches serve
every constant.
-/
import Lean.Util.FoldConsts
import Lean.Util.Path
import LeanExport.Parse
import LeanBlame.Core.Hash
import LeanBlame.Lean.Canon
import LeanBlame.Lean.Load

namespace LeanBlame.Source

open Lean

/-- The kind label of a constant, as the boundary list, status and the hash name it. A definition
the export marks partial would be `partial def`; Lean 4.35 exports a `partial def` as `opaque`. -/
def kindOf : ConstantInfo → String
  | .defnInfo d => if d.safety == .safe then "def" else "partial def"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .recInfo _ => "rec"

/-- What a signer reads of a constant's body: an axiom is assumed, a theorem is proved, every other
constant is defined. -/
def roleOf : ConstantInfo → Role
  | .axiomInfo _ => .assumed
  | .thmInfo _ => .proved
  | _ => .defined

/-- The constants of an export by printed name. Fails if two of them print the same. -/
def nameMap (exported : LeanExport.ExportedEnv) : IO (Std.HashMap String Name) :=
  exported.constOrder.foldlM (init := {}) fun m n => do
    let s := n.toString
    if m[s]?.any (· != n) then
      fail s!"two constants of the export print as '{s}'; LeanBlame needs printed names to be distinct"
    return m.insert s n

/-- One `Core` and one `Meta` state, carried from one `MetaM` run to the next. -/
structure MetaRunner where
  coreState : IO.Ref Lean.Core.State
  metaState : IO.Ref Meta.State

def MetaRunner.new (env : Environment) : IO MetaRunner :=
  return { coreState := ← IO.mkRef ({ env } : Lean.Core.State), metaState := ← IO.mkRef {} }

/-- Run `x`, continuing from the states the previous run left. -/
def MetaRunner.run (r : MetaRunner) (x : MetaM α) : IO α := do
  let (a, coreState, metaState) ← x.toIO { fileName := "", fileMap := default, maxHeartbeats := 0 }
    (← r.coreState.get) {} (← r.metaState.get)
  r.coreState.set coreState
  r.metaState.set metaState
  return a

/--
The facts about one constant. Like comparator's `runForUsedConsts`, the dependencies are the
constants in the type and the value, plus constructors for inductives and the inductive for
constructors; unlike it, a theorem's value, the value of an `opaque` or `partial` definition, proof
subterms of types and definition bodies, and recursor rules are skipped.
-/
def declOf (ci : ConstantInfo) (module : String) : MetaM Core.Decl := do
  if ci.isUnsafe then
    throwError s!"'{ci.name}' is unsafe: unsafe declarations cannot be tagged or hashed"
  let ups := ci.levelParams
  let type ← Erase.eraseProofs ci.type
  let mut deps := type.getUsedConstants
  let mut bodyHash : Option String := none
  match ci with
  | .defnInfo d =>
    if d.safety == .safe then
      let body ← Erase.eraseProofs d.value
      bodyHash := some (Canon.exprHash ups body)
      deps := deps ++ body.getUsedConstants
  | .inductInfo iv =>
    bodyHash := some <| Hash.hashFields "leanblame.inductive.2"
      ([toString iv.numParams, toString iv.numIndices] ++
        iv.ctors.map (Canon.name "" ·) ++ ["all"] ++ iv.all.map (Canon.name "" ·))
    deps := deps ++ iv.ctors.toArray ++ iv.all.toArray
  | .ctorInfo cv => deps := deps.push cv.induct
  | _ => pure ()
  return {
    name := ci.name.toString, module, kind := kindOf ci, role := roleOf ci, uparams := ups.length
    typeHash := Canon.exprHash ups type, bodyHash
    deps := (Core.sortNames ((deps.filter (· != ci.name)).map toString)).eraseReps }

/-- What `Lean.collectAxioms` follows from a constant: the constants of its type and value, proofs
included, and the constructors of an inductive. -/
def usesOf : ConstantInfo → Array Name
  | .quotInfo _ => #[]
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
  | ci => ci.type.getUsedConstants ++
    ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]

/-- A parsed export as the core sees it; `moduleOf` names the module of a constant. `decl` erases
proofs in the environment `Load` builds; `uses` and `isAssumed` follow what `Lean.collectAxioms`
follows in that environment, which leaves out unsafe and partial constants. -/
def ofExport (exported : LeanExport.ExportedEnv) (moduleOf : Name → IO Name) : IO Core.Source := do
  let names ← nameMap exported
  let find? (s : String) : Option ConstantInfo := names[s]? >>= (exported.constMap[·]?)
  let inEnv? (s : String) := (find? s).filter fun ci => !ci.isUnsafe && !ci.isPartial
  let runner ← MetaRunner.new (← Load.environmentOfExport exported)
  return {
    decl := fun s => do
      let some ci := find? s | fail s!"Const not found in export '{s}'"
      runner.run (declOf ci (← moduleOf ci.name).toString)
    uses := fun s => (((inEnv? s).map usesOf).getD #[]).map toString
    isAssumed := fun s => inEnv? s matches some (.axiomInfo _) }

/-- The export file at `path`, parsed. -/
def parseFile (path : System.FilePath) : IO LeanExport.ExportedEnv := do
  LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk path .read))

/-- Export `hash` from the object store, parsed. -/
def loadExported (root : System.FilePath) (hash : String) : IO LeanExport.ExportedEnv := do
  let p := Store.objectPath root .exports hash
  unless ← p.pathExists do fail s!"export {hash} is not in the store"
  parseFile p

/-- Whether the toolchain's `leanchecker` replays the export file `path` without error: the
kernel check `release` and `equiv` run on what they store. -/
def kernelAccepts (path : System.FilePath) : IO Bool := do
  unless ← path.pathExists do fail s!"{path} is not in the store"
  let leanchecker := (← findSysroot) / "bin" / "leanchecker" |>.addExtension System.FilePath.exeExtension
  let child ← IO.Process.spawn { cmd := leanchecker.toString, stdin := .null, stdout := .null
                                 args := #["--silent", "--from-export", path.toString] }
  return (← child.wait) == 0

/-- Lean as the core's backend. The standard axioms are the three every Lean library may rest on
(docs/design/07). -/
def backend : Core.Backend where
  kernelAccepts := kernelAccepts
  checker := "leanchecker"
  standard := #[``propext, ``Classical.choice, ``Quot.sound].map (·.toString)
  incomplete := #[``sorryAx].map (·.toString)

end LeanBlame.Source
