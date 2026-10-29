/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
/-
The Lean frontend (docs/decisions.md, "Beyond Lean"): a parsed export served to the core as a
`Core.Source`, the constants of an environment in memory served as the same facts (`declsIn`), and
`backend`, what Lean contributes to the commands. `declOf` is adapted from comparator's
`runForUsedConsts`, which ships in the Lean toolchain as `Lake/Check/Util.lean`; the licence text is
in `cli/LICENSES/Apache-2.0.txt`.

The core keys constants by their printed name (`Lean.Name.toString`); `nameMap` maps those back and
refuses an export in which two constants print the same. Per constant the core gets its kind label,
role, number of universe parameters, the hashes of its canonical type and body with proofs erased
(`Erase`, `Canon`; trust-model.md, "The hash, precisely") and the dependencies the
claim follows. All constants of one export are hashed in one `Meta` state, so that its caches serve
every constant. That state sees the constants alone: the environment an export rebuilds has no
environment extensions, an environment in memory is imported without them, and smart unfolding,
which depends on helpers an export may leave out, is off.
-/
import Lean.Util.FoldConsts
import Lean.Util.Path
import LeanExport.Parse
import LeanBlame.Core.Hash
import LeanBlame.Lean.Canon
import LeanBlame.Lean.Load

namespace LeanBlame.Source

open Lean

/-- The kernel's kind of a constant, as the hash takes it (the boundary list names it in words:
`Export.kindWord`). A definition the export marks partial would be `partial def`; Lean 4.35 exports
a `partial def` as `opaque`. -/
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
  let options := ({} : Options).setBool `smartUnfolding false
  let (a, coreState, metaState) ← x.toIO { fileName := "", fileMap := default, options, maxHeartbeats := 0 }
    (← r.coreState.get) {} (← r.metaState.get)
  r.coreState.set coreState
  r.metaState.set metaState
  return a

/--
The facts about one constant, its constants named by `rename?` and its dependencies printed by
`print`. Like comparator's `runForUsedConsts`, the dependencies are the constants in the type and the
value, plus constructors for inductives and the inductive for constructors; unlike it, a theorem's
value, the value of an `opaque` or `partial` definition, proof subterms of types and definition
bodies, and recursor rules are skipped.
-/
def declOf (ci : ConstantInfo) (module : String) (print : Name → IO String)
    (rename? : Option (Name → Name) := none) : MetaM Core.Decl := do
  if ci.isUnsafe then
    throwError s!"'{ci.name}' is unsafe: unsafe declarations cannot be tagged or hashed"
  let rename := rename?.getD id
  let renamed (e : Expr) : Expr := match rename? with
    | some f => e.replace fun | .const n us => some (.const (f n) us) | _ => none
    | none => e
  let ups := ci.levelParams
  let type ← Erase.eraseProofs ci.type
  let mut deps := type.getUsedConstants
  let mut bodyHash : Option String := none
  match ci with
  | .defnInfo d =>
    if d.safety == .safe then
      let body ← Erase.eraseProofs d.value
      bodyHash := some (Canon.exprHash ups (renamed body))
      deps := deps ++ body.getUsedConstants
  | .inductInfo iv =>
    bodyHash := some <| Hash.hashFields "leanblame.inductive"
      ([toString iv.numParams, toString iv.numIndices] ++
        iv.ctors.map (Canon.name "" <| rename ·) ++ ["all"] ++ iv.all.map (Canon.name "" <| rename ·))
    deps := deps ++ iv.ctors.toArray ++ iv.all.toArray
  | .ctorInfo cv => deps := deps.push cv.induct
  | _ => pure ()
  let printed ← (deps.filter (· != ci.name)).mapM (print ·)
  return {
    name := (rename ci.name).toString, module, kind := kindOf ci, role := roleOf ci, uparams := ups.length
    typeHash := Canon.exprHash ups (renamed type), bodyHash, deps := (Core.sortNames printed).eraseReps }

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
      runner.run (declOf ci (← moduleOf ci.name).toString (pure ·.toString))
    uses := fun s => (((inEnv? s).map usesOf).getD #[]).map toString
    isAssumed := fun s => inEnv? s matches some (.axiomInfo _) }

/-- `Source.decl` for the constants of `env`, imported without its environment extensions, as an
export of them would serve it, without writing the export (`Challenge.check`); `rename?` names
constants as another export does. A printed name maps back to the constant it was printed from:
`roots`, and each dependency once reported; two constants that print the same are an error. -/
def declsIn (env : Environment) (roots : Array Name) (moduleOf : Name → IO Name)
    (rename? : Option (Name → Name) := none) : IO (String → IO Core.Decl) := do
  let rename := rename?.getD id
  let names ← IO.mkRef ({} : Std.HashMap String Name)
  let print (n : Name) : IO String := do
    let s := (rename n).toString
    match (← names.get)[s]? with
    | some m => unless m == n do fail s!"two constants print as '{s}'; LeanBlame needs printed names to be distinct"
    | none => names.modify (·.insert s n)
    return s
  for r in roots do discard <| print r
  let runner ← MetaRunner.new env
  return fun s => do
    let some ci := (← names.get)[s]? >>= env.find? | fail s!"'{s}' is not a constant here"
    runner.run (declOf ci (← moduleOf ci.name).toString print rename?)

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
(docs/decisions.md, "Releases"). -/
def backend : Core.Backend where
  kernelAccepts := kernelAccepts
  checker := "leanchecker"
  standard := #[``propext, ``Classical.choice, ``Quot.sound].map (·.toString)
  incomplete := #[``sorryAx].map (·.toString)

end LeanBlame.Source
