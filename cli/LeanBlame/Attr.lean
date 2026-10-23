/-
Adapted from lean-eval-generator, `LeanEvalGenerator/Core/Markers.lean`
(https://github.com/leanprover/lean-eval-generator, commit 0b8cc2d1, the
`@[eval_problem]` attribute that lean-eval uses).
Copyright 2026 Lean FRO. Licensed under the Apache License, Version 2.0.

Changes: renamed `eval_problem` to `trusted`; dropped the manifest lookup, the
binder validation and the hover info; kept the persistent extension and the
attribute registration unchanged.
-/
module

public import Lean.Attributes

public section

open Lean

namespace LeanBlame

/--
The declarations tagged `@[trusted]` in each module. Persistent: the entries of
every imported module are stored in its `.olean` and visible to importers.
-/
initialize trustedExt : PersistentEnvExtension Name Name NameSet ←
  registerPersistentEnvExtension {
    name := `LeanBlame.trustedExt
    mkInitial := pure {}
    addImportedFn := fun _ _ => pure {}
    addEntryFn := fun (s : NameSet) n => s.insert n
    exportEntriesFnEx := fun env es =>
      let entries : Array Name := es.foldl (fun acc entry => acc.push entry) #[]
      let entries := entries.filter (env.contains (skipRealize := false))
      .uniform <| entries.qsort Name.quickLt
    statsFn := fun s => "trusted attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
    asyncMode := .mainOnly
    replay? := some fun _ newState newConsts s =>
      newConsts.foldl (init := s) fun acc c =>
        if newState.contains c then acc.insert c else acc
  }

/--
`@[trusted]` puts a declaration on the trusted boundary: a human must read it,
with its docstring, for results that use it to mean anything. Tagging a
`structure` or `inductive` also tags its constructors and projections.
-/
initialize trustedAttr : AttributeImpl ←
  let attrImpl : AttributeImpl := {
    ref := `trusted
    name := `trusted
    descr := "Puts a declaration on the LeanBlame trusted boundary."
    applicationTime := AttributeApplicationTime.afterTypeChecking
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal `trusted kind
      let env ← getEnv
      unless (env.getModuleIdxFor? decl).isNone do
        throwAttrDeclInImportedModule `trusted decl
      unless trustedExt.toEnvExtension.asyncMayModify env decl do
        throwAttrNotInAsyncCtx `trusted decl env.asyncPrefix?
      modifyEnv fun env => trustedExt.addEntry (asyncDecl := decl) env decl
  }
  registerBuiltinAttribute attrImpl
  pure attrImpl

/-- Whether `declName` carries `@[trusted]`, in this module or an imported one. -/
def hasTrustedTag (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some modIdx => (trustedExt.getModuleEntries env modIdx).binSearchContains declName Name.quickLt
  | none => (trustedExt.getState (asyncDecl := declName) env).contains declName

/-- Every declaration tagged `@[trusted]`: the imported ones, then the current module's. -/
def trustedDecls (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for i in [:env.header.moduleNames.size] do
    out := out ++ trustedExt.getModuleEntries env i
  for n in trustedExt.getState env do
    out := out.push n
  return out

end LeanBlame
