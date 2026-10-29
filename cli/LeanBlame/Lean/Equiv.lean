/-
`leanblame equiv [NAME...]` (trust-model.md, "`equiv`").

Mechanical: no build, no tactics. For each tagged declaration X that is `outdated` with `untagged`
as the only cause (the named ones, else all), compared with X's last live approval:
1. Old meaning. From the export that approval names, what X's old statement (and value, for a
   definition) uses that is not shared goes under `Old.`, references renamed, into the environment
   of the current export, and so does a definition X itself; the kernel checks each. Not shared: an
   untagged hashed constant whose claim changed, or a constant used only in proofs (so not hashed)
   that the current export lacks or states differently. Tagged constants are always shared.
2. Goals. For X and for each changed definition C still present, one kernel call decides whether
   old and new are definitionally equal:
   `theorem LeanBlame.Equiv.C : Old.C = C := Eq.refl C`, or for a theorem X
   `<old statement> ↔ <new statement>`, proved by the identity both ways. Steps 1 and 2 are
   `prove`, which `challenge --check` runs too, with the library as the old version.
3. The accepted theorems, with what they use, go to the object store as the solution export, which
   `leanchecker` replays (the kernel check `release` runs): a file anyone can check again.
4. For each X whose own theorem was accepted, an evidence file (`Store.evidencePath`) names the
   solution export: `status` shows it as X's `evidence`, `sign` puts the hash in X's entry of the
   record.
What is left is for a human to read: equiv prints the root causes, with the old and new values of
each changed definition that is not definitionally equal.

The hashes come from the graphs `export` stored (docs/decisions.md, "Storage"), keyed by
printed name; the terms from the old and current exports.
-/
import LeanBlame.Core.Status
import LeanBlame.Lean.Export

namespace LeanBlame.Equiv

open Lean

def oldName (n : Name) : Name := `Old ++ n

def thmName (n : Name) : Name := `LeanBlame.Equiv ++ n

/-- `e` with references to the constants of `dup`, and projections out of them, renamed to `Old.`;
the other constants named as the current environment names them (`toNew`). -/
partial def renameExpr (dup : NameSet) (toNew : Name → Name) (e : Expr) : Expr :=
  let rename (n : Name) := if dup.contains n then oldName n else toNew n
  e.replace fun
    | .const n us => some (.const (rename n) us)
    | .proj s i b => some (.proj (rename s) i (renameExpr dup toNew b))
    | _ => none

/-- An old constant as the `Old.` constant: its name and references to `dup` renamed, the other
references named by `toNew`. -/
def renameConst (dup : NameSet) (toNew : Name → Name) (ci : ConstantInfo) : ConstantInfo :=
  let e := renameExpr dup toNew
  let n (x : Name) := if dup.contains x || x == ci.name then oldName x else toNew x
  match ci with
  | .defnInfo v => .defnInfo { v with name := n v.name, type := e v.type, value := e v.value, all := v.all.map n }
  | .thmInfo v => .thmInfo { v with name := n v.name, type := e v.type, value := e v.value, all := v.all.map n }
  | .opaqueInfo v => .opaqueInfo { v with name := n v.name, type := e v.type, value := e v.value, all := v.all.map n }
  | .axiomInfo v => .axiomInfo { v with name := n v.name, type := e v.type }
  | .inductInfo v => .inductInfo { v with name := n v.name, type := e v.type, all := v.all.map n, ctors := v.ctors.map n }
  | .ctorInfo v => .ctorInfo { v with name := n v.name, type := e v.type, induct := n v.induct }
  | .recInfo v => .recInfo { v with name := n v.name, type := e v.type, all := v.all.map n,
                                    rules := v.rules.map fun r => { r with ctor := n r.ctor, rhs := e r.rhs } }
  | .quotInfo v => .quotInfo v

/-- Whether old constant `o`, renamed, is the current constant `n`: the same type, and for anything
but a theorem (proof irrelevance) the same value. -/
def sameDecl (dup : NameSet) (toNew : Name → Name) (o n : ConstantInfo) : Bool :=
  let e (x : Expr) := (renameExpr dup toNew x).instantiateLevelParams o.levelParams (n.levelParams.map .param)
  o.levelParams.length == n.levelParams.length && e o.type == n.type &&
    (o matches .thmInfo _ || (o.value? (allowOpaque := true)).map e == n.value? (allowOpaque := true))

/-- Add a declaration, checked by the kernel; the kernel's message if it is rejected. -/
def addChecked (env : Kernel.Environment) (d : Declaration) : IO (Except String Kernel.Environment) := do
  match env.addDecl {} d with
  | .ok env => return .ok env
  | .error ex => return .error (← (ex.toMessageData {}).toString)

def runMeta (env : Kernel.Environment) (x : MetaM α) : IO α := do
  let options := ({} : Options).setBool `pp.notation false |>.setBool `pp.fieldNotation false
  let (a, _, _) ← x.toIO { fileName := "", fileMap := default, options, maxHeartbeats := 0 }
    { env := .ofKernelEnv env }
  return a

/-- `e` printed with notation (field notation too) off. -/
def pp (env : Kernel.Environment) (e : Expr) : IO String := do
  return toString (← runMeta env (PrettyPrinter.ppExpr e))

/-- The statement that old and current `c` mean the same, with its proof: `Old.c = c` for a safe
definition with the same number of universe parameters, `<old type> ↔ <type>` for a theorem; or why
there is none. The kernel accepts it exactly when the two are definitionally equal. -/
def goal (env : Kernel.Environment) (dup : NameSet) (toNew : Name → Name) (c : Name) (o n : ConstantInfo) :
    IO (Except String (Expr × Expr)) := do
  let us := n.levelParams.map Level.param
  unless o.levelParams.length == us.length do return .error "its universe parameters changed"
  match o, n with
  | .defnInfo ov, .defnInfo nv =>
    unless ov.safety == .safe && nv.safety == .safe do return .error "it is not a safe definition"
    let u ← runMeta env (Meta.getLevel n.type)
    let new := Expr.const (toNew c) us
    return .ok (mkApp3 (.const ``Eq [u]) n.type (.const (oldName c) us) new, mkApp2 (.const ``Eq.refl [u]) n.type new)
  | .thmInfo _, .thmInfo _ =>
    let a := (renameExpr dup toNew o.type).instantiateLevelParams o.levelParams us
    let b := n.type
    return .ok (mkIff a b,
                mkApp4 (.const ``Iff.intro []) a b (.lam `h a (.bvar 0) .default) (.lam `h b (.bvar 0) .default))
  | _, _ => return .error s!"no goal for a changed {Source.kindOf n}"

/-- Two versions of the same declarations, for the kernel to compare: each one's graph, and its
constants by the names the old graph gives them (`none`: not at hand). `toNew` names a constant as
the current environment has it; `oldPos` orders old constants dependency-first. -/
structure Sides where
  old : Core.Hashed
  new : Core.Hashed
  oldConst? : Name → Option ConstantInfo
  newConst? : Name → Option ConstantInfo
  toNew : Name → Name := id
  oldPos : Name → Nat

/-- What the kernel accepted. -/
structure Proven where
  /-- The current environment with the `Old.` constants and the accepted theorems. -/
  env : Kernel.Environment
  /-- The accepted theorems. -/
  theorems : Array Name
  /-- The targets whose own theorem was accepted. -/
  targets : Array Name
  /-- Why the others were not, from the root causes: a line each, with the old and new values of a
  definition that is not definitionally equal. -/
  notes : Array (String × Array String)

/--
Ask the kernel whether the targets of `sides` mean the same in both versions, in `base`, the current
environment. What an old meaning uses that is not shared goes under `Old.`, references renamed: an
untagged hashed constant whose claim changed, or a constant used only in proofs (so not hashed) that
the current version lacks or states differently; tagged constants and constants not at hand are
shared. The kernel checks each `Old.` constant, then decides, one call each, whether every changed
definition and every target is definitionally equal to its old version.
-/
def prove (base : Kernel.Environment) (sides : Sides) (targets : Array Name) : IO Proven := do
  let ⟨old, new, oldConst?, newConst?, toNew, oldPos⟩ := sides
  let targetSet : NameSet := targets.foldl (·.insert ·) {}
  let isTarget := targetSet.contains
  -- What an old meaning uses: of a target theorem only its statement.
  let uses (c : Name) : Array Name := match oldConst? c with
    | some ci => if isTarget c && ci matches .thmInfo _ then ci.type.getUsedConstants
      else ci.getUsedConstantsAsSet.toArray
    | none => #[]
  -- The constants to duplicate, until nothing is added.
  let needs (dup : NameSet) (r : Name) : Bool :=
    let s := r.toString
    !old.isTagged s && match old.nodes[s]? with
    | some o => (new.nodes[s]?.map (·.claim)) != some o.claim
    | none => match oldConst? r, newConst? r with
      | some o, some n => !sameDecl dup toNew o n
      | some _, none => true
      | none, _ => false
  let seeds := targets.flatMap uses
  let mut dup : NameSet := {}
  repeat
    let size := dup.size
    let mut todo := seeds ++ dup.toArray.flatMap uses
    while h : todo.size > 0 do
      let r := todo[todo.size - 1]
      todo := todo.pop
      if !dup.contains r && needs dup r then
        dup := dup.insert r
        todo := todo ++ uses r
    if dup.size == size then break
  -- `Old.` constants: the duplicated ones, and each target definition.
  let consts : Std.HashMap Name ConstantInfo :=
    (dup.toArray ++ targets).foldl (init := {}) fun m c =>
      match oldConst? c with
      | some ci => if isTarget c && !(ci matches .defnInfo _) then m else m.insert (oldName c) (renameConst dup toNew ci)
      | none => m
  let succ (c : Name) := (uses c).filter dup.contains
  -- In dependency order: rebuild each component, then check its goals. `taint` holds, per constant,
  -- the failures at or below it that its goal may rest on.
  let mut env := base
  let mut broken : NameSet := {}
  let mut taint : Std.HashMap Name (Array Name) := {}
  let mut theorems : Array Name := #[]
  let mut notes : Array (String × Array String) := #[]
  for comp in Walk.tarjan (dup.toArray ++ targets) succ do
    let deps := (comp.flatMap succ).filter (!comp.contains ·)
    let below := dedup (deps.flatMap (taint.getD · #[]))
    -- `Old.` constants are added in the old order, which is dependency-first.
    let names := (comp.filter (consts.contains <| oldName ·)).qsort (oldPos · < oldPos ·) |>.map oldName
    let rebuilt ← if deps.any broken.contains then pure false else
      try
        env ← Load.addConstants env consts names true
        pure true
      catch e =>
        notes := notes.push (s!"cannot rebuild {e}", #[])
        pure false
    for c in comp do
      unless rebuilt do
        broken := broken.insert c
        taint := taint.insert c (dedup (below.push c))
        continue
      -- A failure is a root cause when nothing below it failed.
      let rootCause := below.isEmpty
      let failed := if rootCause then #[c] else below
      match oldConst? c, newConst? c, old.nodes[c.toString]?, new.nodes[c.toString]? with
      | some o, some n, some oldNode, some newNode =>
        match ← goal env dup toNew c o n with
        | .error why =>
          if rootCause then notes := notes.push (s!"{c}: {why}", #[])
          taint := taint.insert c failed
        | .ok (stmt, proof) =>
          let decl : Declaration :=
            .thmDecl { name := thmName c, levelParams := n.levelParams, type := stmt, value := proof }
          match ← addChecked env decl with
          | .ok env' =>
            env := env'
            theorems := theorems.push (thmName c)
            taint := taint.insert c #[]
          | .error msg =>
            if rootCause then
              if oldNode.own != newNode.own then
                notes := notes.push (s!"{c}: not definitionally equal",
                  #[s!"  old: {← pp env (o.value?.getD o.type)}", s!"  new: {← pp env (n.value?.getD n.type)}"])
              else notes := notes.push (s!"{c}: not definitionally equal to its old version ({msg})", #[])
            taint := taint.insert c failed
      -- Used only in proofs, or gone: nothing to state.
      | _, _, _, _ => taint := taint.insert c below
  let proven := targets.filter (theorems.contains <| thmName ·)
  for t in targets do
    let causes := (taint.getD t #[]).filter (· != t)
    unless proven.contains t || causes.isEmpty do
      notes := notes.push (s!"{t}: not proven, because of {", ".intercalate (causes.toList.map toString)}", #[])
  return { env, theorems, targets := proven, notes }

/-- One eligible declaration: its id, the approve record it is compared with and its current claim. -/
structure Target where
  name : Name
  id : String
  record : String
  claim : String

/--
Prove the targets that share one old export and boundary list (`old`, `oldExp`); returns those
proven, with the hash of the solution export.
-/
def proveGroup (root : System.FilePath) (base : Kernel.Environment) (new old : Core.Hashed)
    (newExp oldExp : LeanExport.ExportedEnv) (targets : Array Target) :
    IO (Array Target × String) := do
  let pos : Std.HashMap Name Nat := oldExp.constOrder.foldl (init := {}) fun m c => m.insert c m.size
  let p ← prove base { old, new, oldConst? := (oldExp.constMap[·]?), newConst? := (newExp.constMap[·]?)
                       oldPos := (pos.getD · 0) } (targets.map (·.name))
  for (line, detail) in p.notes do
    IO.eprintln s!"{line}; a human reads"
    for d in detail do IO.eprintln d
  let proven := targets.filter (p.targets.contains ·.name)
  if proven.isEmpty then return (#[], "")
  -- The solution export: the accepted theorems and what they use, replayed by `leanchecker`.
  let tmp ← Store.tmpPath root "solution"
  let solution ← Store.putFile root .proofs tmp (← Export.dumpToFile (.ofKernelEnv p.env) p.theorems tmp)
  unless ← Source.kernelAccepts (Store.objectPath root .proofs solution) do
    fail s!"leanchecker rejected the solution export {solution}"
  return (proven, solution)

def run (root : System.FilePath) (keys : Array String) : IO UInt32 := do
  let ledger ← Ledger.load root
  let r ← Status.compute root ledger
  let decls := r.report.declarations
  let new := r.new
  let names ← keys.mapM fun k => do
    let some d ← IO.ofExcept (new.boundary.find? k) | fail s!"{k} is not on the boundary list"
    pure d.name
  -- Eligible: outdated, and `untagged` the only cause; with the approve record compared with.
  let mut eligible : Array (String × StatusDecl × LoadedRecord × ApproveRecord) := #[]
  let mut left := 0
  for d in decls do
    let n := d.decl.name
    unless names.isEmpty || names.contains n do continue
    let untaggedOnly := match d.change with
      | some #[c] => c.cause == .untagged
      | _ => false
    if d.state == .outdated && untaggedOnly then
      let some (lastRec, a, _) := (Status.liveApprovals ledger d.decl.id).back?
        | fail s!"{n} is outdated but has no live approval"
      eligible := eligible.push (n, d, lastRec, a)
    else if !names.isEmpty && d.state != .valid then
      left := left + 1
      IO.eprintln (if d.state == .unsigned then s!"{n}: unsigned: no approved meaning to compare with"
        else s!"{Status.textLine d}\n{n}: no goal: a cause other than `untagged`; a human reads")
  if eligible.isEmpty then
    if left == 0 then IO.println "equiv: no outdated declaration whose only cause is untagged"
    return if left == 0 then 0 else 1
  let newExp ← Source.loadExported root r.cur.exportHash
  let constOf ← Source.nameMap newExp
  let targets : Array (Target × ApproveRecord) ← eligible.mapM fun (n, d, lastRec, a) => do
    let some c := constOf[n]? | fail s!"{n} is not in the current export"
    pure ({ name := c, id := d.decl.id, record := lastRec.hash, claim := d.claim }, a)
  let base := (← Load.environmentOfExport newExp).toKernelEnv
  -- One group per old export and boundary list.
  let groups := dedup (targets.map fun (_, a) => (a.exportHash, a.boundary))
  let mut proven := 0
  for (e, b) in groups do
    let old ← Status.graph root e b
    let group := (targets.filter fun (_, a) => a.exportHash == e && a.boundary == b).map (·.1)
    let (ok, solution) ← proveGroup root base (new := new) (newExp := newExp) (old := old)
      (oldExp := ← Source.loadExported root e) group
    for t in ok do
      let evidence : Store.Evidence := { id := t.id, claim := t.claim, oldRecord := t.record, proof := solution }
      writeFileMkdirs (Store.evidencePath root t.claim) (jsonText evidence)
      IO.println s!"{t.name} proven {solution}"
    proven := proven + ok.size
    left := left + group.size - ok.size
  IO.println s!"equiv: {proven} proven, {left} left to a human"
  return if left == 0 then 0 else 1

end LeanBlame.Equiv
