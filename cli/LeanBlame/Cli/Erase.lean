/-
Proof erasure (docs/03-trust-model.md, "The hash, precisely"): every subterm of
a definition body whose type is a proposition is replaced by a marker before
hashing.

"Is this subterm a proof?" needs its type and the type of that type. This file
has a small type inferer over the parsed export: weak-head reduction with beta,
zeta, delta (definitions), iota (recursors on constructors and literals) and
projections of constructors, and `inferType` for every expression form. It does
not check anything: the export was checked by the kernel.

The answer errs on one side only. A subterm counts as a proof only when its
type's type reduces to `Sort u` with `u` zero for every universe assignment.
When inference fails (an unsupported reduction, the step budget runs out), the
subterm is kept and hashed. Keeping a proof costs a spurious hash change;
erasing a non-proof would hide a change of meaning, and cannot happen here
short of a bug.
-/
import LeanExport.Parse
import Lean.Environment
import Lean.Util.InstantiateLevelParams

namespace LeanBlame.Erase

open Lean

/-- The marker that replaces an erased proof. Never occurs in exported terms. -/
def proofMarker : Expr := .mvar ⟨`_leanblame_erased_proof⟩

def isProofMarker (e : Expr) : Bool := e == proofMarker

structure Ctx where
  consts : Std.HashMap Name ConstantInfo

structure St where
  /-- Types of the local variables introduced while descending under binders. -/
  lctx : Std.HashMap FVarId Expr := {}
  /-- Values of `let`-bound locals. -/
  lvals : Std.HashMap FVarId Expr := {}
  nextId : Nat := 0
  fuel : Nat := 0
  inferCache : Std.HashMap Expr Expr := {}

abbrev M := ReaderT Ctx (StateT St (Except String))

/-- Steps allowed for one "is this a proof?" question. -/
def stepBudget : Nat := 20000

def tick : M Unit := do
  let s ← get
  if s.fuel == 0 then throw "out of fuel"
  set { s with fuel := s.fuel - 1 }

def mkLocal (type : Expr) (value? : Option Expr := none) : M Expr := do
  let s ← get
  let id : FVarId := ⟨.num `_leanblame_local s.nextId⟩
  let lvals := match value? with
    | some v => s.lvals.insert id v
    | none => s.lvals
  set { s with nextId := s.nextId + 1, lctx := s.lctx.insert id type, lvals }
  return .fvar id

def getConst? (n : Name) : M (Option ConstantInfo) :=
  return (← read).consts[n]?

/-- A level that is zero under every assignment of its parameters. -/
def levelIsZero : Level → Bool
  | .zero => true
  | .succ _ => false
  | .max a b => levelIsZero a && levelIsZero b
  | .imax _ b => levelIsZero b
  | .param _ => false
  | .mvar _ => false

/-- A natural-number literal as a constructor application, for iota reduction. -/
def natLitToCtor : Expr → Expr
  | .lit (.natVal 0) => .const ``Nat.zero []
  | .lit (.natVal (n+1)) => .app (.const ``Nat.succ []) (.lit (.natVal n))
  | e => e

mutual

/-- Weak-head normal form, as far as this reducer goes. -/
partial def whnf (e : Expr) : M Expr := do
  tick
  match e with
  | .mdata _ b => whnf b
  | .letE _ _ v b _ => whnf (b.instantiate1 v)
  | .fvar id =>
    match (← get).lvals[id]? with
    | some v => whnf v
    | none => return e
  | .proj _ i s =>
    match ← projCtor? (← whnf s) i with
    | some r => whnf r
    | none => return e
  | .app .. | .const .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .lam .. => whnf (f.betaRev args.reverse)
    | .mdata _ f' => whnf (mkAppN f' args)
    | .letE .. | .proj .. | .fvar .. =>
      let f' ← whnf f
      if f' == f then return e else whnf (mkAppN f' args)
    | .const c us =>
      match ← getConst? c with
      | some (.defnInfo d) =>
        if d.safety == .safe && d.levelParams.length == us.length then
          whnf ((d.value.instantiateLevelParams d.levelParams us).betaRev args.reverse)
        else return e
      | some (.recInfo r) =>
        match ← iota? r us args with
        | some e' => whnf e'
        | none => return e
      | _ => return e
    | _ => return e
  | _ => return e

/-- Field `i` of a structure value that reduced to a constructor application. -/
partial def projCtor? (s : Expr) (i : Nat) : M (Option Expr) := do
  let .const c _ := s.getAppFn | return none
  let some (.ctorInfo cv) ← getConst? c | return none
  let args := s.getAppArgs
  return args[cv.numParams + i]?

/-- One recursor step on a constructor (or literal) major premise. -/
partial def iota? (r : RecursorVal) (us : List Level) (args : Array Expr) : M (Option Expr) := do
  let majorIdx := r.numParams + r.numMotives + r.numMinors + r.numIndices
  let some major := args[majorIdx]? | return none
  let major := natLitToCtor (← whnf major)
  let .const c _ := major.getAppFn | return none
  let some rule := r.rules.find? (·.ctor == c) | return none
  let majorArgs := major.getAppArgs
  if majorArgs.size < rule.nfields || r.levelParams.length != us.length then return none
  let rhs := rule.rhs.instantiateLevelParams r.levelParams us
  let rhs := mkAppN rhs (args.extract 0 (r.numParams + r.numMotives + r.numMinors))
  let rhs := mkAppN rhs (majorArgs.extract (majorArgs.size - rule.nfields) majorArgs.size)
  return some (mkAppN rhs (args.extract (majorIdx + 1) args.size))

partial def sortLevel (t : Expr) : M Level := do
  match ← whnf t with
  | .sort l => return l
  | _ => throw "type expected"

partial def inferType (e : Expr) : M Expr := do
  tick
  if let some t := (← get).inferCache[e]? then return t
  let t ← match e with
    | .bvar _ => throw "loose bound variable"
    | .mvar _ => throw "metavariable"
    | .fvar id =>
      match (← get).lctx[id]? with
      | some t => pure t
      | none => throw "unknown local"
    | .sort l => pure (.sort (.succ l))
    | .const c us =>
      match ← getConst? c with
      | some ci =>
        if ci.levelParams.length != us.length then throw s!"universe arity of {c}"
        pure (ci.instantiateTypeLevelParams us)
      | none => throw s!"unknown constant {c}"
    | .app .. => inferApp e.getAppFn e.getAppArgs
    | .lam .. => inferLambda e
    | .forallE .. => inferForall e
    | .letE _ _ v b _ => inferType (b.instantiate1 v)
    | .lit (.natVal _) => pure (.const ``Nat [])
    | .lit (.strVal _) => pure (.const ``String [])
    | .mdata _ b => inferType b
    | .proj s i st => inferProj s i st
  modify fun st => { st with inferCache := st.inferCache.insert e t }
  return t

/-- As `Lean.Meta.inferAppType`. -/
partial def inferApp (f : Expr) (args : Array Expr) : M Expr := do
  let mut fType ← inferType f
  let mut j := 0
  for i in [:args.size] do
    match fType with
    | .forallE _ _ b _ => fType := b
    | _ =>
      match ← whnf (fType.instantiateRevRange j i args) with
      | .forallE _ _ b _ =>
        j := i
        fType := b
      | _ => throw "function expected"
  return fType.instantiateRevRange j args.size args

partial def inferLambda (e : Expr) : M Expr := do
  let mut fvars : Array Expr := #[]
  let mut binders : Array (Name × Expr × BinderInfo) := #[]
  let mut cur := e
  repeat
    match cur with
    | .lam n d b bi =>
      let d := d.instantiateRev fvars
      fvars := fvars.push (← mkLocal d)
      binders := binders.push (n, d, bi)
      cur := b
    | _ => break
  let bodyType ← inferType (cur.instantiateRev fvars)
  let mut r := bodyType.abstract fvars
  for i' in [:fvars.size] do
    let i := fvars.size - 1 - i'
    let (n, d, bi) := binders[i]!
    r := .forallE n (d.abstractRange i fvars) r bi
  return r

partial def inferForall (e : Expr) : M Expr := do
  let mut fvars : Array Expr := #[]
  let mut levels : Array Level := #[]
  let mut cur := e
  repeat
    match cur with
    | .forallE _ d b _ =>
      let d := d.instantiateRev fvars
      levels := levels.push (← sortLevel (← inferType d))
      fvars := fvars.push (← mkLocal d)
      cur := b
    | _ => break
  let mut l ← sortLevel (← inferType (cur.instantiateRev fvars))
  for i' in [:levels.size] do
    l := .imax levels[levels.size - 1 - i']! l
  return .sort l

partial def inferProj (structName : Name) (i : Nat) (st : Expr) : M Expr := do
  let ty ← whnf (← inferType st)
  let .const iName us := ty.getAppFn | throw "projection of a non-structure"
  let args := ty.getAppArgs
  let some (.inductInfo iv) ← getConst? iName | throw "projection of a non-inductive"
  unless iName == structName do throw "projection type mismatch"
  let [ctorName] := iv.ctors | throw "projection of a type with several constructors"
  let some ctor ← getConst? ctorName | throw "unknown constructor"
  let mut ct := ctor.instantiateTypeLevelParams us
  for k in [:iv.numParams] do
    match ← whnf ct with
    | .forallE _ _ b _ => ct := b.instantiate1 (args[k]?.getD (.bvar 0))
    | _ => throw "bad constructor type"
  for k in [:i] do
    match ← whnf ct with
    | .forallE _ _ b _ => ct := b.instantiate1 (.proj structName k st)
    | _ => throw "bad constructor type"
  match ← whnf ct with
  | .forallE _ d _ _ => return d
  | _ => throw "bad constructor type"

end

/-- Whether `e` (closed but for locals) is a proof. Failures answer `false`: keep it. -/
def isProof (e : Expr) : M Bool := do
  match e with
  | .sort _ | .forallE .. | .lit _ => return false
  | _ => pure ()
  -- The kernel rejects theorems whose type is not a proposition, so any application of a
  -- theorem is a proof.
  if let .const c _ := e.getAppFn then
    if let some (.thmInfo _) ← getConst? c then return true
  let saved ← get
  modify fun s => { s with fuel := stepBudget }
  let attempt : M Bool := do
    let ty ← inferType e
    match ← whnf (← inferType ty) with
    | .sort l => return levelIsZero l
    | _ => return false
  try attempt catch _ => do
    -- Drop locals and cache entries made by the failed attempt; keep the counter fresh.
    let n := (← get).nextId
    set { saved with nextId := n }
    return false

/-- Replace every proof subterm by `proofMarker`. -/
partial def erase (e : Expr) : M Expr := do
  if ← isProof e then return proofMarker
  match e with
  | .app .. =>
    let f' ← erase e.getAppFn
    let args' ← e.getAppArgs.mapM erase
    return mkAppN f' args'
  | .lam n d b bi =>
    let d' ← erase d
    let x ← mkLocal d
    let b' ← erase (b.instantiate1 x)
    return .lam n d' (b'.abstract #[x]) bi
  | .forallE n d b bi =>
    let d' ← erase d
    let x ← mkLocal d
    let b' ← erase (b.instantiate1 x)
    return .forallE n d' (b'.abstract #[x]) bi
  | .letE n t v b nd =>
    let t' ← erase t
    let v' ← erase v
    let x ← mkLocal t (some v)
    let b' ← erase (b.instantiate1 x)
    return .letE n t' v' (b'.abstract #[x]) nd
  | .proj s i st => return .proj s i (← erase st)
  | .mdata _ b => erase b
  | _ => return e

/-- Erase the proofs in a closed definition body. -/
def eraseBody (consts : Std.HashMap Name ConstantInfo) (body : Expr) : Expr :=
  match ((erase body).run { consts }).run {} with
  | .ok (e, _) => e
  | .error _ => body

end LeanBlame.Erase
