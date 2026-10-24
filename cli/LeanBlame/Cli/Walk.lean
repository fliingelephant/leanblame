/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
/-
Adapted for LeanBlame from comparator's closure walk, which ships in the Lean toolchain as
`Lake/Check/Compare.lean` and `Lake/Check/Util.lean` (`runForUsedConsts`). The licence text is in
`cli/LICENSES/Apache-2.0.txt`.

Changes: the worklist loop is kept, but it walks one export instead of
comparing a challenge with a solution. It seeds from the boundary list, cuts at
tagged declarations, skips proofs (theorem values, and proof subterms erased
from types and definition bodies), and hashes every constant it reaches
(docs/design/03-trust-model.md, "The hash, precisely"). Cycles are found with
Tarjan's algorithm and hashed as groups. Instead of stopping at the first
mismatch, `changes` collects every difference between two hashed exports under
a declaration and charges it to a cause.
-/
import LeanExport.Parse
import Lean.Util.FoldConsts
import LeanBlame.Cli.Canon
import LeanBlame.Cli.Load
import LeanBlame.Cli.Schema

namespace LeanBlame.Walk

open Lean

/-- The export kind of a constant, as the boundary list and the hash name it. -/
def kindOf : ConstantInfo → Kind
  | .defnInfo _ => .«def»
  | .thmInfo _ => .«theorem»
  | .axiomInfo _ => .«axiom»
  | .inductInfo _ => .«inductive»
  | .ctorInfo _ => .ctor
  | .opaqueInfo _ => .«opaque»
  | .quotInfo _ => .quot
  | .recInfo _ => .recursor

/-- One hashed constant. -/
structure Node where
  fields : Canon.Fields
  informal : Option String
  /-- Direct hash dependencies, sorted by printed name. -/
  deps : Array Name
  own : String
  /-- Tagged declarations only. -/
  spec : Option String
  claim : String := ""
  deriving Inhabited

/-- Every constant reached from the boundary list, hashed. -/
structure Hashed where
  nodes : Std.HashMap Name Node
  /-- The axioms the type and value of each tagged declaration rest on, sorted
  (`Lean.collectAxioms`). A function of the export alone. -/
  axioms : Std.HashMap Name (Array Name)
  /-- The boundary list it was hashed with. -/
  boundary : BoundaryList
  /-- The boundary list's declarations with their constants, in list order. -/
  declarations : Array (Name × BoundaryDecl)

/-- Tagged nodes are the ones with informal text. -/
def Hashed.isTagged (h : Hashed) (n : Name) : Bool := (h.nodes[n]?.bind (·.informal)).isSome

def sortNames (xs : Array Name) : Array Name :=
  (xs.map fun n => (n.toString, n)).qsort (fun a b => a.1 < b.1) |>.map (·.2)

namespace Hash

structure Context where
  exported : LeanExport.ExportedEnv
  /-- Tagged declarations with their informal text. -/
  tagged : Std.HashMap Name String

structure State where
  worklist : Array Name
  nodes : Std.HashMap Name Node := {}

/-- One `Meta` state for the whole export, so its caches serve every constant. -/
abbrev HashM := ReaderT Context <| StateRefT State MetaM

def addWorklist (n : Name) : HashM Unit := do
  if !(← get).nodes.contains n then
    modify fun s => { s with worklist := s.worklist.push n }

/--
Hash one constant. Like comparator's `runForUsedConsts`, the dependencies are the constants
in the type and the value, plus constructors for inductives and the inductive for constructors;
unlike it, a theorem's value, the value of an `opaque` or `partial` definition, proof subterms
of types and definition bodies, and recursor rules are skipped.
-/
def mkNode (info : ConstantInfo) : HashM Node := do
  let ctx ← read
  let informal := ctx.tagged[info.name]?
  if info.isUnsafe then
    throwError s!"'{info.name}' is unsafe: unsafe declarations cannot be tagged or hashed"
  let ups := info.levelParams
  let type ← Erase.eraseProofs info.type
  let typeHash := Canon.exprHash ups type
  let mut deps := type.getUsedConstants
  let mut bodyHash : Option String := none
  let mut safety : Safety := .safe
  match info with
  | .defnInfo d =>
    match d.safety with
    | .safe =>
      let body ← Erase.eraseProofs d.value
      bodyHash := some (Canon.exprHash ups body)
      deps := deps ++ body.getUsedConstants
    | _ => safety := .«partial»
  | .opaqueInfo _ => safety := .«opaque»
  | .inductInfo iv =>
    bodyHash := some <| Canon.hashFields "leanblame.inductive.1"
      ([toString iv.numParams, toString iv.numIndices] ++
        iv.ctors.map (Canon.name "" ·) ++ ["all"] ++ iv.all.map (Canon.name "" ·))
    deps := deps ++ iv.ctors.toArray ++ iv.all.toArray
  | .ctorInfo cv => deps := deps.push cv.induct
  | _ => pure ()
  let directDeps := (sortNames (deps.filter (· != info.name))).eraseReps
  let fields : Canon.Fields := {
    kind := kindOf info, name := info.name, uparams := ups.length, typeHash, bodyHash, safety }
  return {
    fields, informal, deps := directDeps
    own := Canon.own fields informal
    spec := informal.map (Canon.spec fields ·) }

/-- comparator's worklist loop, cut at tagged declarations (each is a seed of its own). -/
partial def loop : HashM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  if (← get).nodes.contains target then
    loop
  else
    let some info := (← read).exported.constMap[target]?
      | throwError s!"Const not found in export '{target}'"
    let node ← mkNode info
    for d in node.deps do
      unless (← read).tagged.contains d do addWorklist d
    modify fun s => { s with nodes := s.nodes.insert target node }
    loop

end Hash

/-! Cycles: Tarjan's strongly connected components over edges to untagged dependencies. -/

structure TState where
  index : Nat := 0
  idx : Std.HashMap Name Nat := {}
  low : Std.HashMap Name Nat := {}
  stack : Array Name := #[]
  onStack : Std.HashSet Name := {}
  sccs : Array (Array Name) := #[]

/-- Components in Tarjan's emission order: each after every component it reaches. -/
def tarjan (roots : Array Name) (succ : Name → Array Name) : Array (Array Name) := Id.run do
  let mut st : TState := {}
  for root in roots do
    if st.idx.contains root then continue
    -- Frames: (vertex, its successors, index of the next one to look at).
    let mut frames : Array (Name × Array Name × Nat) := #[(root, succ root, 0)]
    st := { st with idx := st.idx.insert root st.index, low := st.low.insert root st.index,
                    index := st.index + 1, stack := st.stack.push root,
                    onStack := st.onStack.insert root }
    while h : frames.size > 0 do
      let (v, ss, i) := frames[frames.size - 1]
      if hi : i < ss.size then
        frames := frames.set! (frames.size - 1) (v, ss, i + 1)
        let w := ss[i]
        if !st.idx.contains w then
          st := { st with idx := st.idx.insert w st.index, low := st.low.insert w st.index,
                          index := st.index + 1, stack := st.stack.push w,
                          onStack := st.onStack.insert w }
          frames := frames.push (w, succ w, 0)
        else if st.onStack.contains w then
          st := { st with low := st.low.insert v (min st.low[v]! st.idx[w]!) }
      else
        frames := frames.pop
        if st.low[v]! == st.idx[v]! then
          let mut comp := #[]
          repeat
            let w := st.stack.back!
            st := { st with stack := st.stack.pop, onStack := st.onStack.erase w }
            comp := comp.push w
            if w == v then break
          st := { st with sccs := st.sccs.push comp }
        if h' : frames.size > 0 then
          let (u, _, _) := frames[frames.size - 1]
          st := { st with low := st.low.insert u (min st.low[u]! st.low[v]!) }
  return st.sccs

/-- The axioms every Lean library may rest on (docs/design/07). -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/--
The axioms each of `roots` rests on, sorted: exactly what `Lean.collectAxioms` returns in the
environment `Load` builds (constants in types and values, and the constructors of inductives;
unsafe and partial constants are not there), but in one pass over the components of the constant
graph instead of one walk per root.
-/
def axiomsOf (find? : Name → Option ConstantInfo) (roots : Array Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let info? (n : Name) := (find? n).filter fun ci => !ci.isUnsafe && !ci.isPartial
  let uses : ConstantInfo → Array Name
    | .quotInfo _ => #[]
    | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
    | ci => ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  -- The reachable graph, each constant's edges computed once.
  let mut succs : Std.HashMap Name (Array Name) := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if succs.contains n then continue
    let ss := ((info? n).map uses).getD #[]
    succs := succs.insert n ss
    todo := todo ++ ss
  -- Components come after every component they reach.
  let mut axioms : Std.HashMap Name (Array Name) := {}
  for comp in tarjan roots (succs.getD · #[]) do
    let mut set : NameSet := {}
    for n in comp do
      if info? n matches some (.axiomInfo _) then set := set.insert n
      for d in succs.getD n #[] do
        set := (axioms.getD d #[]).foldl (·.insert ·) set
    let sorted := set.toArray.qsort Name.lt
    for n in comp do axioms := axioms.insert n sorted
  return roots.foldl (init := {}) fun m n => m.insert n (axioms.getD n #[])

/-- Hash every constant reachable from the boundary list of `exported`. -/
def hashExport (exported : LeanExport.ExportedEnv) (boundary : BoundaryList) : IO Hashed := do
  let mut tagged : Std.HashMap Name String := {}
  let mut declarations : Array (Name × BoundaryDecl) := #[]
  for d in boundary.declarations do
    let some n := (constName? d.name).filter exported.constMap.contains
      | fail s!"'{d.name}' is on the boundary list but not in the export"
    tagged := tagged.insert n (strTrim d.informal)
    declarations := declarations.push (n, d)
  let order := declarations.map (·.1)
  let ctx : Hash.Context := { exported, tagged }
  let env ← Load.environmentOfExport exported
  let (((), st), _) ← ((Hash.loop.run ctx).run { worklist := order.reverse }).toIO
    { fileName := "", fileMap := default, maxHeartbeats := 0 } { env }
  let axioms := axiomsOf (exported.constMap[·]?) order
  let mut nodes := st.nodes
  let isTagged (n : Name) := tagged.contains n
  let succ (n : Name) : Array Name :=
    (nodes[n]?.map (·.deps) |>.getD #[]).filter fun d => !isTagged d && nodes.contains d
  let roots := sortNames (nodes.fold (init := #[]) fun acc n _ => acc.push n)
  let comps := tarjan roots succ
  let entry (nodes : Std.HashMap Name Node) (d : Name) : IO Canon.DepEntry := do
    let some dn := nodes[d]? | fail s!"dependency '{d}' was not hashed"
    if isTagged d then
      let some s := dn.spec | fail s!"tagged '{d}' has no spec"
      return .spec s
    else
      if dn.claim.isEmpty then fail s!"internal: claim of '{d}' needed before it was computed"
      return .full dn.claim
  for comp in comps do
    if h : comp.size = 1 then
      let n := comp[0]
      let node := nodes[n]!
      let entries ← node.deps.toList.mapM (entry nodes)
      nodes := nodes.insert n { node with claim := Canon.claim node.own entries }
    else
      let members := sortNames comp
      let memberSet : Std.HashSet Name := members.foldl (·.insert ·) {}
      let owns := members.toList.map fun m => nodes[m]!.own
      let external := Array.eraseReps <| sortNames <|
        members.foldl (init := #[]) fun acc m => acc ++ (nodes[m]!.deps.filter (!memberSet.contains ·))
      let entries ← external.toList.mapM (entry nodes)
      let g := Canon.group owns entries
      for m in members do
        let node := nodes[m]!
        nodes := nodes.insert m { node with claim := Canon.member g m }
  return { nodes, axioms, boundary, declarations }

/--
The closure under `x`: the tagged declarations where the walk stops (the cut, sorted), and the
untagged constants passed through (unsorted). `x` itself is in neither.
-/
def closureOf (h : Hashed) (x : Name) : Array Name × Array Name := Id.run do
  let mut cut : Std.HashSet Name := {}
  let mut untagged : Std.HashSet Name := {}
  let mut worklist := (h.nodes[x]?.map (·.deps)).getD #[]
  let mut checked : Std.HashSet Name := {}
  while h' : worklist.size > 0 do
    let d := worklist[worklist.size - 1]
    worklist := worklist.pop
    if checked.contains d || d == x then continue
    checked := checked.insert d
    if h.isTagged d then
      cut := cut.insert d
    else
      untagged := untagged.insert d
      worklist := worklist ++ ((h.nodes[d]?.map (·.deps)).getD #[])
  return (sortNames cut.toArray, untagged.toArray)

/--
Why `claim(x)` differs between `old` and `new` (docs/design/03, "Why a hash moved"). Collects every
mismatch instead of stopping at the first:
* `own-text`: the informal text of `x`;
* `own-body`: kind, name, universe parameters, type, body or safety of `x`;
* `dep-spec`: tagged dependencies at the cut, in both closures, whose spec differs;
* `cut-moved`: dependencies in both closures that gained or lost their tag;
* `untagged`: untagged constants in both closures whose own hash differs.
Dependencies that appear or disappear are explained by the change of whatever references them.
-/
def changes (old new : Hashed) (x : Name) (closure : Array Name × Array Name := closureOf new x) :
    Array Change := Id.run do
  let some n := new.nodes[x]? | return #[]
  let some o := old.nodes[x]? | return #[{ cause := .ownBody, names := #[x.toString] }]
  let mut out : Array Change := #[]
  if o.informal != n.informal then out := out.push { cause := .ownText, names := #[x.toString] }
  if o.fields != n.fields then out := out.push { cause := .ownBody, names := #[x.toString] }
  let (cut0, unt0) := closureOf old x
  let (cut1, unt1) := closure
  let cut0s : Std.HashSet Name := cut0.foldl (·.insert ·) {}
  let unt0s : Std.HashSet Name := unt0.foldl (·.insert ·) {}
  let depSpec := cut1.filter fun d => cut0s.contains d &&
    (old.nodes[d]?.bind (·.spec)) != (new.nodes[d]?.bind (·.spec))
  let cutMoved := sortNames ((cut1.filter unt0s.contains) ++ (unt1.filter cut0s.contains))
  let untagged := sortNames <| unt1.filter fun u => unt0s.contains u &&
    (old.nodes[u]?.map (·.own)) != (new.nodes[u]?.map (·.own))
  let names (xs : Array Name) := xs.map (·.toString)
  unless depSpec.isEmpty do out := out.push { cause := .depSpec, names := names depSpec }
  unless cutMoved.isEmpty do out := out.push { cause := .cutMoved, names := names cutMoved }
  unless untagged.isEmpty do out := out.push { cause := .untagged, names := names untagged }
  return out

end LeanBlame.Walk
