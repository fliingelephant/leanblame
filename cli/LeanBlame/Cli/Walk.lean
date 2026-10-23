/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
/-
Adapted for LeanBlame from comparator's `Comparator/Compare.lean` and
`Comparator/Util.lean` (https://github.com/leanprover/comparator, commit
865edc1). The licence text is in `cli/LICENSES/Apache-2.0.txt`.

Changes: the worklist loop is kept, but it walks one export instead of
comparing a challenge with a solution. It seeds from the boundary list, cuts at
tagged declarations, skips proofs (theorem values, and proof subterms erased
from definition bodies), and hashes every constant it reaches
(docs/03-trust-model.md, "The hash, precisely"). Cycles are found with
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
def kindOf : ConstantInfo → String
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .recInfo _ => "rec"

/-- One hashed constant. -/
structure Node where
  fields : Canon.Fields
  informal : Option String
  /-- Direct hash dependencies, sorted by printed name. -/
  deps : Array Name
  core : String
  own : String
  /-- Tagged declarations only. -/
  spec : Option String
  claim : String := ""
  deriving Inhabited

/-- Every constant reached from the boundary list, hashed. -/
structure Hashed where
  nodes : Std.HashMap Name Node
  tagged : Std.HashSet Name
  /-- Boundary-list names, in list order. -/
  boundary : Array Name

def Hashed.isTagged (h : Hashed) (n : Name) : Bool := h.tagged.contains n

def sortNames (xs : Array Name) : Array Name :=
  (xs.map fun n => (n.toString, n)).qsort (fun a b => a.1 < b.1) |>.map (·.2)

def dedupNames (xs : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out := #[]
  for x in xs do
    unless seen.contains x do
      seen := seen.insert x
      out := out.push x
  return out

namespace Hash

structure Context where
  exported : LeanExport.ExportedEnv
  /-- Tagged declarations with their informal text. -/
  tagged : Std.HashMap Name String

structure State where
  worklist : Array Name
  checked : Std.HashSet Name
  nodes : Std.HashMap Name Node := {}

/-- One `Meta` state for the whole export, so its caches serve every constant. -/
abbrev HashM := ReaderT Context <| StateRefT State MetaM

def addWorklist (n : Name) : HashM Unit := do
  if !(← get).checked.contains n then
    modify fun s => { s with worklist := s.worklist.push n }

/--
Hash one constant. Like comparator's `runForUsedConsts`, the dependencies are the constants
in the type and the value, plus constructors for inductives and the inductive for constructors;
unlike it, a theorem's value, the value of an `opaque` or `partial` definition, proof subterms
of definition bodies and recursor rules are skipped.
-/
def mkNode (info : ConstantInfo) : HashM Node := do
  let ctx ← read
  let informal := ctx.tagged[info.name]?
  if info.isUnsafe then
    throwError s!"'{info.name}' is unsafe: unsafe declarations cannot be tagged or hashed"
  let ups := info.levelParams
  let typeHash := Canon.exprHash ups info.type
  let mut deps := info.type.getUsedConstants
  let mut bodyHash : Option String := none
  let mut safety := "safe"
  match info with
  | .defnInfo d =>
    match d.safety with
    | .safe =>
      let body ← Erase.eraseBody d.value
      bodyHash := some (Canon.exprHash ups body)
      deps := deps ++ body.getUsedConstants
    | .partial => safety := "partial"
    | .unsafe => safety := "unsafe"
  | .opaqueInfo _ => safety := "opaque"
  | .inductInfo iv =>
    bodyHash := some <| Canon.hashFields "leanblame.inductive.1"
      ([toString iv.numParams, toString iv.numIndices] ++
        iv.ctors.map (Canon.name "" ·) ++ ["all"] ++ iv.all.map (Canon.name "" ·))
    deps := deps ++ iv.ctors.toArray ++ iv.all.toArray
  | .ctorInfo cv => deps := deps.push cv.induct
  | _ => pure ()
  let directDeps := sortNames (dedupNames (deps.filter (· != info.name)))
  let fields : Canon.Fields := {
    kind := kindOf info, name := info.name, uparams := ups.length, typeHash, bodyHash, safety }
  return {
    fields, informal, deps := directDeps
    core := Canon.core fields, own := Canon.own fields informal
    spec := informal.map (Canon.spec fields ·) }

/-- comparator's worklist loop, cut at tagged declarations (each is a seed of its own). -/
partial def loop : HashM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  if (← get).checked.contains target then
    loop
  else
    let some info := (← read).exported.constMap[target]?
      | throwError s!"Const not found in export '{target}'"
    let node ← mkNode info
    for d in node.deps do
      unless (← read).tagged.contains d do addWorklist d
    modify fun s => { s with checked := s.checked.insert target, nodes := s.nodes.insert target node }
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
    -- Frames: (vertex, index of the next successor to look at).
    let mut frames : Array (Name × Nat) := #[(root, 0)]
    st := { st with idx := st.idx.insert root st.index, low := st.low.insert root st.index,
                    index := st.index + 1, stack := st.stack.push root,
                    onStack := st.onStack.insert root }
    while h : frames.size > 0 do
      let (v, i) := frames[frames.size - 1]
      let ss := succ v
      if hi : i < ss.size then
        frames := frames.set! (frames.size - 1) (v, i + 1)
        let w := ss[i]
        if !st.idx.contains w then
          st := { st with idx := st.idx.insert w st.index, low := st.low.insert w st.index,
                          index := st.index + 1, stack := st.stack.push w,
                          onStack := st.onStack.insert w }
          frames := frames.push (w, 0)
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
          let (u, _) := frames[frames.size - 1]
          st := { st with low := st.low.insert u (min st.low[u]! st.low[v]!) }
  return st.sccs

/-- Hash every constant reachable from the boundary list of `exported`. -/
def hashExport (exported : LeanExport.ExportedEnv) (boundary : BoundaryList) : IO Hashed := do
  -- Boundary names are strings; map them to the export's constants.
  let byString : Std.HashMap String Name :=
    exported.constMap.fold (init := {}) fun m n _ => m.insert n.toString n
  let mut tagged : Std.HashMap Name String := {}
  let mut order : Array Name := #[]
  for d in boundary.declarations do
    let some n := byString[d.name]?
      | fail s!"'{d.name}' is on the boundary list but not in the export"
    tagged := tagged.insert n (strTrim d.informal)
    order := order.push n
  let ctx : Hash.Context := { exported, tagged }
  let env ← Load.environmentOfExport exported
  let (((), st), _) ← ((Hash.loop.run ctx).run { worklist := order.reverse, checked := {} }).toIO
    { fileName := "", fileMap := default, maxHeartbeats := 0 } { env }
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
      let external := sortNames <| dedupNames <|
        members.foldl (init := #[]) fun acc m => acc ++ (nodes[m]!.deps.filter (!memberSet.contains ·))
      let entries ← external.toList.mapM (entry nodes)
      let g := Canon.group owns entries
      for m in members do
        let node := nodes[m]!
        nodes := nodes.insert m { node with claim := Canon.member g m }
  let taggedSet : Std.HashSet Name := order.foldl (·.insert ·) {}
  return { nodes, tagged := taggedSet, boundary := order }

/--
The closure under `x`: the tagged declarations where the walk stops (the cut), and the untagged
constants passed through. `x` itself is in neither.
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
  return (sortNames cut.toArray, sortNames untagged.toArray)

/--
Why `claim(x)` differs between `old` and `new` (docs/03, "Why a hash moved"). Collects every
mismatch instead of stopping at the first:
* `own-text`: the informal text of `x`;
* `own-body`: kind, name, universe parameters, type, body or safety of `x`;
* `dep-spec`: tagged dependencies at the cut, in both closures, whose spec differs;
* `cut-moved`: dependencies in both closures that gained or lost their tag;
* `untagged`: untagged constants in both closures whose own hash differs.
Dependencies that appear or disappear are explained by the change of whatever references them.
-/
def changes (old new : Hashed) (x : Name) : Array Change := Id.run do
  let some n := new.nodes[x]? | return #[]
  let some o := old.nodes[x]? | return #[{ cause := "own-body", names := #[x.toString] }]
  let mut out : Array Change := #[]
  if o.informal != n.informal then out := out.push { cause := "own-text", names := #[x.toString] }
  if o.core != n.core then out := out.push { cause := "own-body", names := #[x.toString] }
  let (cut0, unt0) := closureOf old x
  let (cut1, unt1) := closureOf new x
  let cut0s : Std.HashSet Name := cut0.foldl (·.insert ·) {}
  let unt0s : Std.HashSet Name := unt0.foldl (·.insert ·) {}
  let depSpec := cut1.filter fun d => cut0s.contains d &&
    (old.nodes[d]?.bind (·.spec)) != (new.nodes[d]?.bind (·.spec))
  let cutMoved := sortNames ((cut1.filter unt0s.contains) ++ (unt1.filter cut0s.contains))
  let untagged := unt1.filter fun u => unt0s.contains u &&
    (old.nodes[u]?.map (·.own)) != (new.nodes[u]?.map (·.own))
  let names (xs : Array Name) := xs.map (·.toString)
  unless depSpec.isEmpty do out := out.push { cause := "dep-spec", names := names depSpec }
  unless cutMoved.isEmpty do out := out.push { cause := "cut-moved", names := names cutMoved }
  unless untagged.isEmpty do out := out.push { cause := "untagged", names := names untagged }
  return out

end LeanBlame.Walk
