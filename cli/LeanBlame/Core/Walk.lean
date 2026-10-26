/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
/-
Adapted for LeanBlame from comparator's closure walk, which ships in the Lean toolchain as
`Lake/Check/Compare.lean`. The licence text is in `cli/LICENSES/Apache-2.0.txt`.

Changes: the worklist loop is kept, but it walks one export, which a frontend serves as a
`Core.Source` (docs/design/15-generic-core.md), instead of comparing a challenge with a solution.
It seeds from the boundary list, cuts at tagged declarations, and hashes every declaration it
reaches from the facts the frontend reports, proofs already left out (docs/design/03-trust-model.md,
"The hash, precisely"). Cycles are found with Tarjan's algorithm and hashed as groups. Instead of
stopping at the first mismatch, `changes` collects every difference between two hashed exports under
a declaration and charges it to a cause. Declarations are keyed by their printed name.
-/
import LeanBlame.Core.Hash

namespace LeanBlame.Walk

/-! Cycles: Tarjan's strongly connected components over edges to untagged dependencies. -/

structure TState (α : Type) [BEq α] [Hashable α] where
  index : Nat := 0
  idx : Std.HashMap α Nat := {}
  low : Std.HashMap α Nat := {}
  stack : Array α := #[]
  onStack : Std.HashSet α := {}
  sccs : Array (Array α) := #[]

/-- Components in Tarjan's emission order: each after every component it reaches. -/
def tarjan [BEq α] [Hashable α] [Inhabited α] (roots : Array α) (succ : α → Array α) :
    Array (Array α) := Id.run do
  let mut st : TState α := {}
  for root in roots do
    if st.idx.contains root then continue
    -- Frames: (vertex, its successors, index of the next one to look at).
    let mut frames : Array (α × Array α × Nat) := #[(root, succ root, 0)]
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

/--
The assumptions each of `roots` rests on, sorted: the declarations `Source.isAssumed` names among
those reached through `Source.uses` (statements and bodies, proofs included), in one pass over the
components of the graph instead of one walk per root.
-/
def axiomsOf (src : Core.Source) (roots : Array String) : Std.HashMap String (Array String) :=
    Id.run do
  -- The reachable graph, each declaration's edges computed once.
  let mut succs : Std.HashMap String (Array String) := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if succs.contains n then continue
    let ss := src.uses n
    succs := succs.insert n ss
    todo := todo ++ ss
  -- Components come after every component they reach.
  let mut axioms : Std.HashMap String (Array String) := {}
  for comp in tarjan roots (succs.getD · #[]) do
    let mut set : Std.HashSet String := {}
    for n in comp do
      if src.isAssumed n then set := set.insert n
      for d in succs.getD n #[] do
        set := (axioms.getD d #[]).foldl (·.insert ·) set
    let sorted := Core.sortNames set.toArray
    for n in comp do axioms := axioms.insert n sorted
  return roots.foldl (init := {}) fun m n => m.insert n (axioms.getD n #[])

/-- Hash every declaration reachable from the boundary list in the export `src` serves; the export
and the boundary list are stored as `exportHash` and `boundaryHash`. The graph keeps what the other
commands need from `backend`. -/
def hashExport (backend : Core.Backend) (src : Core.Source) (boundary : BoundaryList)
    (exportHash boundaryHash : String) : IO Core.Hashed := do
  -- Tagged declarations with their informal text.
  let tagged : Std.HashMap String String :=
    boundary.declarations.foldl (init := {}) fun m d => m.insert d.name d.informal
  let isTagged := tagged.contains
  let order := boundary.declarations.map (·.name)
  -- comparator's worklist loop, cut at tagged declarations (each is a seed of its own).
  let mut nodes : Std.HashMap String Core.Node := {}
  let mut worklist := order.reverse
  while h : worklist.size > 0 do
    let target := worklist[worklist.size - 1]
    worklist := worklist.pop
    if nodes.contains target then continue
    let d ← src.decl target
    for dep in d.deps do
      unless isTagged dep || nodes.contains dep do worklist := worklist.push dep
    let informal := tagged[target]?
    nodes := nodes.insert target
      { decl := d, informal, own := Hash.own d informal, spec := informal.map (Hash.spec d ·)
        claim := "" }
  let axioms := axiomsOf src order
  let succ (n : String) : Array String :=
    (nodes[n]?.map (·.decl.deps) |>.getD #[]).filter fun d => !isTagged d && nodes.contains d
  let roots := Core.sortNames (nodes.fold (init := #[]) fun acc n _ => acc.push n)
  let comps := tarjan roots succ
  let entry (nodes : Std.HashMap String Core.Node) (d : String) : IO Hash.DepEntry := do
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
      let entries ← node.decl.deps.toList.mapM (entry nodes)
      nodes := nodes.insert n { node with claim := Hash.claim node.own entries }
    else
      let members := Core.sortNames comp
      let memberSet : Std.HashSet String := members.foldl (·.insert ·) {}
      let owns := members.toList.map fun m => nodes[m]!.own
      let external := Array.eraseReps <| Core.sortNames <|
        members.foldl (init := #[]) fun acc m =>
          acc ++ (nodes[m]!.decl.deps.filter (!memberSet.contains ·))
      let entries ← external.toList.mapM (entry nodes)
      let g := Hash.group owns entries
      for m in members do
        let node := nodes[m]!
        nodes := nodes.insert m { node with claim := Hash.member g m }
  return { nodes, axioms, boundary, exportHash, boundaryHash, standard := backend.standard
           incomplete := backend.incomplete, checker := backend.checker }

/--
The closure under `x`: the tagged declarations where the walk stops (the cut, sorted), and the
untagged declarations passed through (unsorted). `x` itself is in neither.
-/
def closureOf (h : Core.Hashed) (x : String) : Array String × Array String := Id.run do
  let mut cut : Std.HashSet String := {}
  let mut untagged : Std.HashSet String := {}
  let mut worklist := (h.nodes[x]?.map (·.decl.deps)).getD #[]
  let mut checked : Std.HashSet String := {}
  while h' : worklist.size > 0 do
    let d := worklist[worklist.size - 1]
    worklist := worklist.pop
    if checked.contains d || d == x then continue
    checked := checked.insert d
    if h.isTagged d then
      cut := cut.insert d
    else
      untagged := untagged.insert d
      worklist := worklist ++ ((h.nodes[d]?.map (·.decl.deps)).getD #[])
  return (Core.sortNames cut.toArray, untagged.toArray)

/--
Why the claim of declaration `x` of `new`, named `oldName` in `old`, differs between them
(docs/design/03, "Why a hash moved"). Collects every mismatch instead of stopping at the first:
* `own-text`: the informal text of `x`;
* `own-body`: kind, role, name, universe parameters, type or body of `x`;
* `dep-spec`: tagged dependencies at the cut, in both closures, whose spec differs;
* `cut-moved`: dependencies in both closures that gained or lost their tag;
* `untagged`: untagged declarations in both closures whose own hash differs.
Dependencies that appear or disappear are explained by the change of whatever references them. An
error when either graph lacks `x`.
-/
def changes (old new : Core.Hashed) (oldName x : String)
    (closure : Array String × Array String := closureOf new x) : Except String (Array Change) := do
  let some n := new.nodes[x]? | throw s!"{x} is not in the graph of export {new.exportHash}"
  let some o := old.nodes[oldName]? | throw s!"{oldName} is not in the graph of export {old.exportHash}"
  let mut out : Array Change := #[]
  if o.informal != n.informal then out := out.push { cause := .ownText, names := #[x] }
  -- What enters `own` besides the informal text.
  let fields (d : Core.Decl) := (d.kind, d.role, d.name, d.uparams, d.typeHash, d.bodyHash)
  if fields o.decl != fields n.decl then out := out.push { cause := .ownBody, names := #[x] }
  let (cut0, unt0) := closureOf old oldName
  let (cut1, unt1) := closure
  let cut0s : Std.HashSet String := cut0.foldl (·.insert ·) {}
  let unt0s : Std.HashSet String := unt0.foldl (·.insert ·) {}
  let depSpec := cut1.filter fun d => cut0s.contains d &&
    (old.nodes[d]?.bind (·.spec)) != (new.nodes[d]?.bind (·.spec))
  let cutMoved := Core.sortNames ((cut1.filter unt0s.contains) ++ (unt1.filter cut0s.contains))
  let untagged := Core.sortNames <| unt1.filter fun u => unt0s.contains u &&
    (old.nodes[u]?.map (·.own)) != (new.nodes[u]?.map (·.own))
  unless depSpec.isEmpty do out := out.push { cause := .depSpec, names := depSpec }
  unless cutMoved.isEmpty do out := out.push { cause := .cutMoved, names := cutMoved }
  unless untagged.isEmpty do out := out.push { cause := .untagged, names := untagged }
  return out

end LeanBlame.Walk
