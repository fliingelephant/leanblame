/-
`leanblame equiv [NAME...]` (docs/06-versioning.md, "`equiv`").

Mechanical: no build, no tactics. For each tagged declaration X that is `outdated` with `untagged`
as the only cause (the named ones, else all), compared with X's last live approval:
1. Old meaning. From the export that approval names, what X's old statement (and value, for a
   definition) uses that is not shared goes under `Old.`, references renamed, into the environment
   of the current export, and so does a definition X itself; the kernel checks each. Not shared: an
   untagged hashed constant whose claim changed, or a constant used only in proofs (so not hashed)
   that the current export lacks or states differently. Tagged constants are always shared.
2. Goals. For X and for each changed definition C still present with the same type text, one kernel
   call decides whether old and new are definitionally equal:
   `theorem LeanBlame.Equiv.C : Old.C = C := Eq.refl C`, or for a theorem X
   `<old statement> ↔ <new statement>`, proved by the identity both ways.
3. `lake comparator` judges the accepted theorems: the solution export carries them, the challenge
   export the same statements proved by `sorryAx`.
4. For each X whose own theorem was accepted, an evidence file (`Store.evidencePath`) names the
   solution export: `status` flags X `equiv-proven`, `sign` puts the hash in the record.
What is left is for a human to read: equiv prints the root causes, with the old and new values of
each changed definition that is not definitionally equal.
-/
import LeanBlame.Cli.Export
import LeanBlame.Cli.Status

namespace LeanBlame.Equiv

open Lean

def oldName (n : Name) : Name := `Old ++ n

def thmName (n : Name) : Name := `LeanBlame.Equiv ++ n

/-- `e` with references to the constants of `dup`, and projections out of them, renamed to `Old.`. -/
partial def renameExpr (dup : NameSet) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => if dup.contains n then some (.const (oldName n) us) else none
    | .proj s i b => if dup.contains s then some (.proj (oldName s) i (renameExpr dup b)) else none
    | _ => none

/-- An old constant as the `Old.` constant: its name and references to `dup` renamed. -/
def renameConst (dup : NameSet) (ci : ConstantInfo) : ConstantInfo :=
  let e := renameExpr dup
  let n (x : Name) := if dup.contains x || x == ci.name then oldName x else x
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

/-- Whether old constant `o`, with `dup` renamed, is the current constant `n`: the same type, and
for anything but a theorem (proof irrelevance) the same value. -/
def sameDecl (dup : NameSet) (o n : ConstantInfo) : Bool :=
  let e (x : Expr) := (renameExpr dup x).instantiateLevelParams o.levelParams (n.levelParams.map .param)
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

/-- `e` printed with notation (field notation too) off, as the sign server shows types (docs/06). -/
def pp (env : Kernel.Environment) (e : Expr) : IO String := do
  try return toString (← runMeta env (PrettyPrinter.ppExpr e)) catch _ => return toString e

/-- The statement that old and current `c` mean the same, with its proof: `Old.c = c` for a safe
definition whose type text and universe parameters are unchanged, `<old type> ↔ <type>` for a
theorem; or why there is none. -/
def goal (env : Kernel.Environment) (dup : NameSet) (c : Name) (o n : ConstantInfo)
    (oldNode newNode : Walk.Node) : IO (Except String (Expr × Expr)) := do
  let us := n.levelParams.map Level.param
  unless o.levelParams.length == us.length do return .error "its universe parameters changed"
  match o, n with
  | .defnInfo ov, .defnInfo nv =>
    unless ov.safety == .safe && nv.safety == .safe do return .error "it is not a safe definition"
    unless oldNode.fields.typeHash == newNode.fields.typeHash do return .error "its type changed"
    let u ← runMeta env (Meta.getLevel n.type)
    return .ok (mkApp3 (.const ``Eq [u]) n.type (.const (oldName c) us) (.const c us),
                mkApp2 (.const ``Eq.refl [u]) n.type (.const c us))
  | .thmInfo _, .thmInfo _ =>
    let a := (renameExpr dup o.type).instantiateLevelParams o.levelParams us
    let b := n.type
    return .ok (mkApp2 (.const ``Iff []) a b,
                mkApp4 (.const ``Iff.intro []) a b (.lam `h a (.bvar 0) .default) (.lam `h b (.bvar 0) .default))
  | _, _ => return .error s!"no goal for a changed {Walk.kindOf n}"

/-- One eligible declaration: the approve record it is compared with and its current claim. -/
structure Target where
  name : Name
  record : String
  claim : String

/-- Whether `lake comparator` can sandbox here: Linux, with `bwrap` on PATH. -/
def canSandbox : IO Bool := do
  unless System.Platform.isLinux do return false
  ((← IO.getEnv "PATH").getD "").splitOn ":" |>.anyM fun d => (System.FilePath.mk d / "bwrap").pathExists

/--
Prove the targets that share one old export and boundary list (`old`, `oldExp`); returns those
proven, with the hashes of the challenge and solution exports.
-/
def proveGroup (root : System.FilePath) (base : Kernel.Environment) (new old : Walk.Hashed)
    (newExp oldExp : LeanExport.ExportedEnv) (targets : Array Target) :
    IO (Array Target × String × String) := do
  let oldCi (c : Name) := oldExp.constMap[c]?
  let isTarget (c : Name) := targets.any (·.name == c)
  -- What an old meaning uses: of a target theorem only its statement.
  let uses (c : Name) : Array Name := match oldCi c with
    | some ci => if isTarget c && ci matches .thmInfo _ then ci.type.getUsedConstants
      else ci.getUsedConstantsAsSet.toArray
    | none => #[]
  -- The constants to duplicate, until nothing is added.
  let needs (dup : NameSet) (r : Name) : Bool :=
    !old.isTagged r && match old.nodes[r]? with
    | some o => (new.nodes[r]?.map (·.claim)) != some o.claim
    | none => match oldCi r, newExp.constMap[r]? with
      | some o, some n => !sameDecl dup o n
      | some _, none => true
      | none, _ => false
  let seeds := targets.flatMap (uses ·.name)
  let mut dup : NameSet := {}
  repeat
    let size := dup.size
    for r in seeds ++ dup.toArray.flatMap uses do
      if !dup.contains r && needs dup r then dup := dup.insert r
    if dup.size == size then break
  -- `Old.` constants: the duplicated ones, and each target definition.
  let consts : Std.HashMap Name ConstantInfo :=
    (dup.toArray ++ targets.map (·.name)).foldl (init := {}) fun m c =>
      match oldCi c with
      | some ci => if isTarget c && !(ci matches .defnInfo _) then m else m.insert (oldName c) (renameConst dup ci)
      | none => m
  let succ (c : Name) := (uses c).filter dup.contains
  -- In dependency order: rebuild each component, then check its goals. `taint` holds, per constant,
  -- the failures at or below it that its goal may rest on.
  let mut env := base
  let mut broken : NameSet := {}
  let mut rebuiltNames : NameSet := {}
  let mut taint : Std.HashMap Name (Array Name) := {}
  let mut proved : Array (Name × List Name × Expr) := #[]
  for comp in Walk.tarjan (dup.toArray ++ targets.map (·.name)) succ do
    let deps := (comp.flatMap succ).filter (!comp.contains ·)
    let below := dedup (deps.flatMap (taint.getD · #[]))
    let names := NameSet.ofArray (comp.map oldName |>.filter consts.contains)
    let rebuilt ← if deps.any broken.contains then pure false else
      try
        env ← Load.addConstants env consts names true
        rebuiltNames := names.foldl (·.insert ·) rebuiltNames
        pure true
      catch e =>
        IO.eprintln s!"cannot rebuild {e}; a human reads"
        pure false
    for c in comp do
      unless rebuilt do
        broken := broken.insert c
        taint := taint.insert c (dedup (below.push c))
        continue
      let report (msg : String) : IO (Array Name) := do
        if below.isEmpty then IO.eprintln msg
        return if below.isEmpty then #[c] else below
      match oldCi c, newExp.constMap[c]?, old.nodes[c]?, new.nodes[c]? with
      | some o, some n, some oldNode, some newNode =>
        match ← goal env dup c o n oldNode newNode with
        | .error why => taint := taint.insert c (← report s!"{c}: {why}; a human reads")
        | .ok (stmt, proof) =>
          let decl : Declaration :=
            .thmDecl { name := thmName c, levelParams := n.levelParams, type := stmt, value := proof }
          match ← addChecked env decl with
          | .ok env' =>
            env := env'
            proved := proved.push (thmName c, n.levelParams, stmt)
            taint := taint.insert c #[]
          | .error msg =>
            let why ← if oldNode.own != newNode.own then
                pure s!"{c}: not definitionally equal; a human reads\n  old: {← pp env (o.value?.getD o.type)}\n  new: {← pp env (n.value?.getD n.type)}"
              else pure s!"{c}: not definitionally equal to its approved version ({msg}); a human reads"
            taint := taint.insert c (← report why)
      -- Used only in proofs, or gone: nothing to state.
      | _, _, _, _ => taint := taint.insert c below
  let proven := targets.filter fun t => proved.any (·.1 == thmName t.name)
  for t in targets do
    let causes := (taint.getD t.name #[]).filter (· != t.name)
    unless proven.any (·.name == t.name) || causes.isEmpty do
      IO.eprintln s!"{t.name}: not proven, because of {", ".intercalate (causes.toList.map toString)}; a human reads"
  if proven.isEmpty then return (#[], "", "")
  -- The challenge states the accepted theorems with `sorryAx` as proofs.
  unless newExp.constMap.contains ``sorryAx do
    fail "the current export lacks what `lake comparator` needs; run `leanblame export` again"
  let mut challenge ← Load.addConstants base consts rebuiltNames false
  for (name, levelParams, type) in proved do
    let value := mkApp2 (.const ``sorryAx [.zero]) type (.const ``Bool.false [])
    match challenge.addDeclWithoutChecking (.thmDecl { name, levelParams, type, value }) with
    | .ok e => challenge := e
    | .error ex => fail s!"{name}: {← (ex.toMessageData {}).toString}"
  let roots := proved.map (·.1) ++ Export.comparatorRoots.filter newExp.constMap.contains
  let put (env : Kernel.Environment) (tag : String) : IO String := do
    let tmp ← Store.tmpPath root tag
    Store.putFile root tmp (← Export.dumpToFile (.ofKernelEnv env) roots tmp)
  let solution ← put env "solution"
  let challengeHash ← put challenge "challenge"
  -- The generated proofs use no axiom: the statements' own axioms are permitted.
  let axioms := (Walk.axiomsOf (← Status.loadExported root solution) (proved.map (·.1))).fold
    (init := Walk.standardAxioms) fun acc _ as => acc ++ as
  let config := Json.mkObj [
    ("challenge_module", "Challenge"), ("solution_module", "Solution"),
    ("theorem_names", toJson (proved.map (·.1.toString))),
    ("permitted_axioms", toJson ((dedup axioms).map toString))]
  let configHash ← Store.putString root (jsonText config)
  let sandbox ← canSandbox
  unless sandbox do
    IO.eprintln "warning: no bwrap sandbox here: lake comparator runs with --inadvisably-no-sandbox (nothing is built; it reads two exports equiv wrote)"
  let path (h : String) := (Store.objectPath root h).toString
  runToStderr "lake" (#["comparator", "--config", path configHash, "--challenge-from-export",
      path challengeHash, "--solution-from-export", path solution] ++
      (if sandbox then #[] else #["--inadvisably-no-sandbox"])) root "`lake comparator`"
  return (proven, challengeHash, solution)

def run (root : System.FilePath) (names : Array String) : IO UInt32 := do
  let cfg ← Config.load root
  let (all, _) ← loadAllRecords root cfg
  let ledger := Ledger.build cfg all
  let decls := (← Status.compute root cfg ledger none).report.declarations
  for n in names do
    unless decls.any (·.1 == n) do fail s!"{n} is not on the boundary list"
  let cur ← Store.readCurrent root
  let memo : Status.Memo ← IO.mkRef {}
  let some new ← Status.hashed root memo cur.exportHash cur.boundary | unreachable!
  let nameOf : Std.HashMap String Name := new.declarations.foldl (init := {}) fun m (x, _) => m.insert x.toString x
  -- Eligible: outdated, and `untagged` the only cause.
  let mut targets : Array (Target × ApproveRecord) := #[]
  let mut left := 0
  for (n, d) in decls do
    unless names.isEmpty || names.contains n do continue
    if d.state == "outdated" && d.change.size == 1 && d.change[0]!.cause == "untagged" then
      let some (r, a, _) := (Status.liveApprovals ledger n).back? | continue
      targets := targets.push ({ name := nameOf[n]!, record := r.hash, claim := d.claim }, a)
    else if !names.isEmpty && d.state != "valid" then
      left := left + 1
      IO.eprintln (if d.state == "unsigned" then s!"{n}: unsigned: no approved meaning to compare with"
        else s!"{Status.textLine n d}\n{n}: no goal: a cause other than `untagged`; a human reads")
  if targets.isEmpty then
    if left == 0 then IO.println "equiv: no outdated declaration whose only cause is untagged"
    return if left == 0 then 0 else 1
  let newExp ← Status.loadExported root cur.exportHash
  let base := (← Load.environmentOfExport newExp).toKernelEnv
  -- One group per old export and boundary list.
  let groups := dedup (targets.map fun (_, a) => (a.exportHash, a.boundary))
  let mut proven := 0
  for (e, b) in groups do
    let some old ← Status.hashed root memo e b | unreachable!
    let group := (targets.filter fun (_, a) => a.exportHash == e && a.boundary == b).map (·.1)
    let (ok, challenge, solution) ← proveGroup root base (new := new) (newExp := newExp) (old := old)
      (oldExp := ← Status.loadExported root e) group
    for t in ok do
      let evidence := Json.mkObj [("name", t.name.toString), ("claim", t.claim), ("old_record", t.record),
        ("evidence", solution), ("challenge", challenge), ("solution", solution)]
      writeFileMkdirs (Store.evidencePath root t.name.toString t.claim) (jsonText evidence)
      IO.println s!"{t.name} equiv-proven {solution}"
    proven := proven + ok.size
    left := left + group.size - ok.size
  IO.println s!"equiv: {proven} proven, {left} left to a human"
  return if left == 0 then 0 else 1

end LeanBlame.Equiv
