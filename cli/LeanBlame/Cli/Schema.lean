/-
The interfaces of docs/14-schemas.md: boundary list (JSON), record (TOML) and
status (JSON), each a Lean structure with an emitter; the boundary list and the
record have a strict reader. Records keep the field order of docs/05; JSON key
order is not part of the schema. The release manifest comes with `release`.

Declaration names are kept as strings, exactly as `Lean.Name.toString` prints
them; the commands map them back to constants through the export.
-/
import Lake.Toml
import Lean.Data.Json
import LeanBlame.Cli.Time
import LeanBlame.Cli.Util

namespace LeanBlame

open Lean (Json ToJson toJson)

/-! ## 1. Boundary list -/

/-- Kinds a boundary-list entry may have: the export kinds of docs/14. -/
def boundaryKinds : Array String := #["def", "theorem", "axiom", "inductive", "ctor", "opaque", "quot"]

def isInformalSource (s : String) : Bool :=
  s == "docstring" || s == "manual" ||
    (s.startsWith "blueprint:" && s.length > "blueprint:".length)

structure BoundaryDecl where
  name : String
  module : String
  kind : String
  informal : String
  informalSource : String
  deriving Inhabited, Repr

structure BoundaryList where
  library : String
  commit : String
  toolchain : String
  deps : Array (String × String)
  declarations : Array BoundaryDecl
  deriving Inhabited, Repr

def BoundaryList.schemaId : String := "leanblame.boundary.1"

instance : ToJson BoundaryDecl where
  toJson d := Json.mkObj [("name", d.name), ("module", d.module), ("kind", d.kind),
    ("informal", d.informal), ("informal_source", d.informalSource)]

instance : ToJson BoundaryList where
  toJson b := Json.mkObj [("schema", BoundaryList.schemaId), ("library", b.library),
    ("commit", b.commit), ("toolchain", b.toolchain),
    ("deps", Json.mkObj (b.deps.toList.map fun (k, v) => (k, v))),
    ("declarations", toJson b.declarations)]

/-- Field `k` of the object `j` as a string; errors name the field. -/
def getStrField (j : Json) (what k : String) : Except String String :=
  (j.getObjValAs? String k).mapError (s!"{what}.{k}: " ++ ·)

def BoundaryDecl.fromJson? (j : Json) : Except String BoundaryDecl := do
  let name ← getStrField j "declaration" "name"
  let what := s!"declaration {name}"
  let d : BoundaryDecl := {
    name
    module := ← getStrField j what "module"
    kind := ← getStrField j what "kind"
    informal := ← getStrField j what "informal"
    informalSource := ← getStrField j what "informal_source" }
  unless boundaryKinds.contains d.kind do
    throw s!"{what}: kind `{d.kind}` is not one of {", ".intercalate boundaryKinds.toList}"
  if strTrim d.informal == "" then
    throw s!"{what}: informal text is required"
  unless isInformalSource d.informalSource do
    throw s!"{what}: informal_source must be docstring, blueprint:<label> or manual"
  return d

def BoundaryList.fromJson? (j : Json) : Except String BoundaryList := do
  let w := "boundary list"
  let schema ← getStrField j w "schema"
  unless schema == BoundaryList.schemaId do
    throw s!"boundary list: schema is `{schema}`, expected `{BoundaryList.schemaId}`"
  let decls ← (j.getObjVal? "declarations" >>= (·.getArr?)).mapError (s!"{w}.declarations: " ++ ·)
  let decls ← decls.mapM BoundaryDecl.fromJson?
  let mut seen : Std.HashSet String := {}
  for d in decls do
    if seen.contains d.name then throw s!"boundary list: `{d.name}` listed twice"
    seen := seen.insert d.name
  let deps ← (j.getObjVal? "deps" >>= (·.getObj?)).mapError (s!"{w}.deps: " ++ ·)
  return {
    library := ← getStrField j w "library"
    commit := ← getStrField j w "commit"
    toolchain := ← getStrField j w "toolchain"
    deps := ← deps.toList.toArray.mapM fun (k, v) => do
      return (k, ← v.getStr?.mapError (s!"{w}.deps.{k}: " ++ ·))
    declarations := decls }

def BoundaryList.parse (contents : String) : Except String BoundaryList := do
  BoundaryList.fromJson? (← Json.parse contents)

/-! ## 2. Record -/

def Record.schemaId : String := "leanblame.record.1"

/-- `provider:id` with a non-empty lowercase provider and a non-empty id. -/
def isSignerId (s : String) : Bool :=
  match s.splitOn ":" with
  | provider :: rest =>
    let id := ":".intercalate rest
    provider != "" && provider.all (fun c => c.isLower || c.isDigit || c == '-') && id != "" &&
      !rest.isEmpty
  | [] => false

structure ApproveRecord where
  signer : String
  date : UtcTime
  module : String
  commit : String
  toolchain : String
  deps : Array (String × String)
  exportHash : String
  boundary : String
  /-- Constant name → claim hash. -/
  constants : Array (String × String)
  evidence : Option String := none
  note : Option String := none
  deriving Inhabited, Repr

structure WithdrawRecord where
  signer : String
  date : UtcTime
  refersTo : String
  /-- `none`: every constant of the withdrawn record. -/
  constants : Option (Array String) := none
  note : Option String := none
  deriving Inhabited, Repr

inductive Record where
  | approve (r : ApproveRecord)
  | withdraw (r : WithdrawRecord)
  deriving Inhabited, Repr

namespace Record

def signer : Record → String
  | .approve r => r.signer
  | .withdraw r => r.signer

def date : Record → UtcTime
  | .approve r => r.date
  | .withdraw r => r.date

def note : Record → Option String
  | .approve r => r.note
  | .withdraw r => r.note

def action : Record → String
  | .approve _ => "approve"
  | .withdraw _ => "withdraw"

private def tomlStr (s : String) : String := Lake.Toml.ppString s

private def tomlKey (k : String) : String := Lake.Toml.ppSimpleKey k

/-- The record as TOML, in the field order of docs/05 and docs/14. -/
def toToml : Record → String
  | .approve r =>
    let deps := ", ".intercalate (r.deps.toList.map fun (k, v) => s!"{tomlKey k} = {tomlStr v}")
    let deps := if r.deps.isEmpty then "{}" else "{ " ++ deps ++ " }"
    let lines := [
      s!"schema = {tomlStr schemaId}",
      "action = \"approve\"",
      s!"signer = {tomlStr r.signer}",
      s!"date = {r.date.toIso}",
      s!"module = {tomlStr r.module}",
      s!"commit = {tomlStr r.commit}",
      s!"toolchain = {tomlStr r.toolchain}",
      s!"deps = {deps}",
      s!"export = {tomlStr r.exportHash}",
      s!"boundary = {tomlStr r.boundary}"] ++
      (r.evidence.toList.map fun e => s!"evidence = {tomlStr e}") ++
      (r.note.toList.map fun n => s!"note = {tomlStr n}") ++
      ["", "[constants]"] ++
      (r.constants.toList.map fun (k, v) => s!"{tomlStr k} = {tomlStr v}")
    "\n".intercalate lines ++ "\n"
  | .withdraw r =>
    let lines := [
      s!"schema = {tomlStr schemaId}",
      "action = \"withdraw\"",
      s!"signer = {tomlStr r.signer}",
      s!"date = {r.date.toIso}",
      s!"refers_to = {tomlStr r.refersTo}"] ++
      (r.constants.toList.map fun cs =>
        s!"constants = [{", ".intercalate (cs.toList.map tomlStr)}]") ++
      (r.note.toList.map fun n => s!"note = {tomlStr n}")
    "\n".intercalate lines ++ "\n"

/-! Reading records. Strict: unknown keys and keys of the other action are errors. -/

private def keyString (k : Lean.Name) : String :=
  match k with
  | .str .anonymous s => s
  | _ => k.toString (escape := false)

private abbrev Decoder := StateT (Array String) Id

private def report (msg : String) : Decoder Unit := modify (·.push msg)

private def getStr? (t : Lake.Toml.Table) (k : String) (required : Bool) : Decoder (Option String) := do
  match t.find? (Lean.Name.mkSimple k) with
  | some (.string _ s) => return some s
  | some _ => report s!"`{k}` must be a string"; return none
  | none => (if required then report s!"missing `{k}`" else pure ()); return none

private def getHash? (t : Lake.Toml.Table) (k : String) (required : Bool) : Decoder (Option String) := do
  let some s ← getStr? t k required | return none
  unless isHash s do report s!"`{k}` must be sha256: plus 64 lowercase hex digits"
  return some s

/-- Decode a parsed TOML table as a record, collecting every problem. -/
def ofTable (t : Lake.Toml.Table) : Except (Array String) Record :=
  let act : Decoder (Option Record) := do
    let schema ← getStr? t "schema" true
    if let some s := schema then
      unless s == schemaId do report s!"`schema` is `{s}`, expected `{schemaId}`"
    let signer ← getStr? t "signer" true
    if let some s := signer then
      unless isSignerId s do report s!"`signer` must be provider:id, got `{s}`"
    let date ← match t.find? `date with
      | some (.dateTime _ dt) =>
        match UtcTime.ofToml? dt with
        | .ok d => pure (some d)
        | .error e => report s!"`date`: {e}"; pure none
      | some _ => report "`date` must be a TOML datetime"; pure none
      | none => report "missing `date`"; pure none
    let note ← getStr? t "note" false
    let action ← getStr? t "action" true
    match action with
    | some "approve" =>
      let allowed := #["schema", "action", "signer", "date", "constants", "module", "commit",
        "toolchain", "deps", "export", "boundary", "evidence", "note"]
      for (k, _) in t.items do
        unless allowed.contains (keyString k) do report s!"unknown key `{keyString k}` in an approve record"
      let module ← getStr? t "module" true
      let commit ← getStr? t "commit" true
      let toolchain ← getStr? t "toolchain" true
      let exportHash ← getHash? t "export" true
      let boundary ← getHash? t "boundary" true
      let evidence ← getHash? t "evidence" false
      let deps ← match t.find? `deps with
        | some (.table _ dt) => dt.items.filterMapM fun (k, v) => do
            match v with
            | .string _ s => return some (keyString k, s)
            | _ => report s!"`deps.{keyString k}` must be a string"; return none
        | some _ => report "`deps` must be a table"; pure #[]
        | none => report "missing `deps`"; pure #[]
      let constants ← match t.find? `constants with
        | some (.table _ ct) => ct.items.filterMapM fun (k, v) => do
            match v with
            | .string _ s =>
              unless isHash s do report s!"`constants.\"{keyString k}\"` must be a sha256 hash"
              return some (keyString k, s)
            | _ => report s!"`constants.\"{keyString k}\"` must be a string"; return none
        | some _ => report "`constants` must be a table of name = claim hash"; pure #[]
        | none => report "missing `constants`"; pure #[]
      if constants.isEmpty then report "`constants` must list at least one constant"
      match signer, date, module, commit, toolchain, exportHash, boundary with
      | some signer, some date, some module, some commit, some toolchain, some exportHash,
          some boundary =>
        return some (.approve {
          signer := signer, date := date, module := module, commit := commit
          toolchain := toolchain, deps := deps, exportHash := exportHash, boundary := boundary
          constants := constants, evidence := evidence, note := note })
      | _, _, _, _, _, _, _ => return none
    | some "withdraw" =>
      let allowed := #["schema", "action", "signer", "date", "constants", "refers_to", "note"]
      for (k, _) in t.items do
        unless allowed.contains (keyString k) do report s!"unknown key `{keyString k}` in a withdraw record"
      let refersTo ← getHash? t "refers_to" true
      let constants ← match t.find? `constants with
        | some (.array _ vs) => some <$> vs.filterMapM fun v => do
            match v with
            | .string _ s => return some s
            | _ => report "`constants` must be a list of names"; return none
        | some _ => report "`constants` must be a list of names"; pure none
        | none => pure none
      match signer, date, refersTo with
      | some signer, some date, some refersTo =>
        return some (.withdraw {
          signer := signer, date := date, refersTo := refersTo, constants := constants
          note := note })
      | _, _, _ => return none
    | some a => report s!"`action` must be approve or withdraw, got `{a}`"; return none
    | none => return none
  match act.run #[] with
  | (some r, errs) => if errs.isEmpty then .ok r else .error errs
  | (none, errs) => .error (if errs.isEmpty then #["not a record"] else errs)

/-- Parse record text. -/
def parse (contents : String) (fileName : String) : IO (Except (Array String) Record) := do
  let ictx := Lean.Parser.mkInputContext contents fileName
  match ← (Lake.Toml.loadToml ictx).toBaseIO with
  | .ok t => return ofTable t
  | .error log =>
    let msgs ← log.toList.mapM fun m => m.toString
    return .error (msgs.toArray.map strTrim)

end Record

/-! ## 4. Status -/

structure Change where
  cause : String
  names : Array String
  deriving Inhabited, Repr, BEq, ToJson

structure HistoryEntry where
  record : String
  action : String
  signer : String
  date : UtcTime
  claim : Option String
  note : Option String
  deriving Inhabited, Repr

structure ProofReport where
  status : String
  axioms : Array String := #[]
  exportHash : Option String := none
  deriving Inhabited, Repr

structure StatusDecl where
  module : String
  kind : String
  informal : String
  informalSource : String
  claim : String
  state : String
  flags : Array String
  change : Array Change
  signers : Array String
  history : Array HistoryEntry
  blockedBy : Array String
  proof : ProofReport
  evidence : Option String
  taggedDeps : Array String
  closureSize : Nat
  deriving Inhabited, Repr

structure StatusReport where
  library : String
  commit : String
  exportHash : String
  generated : UtcTime
  declarations : Array (String × StatusDecl)
  deriving Inhabited, Repr

def StatusReport.schemaId : String := "leanblame.status.1"

/-- `claim`, `evidence` and `proof.export` are `null` when absent; `note` is omitted. -/
instance : ToJson HistoryEntry where
  toJson h := Json.mkObj <| ([("record", h.record), ("action", h.action), ("signer", h.signer),
    ("date", h.date.toIso), ("claim", toJson h.claim)] : List (String × Json)) ++
    Json.opt "note" h.note

instance : ToJson StatusDecl where
  toJson d := Json.mkObj [("module", d.module), ("kind", d.kind), ("informal", d.informal),
    ("informal_source", d.informalSource), ("claim", d.claim), ("state", d.state),
    ("flags", toJson d.flags), ("change", toJson d.change), ("signers", toJson d.signers),
    ("history", toJson d.history), ("blocked_by", toJson d.blockedBy),
    ("proof", Json.mkObj [("status", d.proof.status), ("axioms", toJson d.proof.axioms),
      ("export", toJson d.proof.exportHash)]),
    ("evidence", toJson d.evidence), ("tagged_deps", toJson d.taggedDeps),
    ("closure_size", d.closureSize)]

instance : ToJson StatusReport where
  toJson s := Json.mkObj [("schema", StatusReport.schemaId), ("library", s.library),
    ("commit", s.commit), ("export", s.exportHash), ("generated", s.generated.toIso),
    ("declarations", Json.mkObj (s.declarations.toList.map fun (n, d) => (n, toJson d)))]

end LeanBlame
