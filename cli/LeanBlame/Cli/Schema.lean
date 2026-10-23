/-
The four interfaces of docs/14-schemas.md: boundary list (JSON), record (TOML),
release manifest (JSON), status (JSON). Each has a Lean structure, an emitter
that writes the fields in the order docs/14 lists them, and a strict reader.

Declaration names are kept as strings, exactly as `Lean.Name.toString` prints
them; the commands map them back to constants through the export.
-/
import Lake.Toml
import LeanBlame.Cli.Json
import LeanBlame.Cli.Time
import LeanBlame.Cli.Util

namespace LeanBlame

open Lean (Json)
open JsonRead

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

def BoundaryDecl.toOJson (d : BoundaryDecl) : OJson :=
  .obj #[("name", .str d.name), ("module", .str d.module), ("kind", .str d.kind),
    ("informal", .str d.informal), ("informal_source", .str d.informalSource)]

def BoundaryList.toOJson (b : BoundaryList) : OJson :=
  .obj #[("schema", .str BoundaryList.schemaId), ("library", .str b.library),
    ("commit", .str b.commit), ("toolchain", .str b.toolchain), ("deps", .strMap b.deps),
    ("declarations", .arr (b.declarations.map (·.toOJson)))]

def BoundaryDecl.fromJson? (j : Json) : Except String BoundaryDecl := do
  let o ← obj j "declaration"
  let name ← strField o "name" "declaration"
  let what := s!"declaration {name}"
  let d : BoundaryDecl := {
    name
    module := ← strField o "module" what
    kind := ← strField o "kind" what
    informal := ← strField o "informal" what
    informalSource := ← strField o "informal_source" what }
  unless boundaryKinds.contains d.kind do
    throw s!"{what}: kind `{d.kind}` is not one of {", ".intercalate boundaryKinds.toList}"
  if strTrim d.informal == "" then
    throw s!"{what}: informal text is required"
  unless isInformalSource d.informalSource do
    throw s!"{what}: informal_source must be docstring, blueprint:<label> or manual"
  return d

def BoundaryList.fromJson? (j : Json) : Except String BoundaryList := do
  let o ← obj j "boundary list"
  let schema ← strField o "schema" "boundary list"
  unless schema == BoundaryList.schemaId do
    throw s!"boundary list: schema is `{schema}`, expected `{BoundaryList.schemaId}`"
  let decls ← (← arr (← field o "declarations" "boundary list") "boundary list.declarations").mapM
    BoundaryDecl.fromJson?
  let mut seen : Std.HashSet String := {}
  for d in decls do
    if seen.contains d.name then throw s!"boundary list: `{d.name}` listed twice"
    seen := seen.insert d.name
  return {
    library := ← strField o "library" "boundary list"
    commit := ← strField o "commit" "boundary list"
    toolchain := ← strField o "toolchain" "boundary list"
    deps := ← strMap (← field o "deps" "boundary list") "boundary list.deps"
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

/-! ## 3. Release manifest -/

structure KernelReport where
  checker : String
  version : String
  passed : Bool
  deriving Inhabited, Repr

structure TheoremReport where
  status : String
  axioms : Array String
  deriving Inhabited, Repr

structure ReleaseManifest where
  library : String
  tag : String
  commit : String
  toolchain : String
  deps : Array (String × String)
  exportHash : String
  boundary : String
  records : Array String
  kernel : KernelReport
  theorems : Array (String × TheoremReport)
  proven : Nat
  «open» : Nat
  deriving Inhabited, Repr

def ReleaseManifest.schemaId : String := "leanblame.release.1"

def ReleaseManifest.toOJson (m : ReleaseManifest) : OJson :=
  .obj #[("schema", .str ReleaseManifest.schemaId), ("library", .str m.library),
    ("tag", .str m.tag), ("commit", .str m.commit), ("toolchain", .str m.toolchain),
    ("deps", .strMap m.deps), ("export", .str m.exportHash), ("boundary", .str m.boundary),
    ("records", .strs m.records),
    ("kernel", .obj #[("checker", .str m.kernel.checker), ("version", .str m.kernel.version),
      ("passed", .bool m.kernel.passed)]),
    ("theorems", .obj (m.theorems.map fun (n, t) =>
      (n, .obj #[("status", .str t.status), ("axioms", .strs t.axioms)]))),
    ("counts", .obj #[("proven", .num m.proven), ("open", .num m.open)])]

def ReleaseManifest.fromJson? (j : Json) : Except String ReleaseManifest := do
  let w := "release manifest"
  let o ← obj j w
  let schema ← strField o "schema" w
  unless schema == ReleaseManifest.schemaId do throw s!"{w}: schema is `{schema}`"
  let k ← obj (← field o "kernel" w) s!"{w}.kernel"
  let ths ← obj (← field o "theorems" w) s!"{w}.theorems"
  let theorems ← ths.toList.toArray.mapM fun (n, tj) => do
    let to ← obj tj s!"{w}.theorems.{n}"
    return (n, { status := ← strField to "status" n, axioms := ← strArr (← field to "axioms" n) n })
  let counts ← obj (← field o "counts" w) s!"{w}.counts"
  return {
    library := ← strField o "library" w, tag := ← strField o "tag" w
    commit := ← strField o "commit" w, toolchain := ← strField o "toolchain" w
    deps := ← strMap (← field o "deps" w) s!"{w}.deps"
    exportHash := ← strField o "export" w, boundary := ← strField o "boundary" w
    records := ← strArr (← field o "records" w) s!"{w}.records"
    kernel := { checker := ← strField k "checker" w, version := ← strField k "version" w
                passed := ← bool (← field k "passed" w) s!"{w}.kernel.passed" }
    theorems
    proven := ← nat (← field counts "proven" w) s!"{w}.counts.proven"
    «open» := ← nat (← field counts "open" w) s!"{w}.counts.open" }

/-! ## 4. Status -/

structure Change where
  cause : String
  names : Array String
  deriving Inhabited, Repr, BEq

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

def HistoryEntry.toOJson (h : HistoryEntry) : OJson :=
  .obj (#[("record", .str h.record), ("action", .str h.action), ("signer", .str h.signer),
    ("date", .str h.date.toIso), ("claim", .optStr h.claim)] ++
    (h.note.toArray.map fun n => ("note", .str n)))

def StatusDecl.toOJson (d : StatusDecl) : OJson :=
  .obj #[("module", .str d.module), ("kind", .str d.kind), ("informal", .str d.informal),
    ("informal_source", .str d.informalSource), ("claim", .str d.claim), ("state", .str d.state),
    ("flags", .strs d.flags),
    ("change", .arr (d.change.map fun c => .obj #[("cause", .str c.cause), ("names", .strs c.names)])),
    ("signers", .strs d.signers),
    ("history", .arr (d.history.map (·.toOJson))),
    ("blocked_by", .strs d.blockedBy),
    ("proof", .obj #[("status", .str d.proof.status), ("axioms", .strs d.proof.axioms),
      ("export", .optStr d.proof.exportHash)]),
    ("evidence", .optStr d.evidence),
    ("tagged_deps", .strs d.taggedDeps),
    ("closure_size", .num d.closureSize)]

def StatusReport.toOJson (s : StatusReport) : OJson :=
  .obj #[("schema", .str StatusReport.schemaId), ("library", .str s.library),
    ("commit", .str s.commit), ("export", .str s.exportHash), ("generated", .str s.generated.toIso),
    ("declarations", .obj (s.declarations.map fun (n, d) => (n, d.toOJson)))]

def HistoryEntry.fromJson? (j : Json) : Except String HistoryEntry := do
  let o ← obj j "history entry"
  return {
    record := ← strField o "record" "history", action := ← strField o "action" "history"
    signer := ← strField o "signer" "history"
    date := ← UtcTime.ofIso? (← strField o "date" "history")
    claim := ← optStrField o "claim" "history", note := ← optStrField o "note" "history" }

def StatusDecl.fromJson? (name : String) (j : Json) : Except String StatusDecl := do
  let o ← obj j name
  let p ← obj (← field o "proof" name) s!"{name}.proof"
  let change ← (← arr (← field o "change" name) s!"{name}.change").mapM fun c => do
    let co ← obj c s!"{name}.change"
    return { cause := ← strField co "cause" name, names := ← strArr (← field co "names" name) name }
  return {
    module := ← strField o "module" name, kind := ← strField o "kind" name
    informal := ← strField o "informal" name, informalSource := ← strField o "informal_source" name
    claim := ← strField o "claim" name, state := ← strField o "state" name
    flags := ← strArr (← field o "flags" name) name
    change
    signers := ← strArr (← field o "signers" name) name
    history := ← (← arr (← field o "history" name) name).mapM HistoryEntry.fromJson?
    blockedBy := ← strArr (← field o "blocked_by" name) name
    proof := { status := ← strField p "status" name, axioms := ← strArr (← field p "axioms" name) name
               exportHash := ← optStrField p "export" name }
    evidence := ← optStrField o "evidence" name
    taggedDeps := ← strArr (← field o "tagged_deps" name) name
    closureSize := ← nat (← field o "closure_size" name) name }

def StatusReport.fromJson? (j : Json) : Except String StatusReport := do
  let o ← obj j "status"
  let schema ← strField o "schema" "status"
  unless schema == StatusReport.schemaId do throw s!"status: schema is `{schema}`"
  let ds ← obj (← field o "declarations" "status") "status.declarations"
  return {
    library := ← strField o "library" "status", commit := ← strField o "commit" "status"
    exportHash := ← strField o "export" "status"
    generated := ← UtcTime.ofIso? (← strField o "generated" "status")
    declarations := ← ds.toList.toArray.mapM fun (n, d) => do return (n, ← StatusDecl.fromJson? n d) }

end LeanBlame
