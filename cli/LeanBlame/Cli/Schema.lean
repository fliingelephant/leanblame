/-
The interfaces of docs/design/14-schemas.md: boundary list (JSON), record (TOML),
release manifest (JSON) and status (JSON), each a Lean structure with an
emitter; the boundary list and the record have a strict reader. Records keep the
field order of docs/design/05; JSON key order is not part of the schema.

Declaration names are kept as strings, exactly as `Lean.Name.toString` prints
them; the commands map them back to constants through the export.
-/
import Lake.Toml
import Lean.Data.Json
import LeanBlame.Cli.Time
import LeanBlame.Cli.Util

namespace LeanBlame

open Lean (Json ToJson toJson)

/-! TOML -/

open Lake.Toml (DecodeM Table logDecodeErrorAt)

/-- Parse TOML text and decode it, collecting every problem, each with its line and column.
`fileName` names the text in messages. -/
def parseToml (contents fileName : String) (decode : Table → DecodeM α) :
    IO (Except (Array String) α) := do
  let ictx := Lean.Parser.mkInputContext contents fileName
  match ← (Lake.Toml.loadToml ictx).toBaseIO with
  | .error log => return .error ((← log.toList.mapM (·.toString)).toArray.map strTrim)
  | .ok t =>
    match (decode t).run #[] with
    | .ok a errs =>
      if errs.isEmpty then return .ok a
      return .error <| errs.map fun e => match e.ref.getPos? with
        | some p => let pos := ictx.fileMap.toPosition p; s!"{pos.line}:{pos.column}: {e.msg}"
        | none => e.msg
    | .error e _ => nomatch e

/-- A TOML key as written: a bare key is not escaped. -/
def keyString (k : Lean.Name) : String :=
  match k with
  | .str .anonymous s => s
  | _ => k.toString (escape := false)

/-- Where key `k` of `t` is, for messages. -/
def refOf (t : Table) (k : Lean.Name) : Lean.Syntax := (t.find? k).map (·.ref) |>.getD .missing

/-- Log every key of `t` that is not in `allowed`. -/
def checkKeys (t : Table) (allowed : Array String) (what : String) : DecodeM Unit :=
  t.items.forM fun (k, v) => unless allowed.contains (keyString k) do
    logDecodeErrorAt v.ref s!"unknown key `{keyString k}` in {what}"

/-- The required string `k` of `t`; when it is a string that fails `ok`, log `msg` at it. -/
def decodeStr (t : Table) (k : Lean.Name) (ok : String → Bool := fun _ => true)
    (msg : String → String := fun _ => "") : DecodeM String := do
  let s ← t.tryDecode k
  if let some (.string ref _) := t.find? k then
    unless ok s do logDecodeErrorAt ref s!"`{keyString k}`: {msg s}"
  return s

/-- The table `k` of `t`, empty when it is missing or not a table (the error is logged). -/
def decodeTable (t : Table) (k : Lean.Name) : DecodeM Table :=
  Lake.Toml.tryDecodeD .empty do (← t.decodeValue k).decodeTable

/-- A constant name as the boundary list and records write it (`Lean.Name.toString`), read back.
`export` lists only names that read back. -/
def constName? (s : String) : Option Lean.Name := Lean.Syntax.decodeNameLit ("`" ++ s)

/-! ## 0. Closed value sets

Each value prints as the string the schemas use; `Kind` and `Safety` enter the hash as that string. -/

/-- The export kind of a constant. Every kind but `rec` may be on the boundary list. (`recursor`,
because `Kind.rec` is the type's own recursor.) -/
inductive Kind where
  | «def» | «theorem» | «axiom» | «inductive» | ctor | «opaque» | quot | recursor
  deriving Inhabited, Repr, BEq, Hashable

/-- What the kernel sees of a definition's body: `partial` and `opaque` bodies are hidden. -/
inductive Safety where
  | safe | «partial» | «opaque»
  deriving Inhabited, Repr, BEq, Hashable

/-- The state of a tagged declaration (docs/design/03, "Validity"). -/
inductive State where
  | valid | outdated | unsigned
  deriving Inhabited, Repr, BEq, Hashable

/-- Why a claim hash moved (docs/design/03, "Why a hash moved"). -/
inductive Cause where
  | ownText | ownBody | depSpec | cutMoved | untagged
  deriving Inhabited, Repr, BEq, Hashable

/-- A theorem's axiom report (docs/design/07). -/
inductive ProofStatus where
  | proven | «open» | na
  deriving Inhabited, Repr, BEq, Hashable

/-- What a record does. -/
inductive Action where
  | approve | withdraw
  deriving Inhabited, Repr, BEq, Hashable

instance : ToString Kind where
  toString
    | .«def» => "def"
    | .«theorem» => "theorem"
    | .«axiom» => "axiom"
    | .«inductive» => "inductive"
    | .ctor => "ctor"
    | .«opaque» => "opaque"
    | .quot => "quot"
    | .recursor => "rec"

instance : ToString Safety where
  toString
    | .safe => "safe"
    | .«partial» => "partial"
    | .«opaque» => "opaque"

instance : ToString State where
  toString
    | .valid => "valid"
    | .outdated => "outdated"
    | .unsigned => "unsigned"

instance : ToString Cause where
  toString
    | .ownText => "own-text"
    | .ownBody => "own-body"
    | .depSpec => "dep-spec"
    | .cutMoved => "cut-moved"
    | .untagged => "untagged"

instance : ToString ProofStatus where
  toString
    | .proven => "proven"
    | .«open» => "open"
    | .na => "n/a"

instance : ToString Action where
  toString
    | .approve => "approve"
    | .withdraw => "withdraw"

def Kind.all : List Kind := [.«def», .«theorem», .«axiom», .«inductive», .ctor, .«opaque», .quot, .recursor]
def Safety.all : List Safety := [.safe, .«partial», .«opaque»]
def Action.all : List Action := [.approve, .withdraw]

/-- The value among `all` that prints as `s`. -/
def ofString? [ToString α] (all : List α) (s : String) : Option α := all.find? (toString · == s)

instance : ToJson Kind := ⟨(Json.str <| toString ·)⟩
instance : ToJson Safety := ⟨(Json.str <| toString ·)⟩
instance : ToJson State := ⟨(Json.str <| toString ·)⟩
instance : ToJson Cause := ⟨(Json.str <| toString ·)⟩
instance : ToJson ProofStatus := ⟨(Json.str <| toString ·)⟩
instance : ToJson Action := ⟨(Json.str <| toString ·)⟩

/-! ## 1. Boundary list -/

def isInformalSource (s : String) : Bool :=
  s == "docstring" || s == "manual" ||
    (s.startsWith "blueprint:" && s.length > "blueprint:".length)

structure BoundaryDecl where
  name : String
  module : String
  kind : Kind
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
  toJson d := Json.mkObj [("name", d.name), ("module", d.module), ("kind", toJson d.kind),
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
  let kind ← getStrField j what "kind"
  let some kind := (ofString? Kind.all kind).filter (· != .recursor)
    | throw s!"{what}: kind `{kind}` is not one of {", ".intercalate ((Kind.all.filter (· != .recursor)).map toString)}"
  let d : BoundaryDecl := {
    name, kind
    module := ← getStrField j what "module"
    informal := ← getStrField j what "informal"
    informalSource := ← getStrField j what "informal_source" }
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
  date : Std.Time.Timestamp
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
  date : Std.Time.Timestamp
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

def date : Record → Std.Time.Timestamp
  | .approve r => r.date
  | .withdraw r => r.date

open Lake.Toml (Value ppTable) in
/-- The record as TOML, printed by Lake: the fields of docs/design/05 in order, tables last. -/
def toToml (rec : Record) : String :=
  let head (action : Action) (signer : String) (date : Std.Time.Timestamp) : Table :=
    Table.empty |>.insert `schema schemaId |>.insert `action (toString action) |>.insert `signer signer
      |>.insert `date (Value.dateTime .missing (Lake.Toml.DateTime.ofString? date.toIso).get!)
  let table (kvs : Array (String × String)) : Table :=
    kvs.foldl (init := Table.empty) fun t (k, v) => t.insert (.mkSimple k) v
  ppTable <| match rec with
  | .approve r => head .approve r.signer r.date |>.insert `module r.module
      |>.insert `commit r.commit |>.insert `toolchain r.toolchain |>.insert `deps (table r.deps)
      |>.insert `export r.exportHash |>.insert `boundary r.boundary
      |>.insertSome `evidence r.evidence |>.insertSome `note r.note
      |>.insert `constants (table r.constants)
  | .withdraw r => head .withdraw r.signer r.date |>.insert `refers_to r.refersTo
      |>.insertSome `constants r.constants |>.insertSome `note r.note

/-! Reading records. Strict: unknown keys and keys of the other action are errors. -/

def hashMsg (s : String) : String := s!"`{s}` is not sha256: plus 64 lowercase hex digits"

/-- Decode a parsed TOML table as a record. Missing or bad fields log an error and decode to a
default, so every problem is reported. -/
def decode (t : Table) : DecodeM Record := do
  discard <| decodeStr t `schema (· == schemaId) (s!"is `{·}`, expected `{schemaId}`")
  let signer ← decodeStr t `signer isSignerId (s!"`{·}` is not provider:id")
  let dt : Lake.Toml.DateTime ← t.tryDecode `date
  let date ← match Std.Time.Timestamp.ofToml? dt with
    | .ok d => pure d
    | .error e => logDecodeErrorAt (refOf t `date) s!"`date`: {e}"; pure default
  let note ← t.tryDecode? `note
  let action ← decodeStr t `action (ofString? Action.all · |>.isSome) (s!"is `{·}`, not approve or withdraw")
  match ofString? Action.all action with
  | some .approve =>
    checkKeys t #["schema", "action", "signer", "date", "constants", "module", "commit", "toolchain",
      "deps", "export", "boundary", "evidence", "note"] "an approve record"
    let deps ← decodeTable t `deps
    let ct ← decodeTable t `constants
    if ct.items.isEmpty then logDecodeErrorAt .missing "`constants` must list at least one constant"
    return .approve {
      signer, date, note, module := ← decodeStr t `module, commit := ← decodeStr t `commit
      toolchain := ← decodeStr t `toolchain
      deps := ← deps.items.mapM fun (k, _) => return (keyString k, ← decodeStr deps k)
      exportHash := ← decodeStr t `export isHash hashMsg
      boundary := ← decodeStr t `boundary isHash hashMsg
      constants := ← ct.items.mapM fun (k, _) => return (keyString k, ← decodeStr ct k isHash hashMsg)
      evidence := ← if t.contains `evidence then some <$> decodeStr t `evidence isHash hashMsg
        else pure none }
  | some .withdraw =>
    checkKeys t #["schema", "action", "signer", "date", "constants", "refers_to", "note"]
      "a withdraw record"
    return .withdraw {
      signer, date, note, refersTo := ← decodeStr t `refers_to isHash hashMsg
      constants := ← t.tryDecode? `constants }
  | none => return default

/-- Parse record text. -/
def parse (contents : String) (fileName : String) : IO (Except (Array String) Record) :=
  parseToml contents fileName decode

end Record

/-- The axiom report of one theorem: `proven`, `open` or `n/a`, with the axioms it rests on. -/
structure ProofReport where
  status : ProofStatus
  axioms : Array String := #[]
  deriving Inhabited, Repr

/-! ## 3. Release manifest -/

structure ReleaseManifest where
  library : String
  tag : String
  commit : String
  toolchain : String
  deps : Array (String × String)
  exportHash : String
  boundary : String
  records : Array String
  /-- Tagged theorems, `proven` or `open`. -/
  theorems : Array (String × ProofReport)
  deriving Inhabited, Repr

def ReleaseManifest.schemaId : String := "leanblame.release.1"

/-- A manifest is written only after `leanchecker` replayed the export, so `passed` is true. -/
instance : ToJson ReleaseManifest where
  toJson m :=
    let count (s : ProofStatus) := (m.theorems.filter (·.2.status == s)).size
    Json.mkObj [("schema", ReleaseManifest.schemaId), ("library", m.library), ("tag", m.tag),
      ("commit", m.commit), ("toolchain", m.toolchain),
      ("deps", Json.mkObj (m.deps.toList.map fun (k, v) => (k, v))), ("export", m.exportHash),
      ("boundary", m.boundary), ("records", toJson m.records),
      ("kernel", Json.mkObj [("checker", "leanchecker"), ("version", m.toolchain), ("passed", true)]),
      ("theorems", Json.mkObj (m.theorems.toList.map fun (n, p) =>
        (n, Json.mkObj [("status", toJson p.status), ("axioms", toJson p.axioms)]))),
      ("counts", Json.mkObj [("proven", count .proven), ("open", count .«open»)])]

/-! ## 4. Status -/

structure Change where
  cause : Cause
  names : Array String
  deriving Inhabited, Repr, BEq, ToJson

structure HistoryEntry where
  record : String
  action : Action
  signer : String
  date : Std.Time.Timestamp
  claim : Option String
  note : Option String
  deriving Inhabited, Repr

structure StatusDecl where
  module : String
  kind : Kind
  informal : String
  informalSource : String
  claim : String
  state : State
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
  generated : Std.Time.Timestamp
  declarations : Array (String × StatusDecl)
  deriving Inhabited, Repr

def StatusReport.schemaId : String := "leanblame.status.1"

/-- `claim` and `evidence` are `null` when absent; `note` is omitted. -/
instance : ToJson HistoryEntry where
  toJson h := Json.mkObj <| ([("record", h.record), ("action", toJson h.action), ("signer", h.signer),
    ("date", h.date.toIso), ("claim", toJson h.claim)] : List (String × Json)) ++
    Json.opt "note" h.note

instance : ToJson StatusDecl where
  toJson d := Json.mkObj [("module", d.module), ("kind", toJson d.kind), ("informal", d.informal),
    ("informal_source", d.informalSource), ("claim", d.claim), ("state", toJson d.state),
    ("change", toJson d.change), ("signers", toJson d.signers),
    ("history", toJson d.history), ("blocked_by", toJson d.blockedBy),
    ("proof", Json.mkObj [("status", toJson d.proof.status), ("axioms", toJson d.proof.axioms)]),
    ("evidence", toJson d.evidence), ("tagged_deps", toJson d.taggedDeps),
    ("closure_size", d.closureSize)]

instance : ToJson StatusReport where
  toJson s := Json.mkObj [("schema", StatusReport.schemaId), ("library", s.library),
    ("commit", s.commit), ("export", s.exportHash), ("generated", s.generated.toIso),
    ("declarations", Json.mkObj (s.declarations.toList.map fun (n, d) => (n, toJson d)))]

end LeanBlame
