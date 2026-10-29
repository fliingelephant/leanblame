/-
The interfaces of docs/design/14-schemas.md: boundary list (JSON), record (TOML), release manifest
(JSON) and status (JSON), each a Lean structure with an emitter; the boundary list and the record
have a strict reader: a missing or an unknown key is an error. Records keep the field order of
docs/design/05; JSON key order is not part of the schema.

Declaration names are kept as strings, exactly as the frontend prints them (Lean:
`Lean.Name.toString`); only the frontend maps them back to its constants
(docs/design/04-architecture.md, "Beyond Lean"). A name identifies a declaration within one export; its id
identifies it across exports.
-/
import Lake.Toml
import Lean.Data.Json
import LeanBlame.Core.Time
import LeanBlame.Core.Util

namespace LeanBlame

open Lean (Json ToJson toJson FromJson)

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

/-! ## 0. Closed value sets

Each value prints as the string the schemas use; `Role` enters the hash as that string. -/

/-- What a signer reads of a declaration's body (docs/design/03-trust-model.md): `assumed`, there
is none and the statement is taken as true; `defined`, the body is the meaning; `proved`, the body
is a proof, which the kernel checks and nobody reads. -/
inductive Role where
  | assumed | defined | proved
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

/-- What an approval of a declaration is worth now (docs/design/05): `current`, it is live and
carries the declaration's current claim; `superseded`, it is live and carries an older claim;
`withdrawn`, its signer withdrew it; `excluded`, `leanblame.toml` excludes its record;
`not-allowed`, its signer is not among `allowed_signers`. -/
inductive Standing where
  | current | superseded | withdrawn | excluded | notAllowed
  deriving Inhabited, Repr, BEq, Hashable

instance : ToString Role where
  toString
    | .assumed => "assumed"
    | .defined => "defined"
    | .proved => "proved"

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

instance : ToString Standing where
  toString
    | .current => "current"
    | .superseded => "superseded"
    | .withdrawn => "withdrawn"
    | .excluded => "excluded"
    | .notAllowed => "not-allowed"

def Role.all : List Role := [.assumed, .defined, .proved]
def Action.all : List Action := [.approve, .withdraw]

/-- The value among `all` that prints as `s`. -/
def ofString? [ToString α] (all : List α) (s : String) : Option α := all.find? (toString · == s)

/-- The value among `all` that the JSON string `j` names. -/
def ofJsonString? [ToString α] (all : List α) (j : Json) : Except String α := do
  let s ← j.getStr?
  let some a := ofString? all s | throw s!"`{s}` is not one of {", ".intercalate (all.map toString)}"
  return a

instance : ToJson Role := ⟨(Json.str <| toString ·)⟩
instance : ToJson State := ⟨(Json.str <| toString ·)⟩
instance : ToJson Cause := ⟨(Json.str <| toString ·)⟩
instance : ToJson ProofStatus := ⟨(Json.str <| toString ·)⟩
instance : ToJson Action := ⟨(Json.str <| toString ·)⟩
instance : ToJson Standing := ⟨(Json.str <| toString ·)⟩
instance : FromJson Role := ⟨ofJsonString? Role.all⟩

/-! ## 1. Boundary list -/

/-- The informal text as docs/design/03 hashes it: ASCII whitespace trimmed, line endings
normalized, no Unicode normalization (Lean core has none). -/
def normalizeInformal (s : String) : String := strTrim s.crlfToLf

/-- One piece of a printed statement: text, and the constant it refers to when it is a reference. -/
structure Segment where
  text : String
  /-- The printed name of the constant this text refers to. -/
  const : Option String := none
  deriving Inhabited, Repr, BEq

instance : ToJson Segment where
  toJson s := Json.mkObj [("text", s.text), ("const", toJson s.const)]

instance : FromJson Segment where
  fromJson? j := do
    let o ← JsonObj.read j "segment" ["text", "const"]
    return { text := ← o.get String "text", const := ← o.get (Option String) "const" }

structure BoundaryDecl where
  name : String
  /-- Stays when the declaration is renamed or edited; never hashed. Its own (Lean: written in
  `@[trusted "id"]`; a blueprint label), or else `<parent's id>/<name relative to the parent>`. -/
  id : String
  /-- The declaration whose id stands for this one: for a constructor or projection of a tagged
  inductive or structure, that declaration; for the other declarations of a blueprint label, the
  first. -/
  parent : Option String := none
  module : String
  /-- What it is, in the proof assistant's own words (Lean: as its documentation names it, `def`,
  `theorem`, `structure`, `field`, …); never interpreted, never hashed. -/
  kind : String
  role : Role
  /-- The docstring (a member without one: its parent's), as `normalizeInformal` leaves it. -/
  informal : String
  /-- Its signature (name, binders, type) as the proof assistant prints it, in segments: every
  constant reference is one of its own, so a page can link it. -/
  statement : Array Segment
  deriving Inhabited, Repr

/-- The declarations of the trusted boundary, in source order (a module after the modules it
imports, then by position). Commit, toolchain and dependencies are not part of it: they change while
the declarations stay (`Store.Current` holds them). -/
structure BoundaryList where
  library : String
  declarations : Array BoundaryDecl
  deriving Inhabited, Repr

instance : ToJson BoundaryDecl where
  toJson d := Json.mkObj [("name", d.name), ("id", d.id), ("parent", toJson d.parent),
    ("module", d.module), ("kind", d.kind), ("role", toJson d.role), ("informal", d.informal),
    ("statement", toJson d.statement)]

instance : ToJson BoundaryList where
  toJson b := Json.mkObj [("library", b.library),
    ("declarations", toJson b.declarations)]

def BoundaryDecl.fromJson? (j : Json) : Except String BoundaryDecl := do
  let o ← JsonObj.read j "declaration"
    ["name", "id", "parent", "module", "kind", "role", "informal", "statement"]
  let name ← o.get String "name"
  let o := { o with what := s!"declaration {name}" }
  let d : BoundaryDecl := {
    name, id := ← o.get String "id", parent := ← o.get (Option String) "parent"
    module := ← o.get String "module", kind := ← o.get String "kind", role := ← o.get Role "role"
    informal := ← o.get String "informal", statement := ← o.get (Array Segment) "statement" }
  for (k, v) in [("id", d.id), ("kind", d.kind), ("informal", d.informal)] do
    if v.isEmpty then throw s!"{o.what}: `{k}` is empty"
  unless normalizeInformal d.informal == d.informal do
    throw s!"{o.what}: the informal text has surrounding whitespace or CRLF line endings"
  return d

def BoundaryList.fromJson? (j : Json) : Except String BoundaryList := do
  let o ← JsonObj.read j "boundary list" ["library", "declarations"]
  let decls ← (← o.get (Array Json) "declarations").mapM BoundaryDecl.fromJson?
  let names : Std.HashSet String := decls.foldl (·.insert ·.name) {}
  unless names.size == decls.size do throw "boundary list: a name is listed twice"
  let mut ids : Std.HashMap String String := {}
  for d in decls do
    if let some other := ids[d.id]? then throw s!"boundary list: `{other}` and `{d.name}` have the same id {d.id}"
    ids := ids.insert d.id d.name
    if let some p := d.parent then
      unless names.contains p do throw s!"boundary list: the parent {p} of {d.name} is not listed"
  return { library := ← o.get String "library", declarations := decls }

/-- The declaration `key` names, by its name or its id. -/
def BoundaryList.find? (b : BoundaryList) (key : String) : Except String (Option BoundaryDecl) :=
  match b.declarations.filter fun d => d.name == key || d.id == key with
  | #[] => .ok none
  | #[d] => .ok (some d)
  | ds => .error s!"{key} is the name of one declaration and the id of another: {", ".intercalate (ds.toList.map (·.name))}"

def BoundaryList.parse (contents : String) : Except String BoundaryList := do
  BoundaryList.fromJson? (← Json.parse contents)

/-! ## 2. Record -/

/-- `provider:id` with a non-empty lowercase provider and a non-empty id. -/
def isSignerId (s : String) : Bool :=
  match s.splitOn ":" with
  | provider :: rest =>
    let id := ":".intercalate rest
    provider != "" && provider.all (fun c => c.isLower || c.isDigit || c == '-') && id != "" &&
      !rest.isEmpty
  | [] => false

/-- One declaration an approve record approves. -/
structure ApprovedConstant where
  /-- The declaration's id: the key in the record's `constants` table. -/
  id : String
  /-- Its name in the export the record names. -/
  name : String
  claim : String
  /-- The `equiv` proof the signer relied on for it. -/
  evidence : Option String := none
  deriving Inhabited, Repr

structure ApproveRecord where
  signer : String
  date : Std.Time.Timestamp
  module : String
  commit : String
  toolchain : String
  deps : Array (String × String)
  exportHash : String
  boundary : String
  constants : Array ApprovedConstant
  note : Option String := none
  deriving Inhabited, Repr

structure WithdrawRecord where
  signer : String
  date : Std.Time.Timestamp
  refersTo : String
  /-- Ids of declarations of the withdrawn record; `none`: all of them. -/
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

def signer : Record → String
  | .approve r => r.signer
  | .withdraw r => r.signer

def note : Record → Option String
  | .approve r => r.note
  | .withdraw r => r.note

def action : Record → Action
  | .approve _ => .approve
  | .withdraw _ => .withdraw

open Lake.Toml (Value ppTable) in
/-- The record as TOML, printed by Lake: the fields of docs/design/05 in order, tables last; each
declaration of an approve record is a line `"id" = { name = …, claim = …, evidence = … }`. -/
def toToml (rec : Record) : String :=
  let head (action : Action) (signer : String) (date : Std.Time.Timestamp) : Table :=
    Table.empty |>.insert `action (toString action) |>.insert `signer signer
      |>.insert `date (Value.dateTime .missing (Lake.Toml.DateTime.ofString? date.toIso).get!)
  let table (kvs : Array (String × String)) : Table :=
    kvs.foldl (init := Table.empty) fun t (k, v) => t.insert (.mkSimple k) v
  let constant (c : ApprovedConstant) : Table :=
    Table.empty |>.insert `name c.name |>.insert `claim c.claim |>.insertSome `evidence c.evidence
  ppTable <| match rec with
  | .approve r => head .approve r.signer r.date |>.insert `module r.module
      |>.insert `commit r.commit |>.insert `toolchain r.toolchain |>.insert `deps (table r.deps)
      |>.insert `export r.exportHash |>.insert `boundary r.boundary |>.insertSome `note r.note
      |>.insert `constants (r.constants.foldl (init := Table.empty) fun t c =>
          t.insert (.mkSimple c.id) (constant c))
  | .withdraw r => head .withdraw r.signer r.date |>.insert `refers_to r.refersTo
      |>.insertSome `constants r.constants |>.insertSome `note r.note

/-! Reading records. Strict: unknown keys and keys of the other action are errors. -/

def hashMsg (s : String) : String := s!"`{s}` is not sha256: plus 64 lowercase hex digits"

/-- Decode a parsed TOML table as a record. Missing or bad fields log an error and decode to a
default, so every problem is reported; a record with a logged error does not parse. -/
def decode (t : Table) : DecodeM Record := do
  let signer ← decodeStr t `signer isSignerId (s!"`{·}` is not provider:id")
  let dt : Lake.Toml.DateTime ← t.tryDecode `date
  let date ← match Std.Time.Timestamp.ofToml? dt with
    | .ok d => pure d
    | .error e => logDecodeErrorAt (refOf t `date) s!"`date`: {e}"; pure default
  let note ← t.tryDecode? `note
  let action ← decodeStr t `action (ofString? Action.all · |>.isSome) (s!"is `{·}`, not approve or withdraw")
  match ofString? Action.all action with
  | some .approve =>
    checkKeys t #["action", "signer", "date", "module", "commit", "toolchain", "deps",
      "export", "boundary", "note", "constants"] "an approve record"
    let deps ← decodeTable t `deps
    let ct ← decodeTable t `constants
    if ct.items.isEmpty then logDecodeErrorAt (refOf t `constants) "`constants` must list at least one declaration"
    return .approve {
      signer, date, note, module := ← decodeStr t `module, commit := ← decodeStr t `commit
      toolchain := ← decodeStr t `toolchain
      deps := ← deps.items.mapM fun (k, _) => return (keyString k, ← decodeStr deps k)
      exportHash := ← decodeStr t `export isHash hashMsg
      boundary := ← decodeStr t `boundary isHash hashMsg
      constants := ← ct.items.mapM fun (k, v) => do
        let id := keyString k
        let c ← Lake.Toml.tryDecodeD .empty v.decodeTable
        checkKeys c #["name", "claim", "evidence"] s!"constants.{id}"
        return { id, name := ← decodeStr c `name, claim := ← decodeStr c `claim isHash hashMsg
                 evidence := ← if c.contains `evidence then some <$> decodeStr c `evidence isHash hashMsg
                   else pure none } }
  | some .withdraw =>
    checkKeys t #["action", "signer", "date", "refers_to", "constants", "note"]
      "a withdraw record"
    let constants : Option (Array String) ← t.tryDecode? `constants
    if constants.any (·.isEmpty) then
      logDecodeErrorAt (refOf t `constants) "`constants` lists no declaration; leave it out to withdraw all"
    return .withdraw { signer, date, note, refersTo := ← decodeStr t `refers_to isHash hashMsg, constants }
  | none => return default

/-- Parse record text. -/
def parse (contents : String) (fileName : String) : IO (Except (Array String) Record) :=
  parseToml contents fileName decode

end Record

/-- A record as loaded from a records directory. -/
structure LoadedRecord where
  /-- `sha256:` of the file bytes: the record's id. -/
  hash : String
  /-- Relative to the library root. -/
  path : System.FilePath
  record : Record
  deriving Inhabited

/-- Every field of the record, with its id and path. -/
instance : ToJson LoadedRecord where
  toJson r :=
    let rec_ := r.record
    let common : List (String × Json) := [("record", r.hash), ("path", r.path.toString),
      ("action", toJson rec_.action), ("signer", rec_.signer), ("date", rec_.date.toIso),
      ("note", toJson rec_.note)]
    Json.mkObj <| common ++ match rec_ with
    | .approve a => [("module", a.module), ("commit", a.commit), ("toolchain", a.toolchain),
        ("deps", stringsJson a.deps), ("export", a.exportHash), ("boundary", a.boundary),
        ("constants", Json.arr (a.constants.map fun c => Json.mkObj [("id", c.id),
          ("name", c.name), ("claim", c.claim), ("evidence", toJson c.evidence)]))]
    | .withdraw w => [("refers_to", w.refersTo), ("constants", toJson w.constants)]

/-- The axiom report of one theorem: `proven`, `open` or `n/a`; the axioms it rests on; and among
them those that are neither standard, nor a valid tagged axiom, nor a missing proof. -/
structure ProofReport where
  status : ProofStatus
  axioms : Array String := #[]
  unpermitted : Array String := #[]
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
  /-- The checker that replayed the export (`Core.Backend.checker`). -/
  checker : String
  /-- Tagged declarations with role `proved`, each `proven` or `open`. -/
  theorems : Array (String × ProofReport)
  deriving Inhabited, Repr

/-- A manifest is written only after `checker` replayed the export, so `passed` is true. -/
instance : ToJson ReleaseManifest where
  toJson m :=
    let count (s : ProofStatus) := (m.theorems.filter (·.2.status == s)).size
    Json.mkObj [("library", m.library), ("tag", m.tag),
      ("commit", m.commit), ("toolchain", m.toolchain), ("deps", stringsJson m.deps),
      ("export", m.exportHash), ("boundary", m.boundary), ("records", toJson m.records),
      ("kernel", Json.mkObj [("checker", m.checker), ("version", m.toolchain), ("passed", true)]),
      ("theorems", Json.mkObj (m.theorems.toList.map fun (n, p) =>
        (n, Json.mkObj [("status", toJson p.status), ("axioms", toJson p.axioms)]))),
      ("counts", Json.mkObj [("proven", count .proven), ("open", count .«open»)])]

/-! ## 4. Status -/

structure Change where
  cause : Cause
  names : Array String
  deriving Inhabited, Repr, BEq, ToJson

/-- A record about one declaration. -/
structure HistoryEntry where
  record : String
  action : Action
  signer : String
  date : Std.Time.Timestamp
  /-- The declaration's name in the approve record. -/
  name : String
  /-- The claim the approval carries; for a withdraw, the claim of the approval it withdraws. -/
  claim : String
  note : Option String
  /-- What the approval is worth now; `none` for a withdraw. -/
  standing : Option Standing
  deriving Inhabited, Repr

/-- An untagged declaration a tagged one uses directly, and its module. -/
structure UntaggedDep where
  name : String
  module : String
  deriving Inhabited, Repr

structure StatusDecl where
  /-- The declaration as the boundary list has it. -/
  decl : BoundaryDecl
  claim : String
  state : State
  /-- Why the claim moved since the last live approval: empty when it did not move or there is
  none; `none` when that is unknown, as the export that approval names is not in this store. -/
  change : Option (Array Change)
  signers : Array String
  history : Array HistoryEntry
  blockedBy : Array String
  proof : ProofReport
  evidence : Option String
  taggedDeps : Array String
  untaggedDeps : Array UntaggedDep
  closureSize : Nat
  deriving Inhabited, Repr

structure StatusReport where
  library : String
  /-- `none` when the export has uncommitted changes. -/
  commit : Option String
  toolchain : String
  deps : Array (String × String)
  exportHash : String
  boundary : String
  generated : Std.Time.Timestamp
  /-- The assumptions every proof may rest on (`Core.Backend.standard`). -/
  standard : Array String
  /-- In the boundary list's order: source order. -/
  declarations : Array StatusDecl
  /-- Every record of the records directories. -/
  records : Array LoadedRecord
  /-- Untagged declarations of this library that tagged ones use, each with those users. -/
  untaggedInLibrary : Array (String × Array String)
  deriving Inhabited

instance : ToJson HistoryEntry where
  toJson h := Json.mkObj [("record", h.record), ("action", toJson h.action), ("signer", h.signer),
    ("date", h.date.toIso), ("name", h.name), ("claim", h.claim), ("note", toJson h.note),
    ("standing", toJson h.standing)]

instance : ToJson StatusDecl where
  toJson d := Json.mkObj [("name", d.decl.name), ("id", d.decl.id), ("parent", toJson d.decl.parent), ("module", d.decl.module),
    ("kind", d.decl.kind), ("role", toJson d.decl.role), ("informal", d.decl.informal),
    ("statement", toJson d.decl.statement), ("claim", d.claim),
    ("state", toJson d.state), ("change", toJson d.change), ("signers", toJson d.signers),
    ("history", toJson d.history), ("blocked_by", toJson d.blockedBy),
    ("proof", Json.mkObj [("status", toJson d.proof.status), ("axioms", toJson d.proof.axioms),
      ("unpermitted", toJson d.proof.unpermitted)]),
    ("evidence", toJson d.evidence), ("tagged_deps", toJson d.taggedDeps),
    ("untagged_deps", Json.arr (d.untaggedDeps.map fun u => Json.mkObj [("name", u.name), ("module", u.module)])),
    ("closure_size", d.closureSize)]

instance : ToJson StatusReport where
  toJson s := Json.mkObj [("library", s.library),
    ("commit", toJson s.commit), ("toolchain", s.toolchain), ("deps", stringsJson s.deps),
    ("export", s.exportHash), ("boundary", s.boundary), ("generated", s.generated.toIso),
    ("standard_axioms", toJson s.standard),
    ("declarations", toJson s.declarations),
    ("records", toJson s.records),
    ("untagged_in_library", Json.arr (s.untaggedInLibrary.map fun (n, users) =>
      Json.mkObj [("name", n), ("used_by", toJson users)]))]

end LeanBlame
