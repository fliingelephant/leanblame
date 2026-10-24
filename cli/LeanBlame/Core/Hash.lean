/-
The hashes of docs/design/03-trust-model.md, "The hash, precisely", over the facts a frontend
reports (docs/design/15-generic-core.md). `H` is SHA-256 over a domain tag and a list of fields,
each as `<byte length>:<bytes>`:

  own(c)   = H("leanblame.own.2",   kind, role, name, uparams, type, body?, informal?)
  spec(c)  = H("leanblame.spec.2",  kind, role, name, uparams, type, informal)
  claim(c) = H("leanblame.claim.2", own(c), per direct dependency d, sorted by name:
               ("spec", spec(d)) if d is tagged, ("full", claim(d)) if not)
  group    = H("leanblame.group.2",  count, member owns sorted by name, external entries)
  member   = H("leanblame.member.2", group, name)

`name` is the printed name, `type` and `body` the hex hashes the frontend computed; an optional
field is `+<len>:<bytes>` or `-`. `informal` is there for tagged declarations only.
-/
import LeanBlame.Core.Graph

namespace LeanBlame.Hash

/-- `<byte length>:<bytes>`. -/
@[inline] def netstr (acc : String) (s : String) : String :=
  acc ++ toString s.utf8ByteSize ++ ":" ++ s

/-- SHA-256 over a domain tag and a list of fields, each as `<len>:<bytes>`. -/
def hashFields (tag : String) (fields : List String) : String :=
  mkHash (Sha256.hexOfString (fields.foldl netstr (netstr "" tag)))

def optField : Option String → String
  | some s => netstr "+" s
  | none => "-"

/-- `own(c) = H(kind, role, name, uparams, type, body, informal-if-tagged)`. -/
def own (d : Core.Decl) (informal? : Option String) : String :=
  hashFields "leanblame.own.2"
    [d.kind, toString d.role, d.name, toString d.uparams, d.typeHash, optField d.bodyHash,
     optField informal?]

/-- `spec(c) = H(kind, role, name, uparams, type, informal-text)`. -/
def spec (d : Core.Decl) (informal : String) : String :=
  hashFields "leanblame.spec.2"
    [d.kind, toString d.role, d.name, toString d.uparams, d.typeHash, informal]

/-- A dependency's contribution to a claim: `("spec", spec(d))` or `("full", claim(d))`. -/
inductive DepEntry where
  | spec (h : String)
  | full (h : String)

def DepEntry.encode : DepEntry → String
  | .spec h => netstr "spec" h
  | .full h => netstr "full" h

/-- `claim(c) = H(own(c), sorted over direct dependencies d: spec(d) or claim(d))`. The entries
come sorted by the dependency's printed name. -/
def claim (ownHash : String) (deps : List DepEntry) : String :=
  hashFields "leanblame.claim.2" (ownHash :: deps.map (·.encode))

/-- A cycle hashed as one unit: members' own hashes (sorted by name), then the dependencies
outside the group (sorted by name). -/
def group (memberOwns : List String) (external : List DepEntry) : String :=
  hashFields "leanblame.group.2"
    (toString memberOwns.length :: memberOwns ++ external.map (·.encode))

/-- Each member's hash is the group hash plus its name. -/
def member (groupHash : String) (name : String) : String :=
  hashFields "leanblame.member.2" [groupHash, name]

end LeanBlame.Hash
