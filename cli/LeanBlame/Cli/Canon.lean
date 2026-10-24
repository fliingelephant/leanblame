/-
Canonical printing of exported terms (docs/design/03-trust-model.md, "The hash,
precisely"), and the per-constant hashes built from it.

Terms are printed from the parsed export with de Bruijn indices, constants by
name (never by export index), universe parameters by position. Binder names,
binder info (implicitness) and metadata are not printed. An erased proof
prints as one marker. A compound subterm is printed in full once; where it
occurs again it prints as a reference to that first occurrence, so a term
prints in time linear in its size as a graph, not as a tree. The encoding is
prefix-free:

  name     n <component>* .     component: s<len>:<utf8>  |  i<number>;
  level    0 | S l | M l l | I l l | P<position>;
  expr     b<index>; | s level | c name <count>; level* | a f x | l type body
           | p type body | z type value body | N<number>; | T<len>:<utf8>
           | j name <index>; expr | e (erased proof)
           | r<index>; (the compound subterm printed in full as the index-th one)

Hashes are SHA-256 over fields encoded as `<len>:<bytes>`, each list prefixed
with a domain tag.
-/
import LeanBlame.Cli.Erase
import LeanBlame.Cli.Schema

namespace LeanBlame.Canon

open Lean

/-- `<byte length>:<bytes>`. -/
@[inline] def netstr (acc : String) (s : String) : String :=
  acc ++ toString s.utf8ByteSize ++ ":" ++ s

/-- `n`, the components root first, `.`. -/
def name (acc : String) (n : Name) : String :=
  n.components.foldl (init := acc ++ "n") component ++ "."
where component (acc : String) : Name → String
  | .str _ s => netstr (acc ++ "s") s
  | .num _ k => acc ++ "i" ++ toString k ++ ";"
  | .anonymous => acc

partial def level (ups : List Name) (acc : String) : Level → String
  | .zero => acc ++ "0"
  | .succ l => level ups (acc ++ "S") l
  | .max a b => level ups (level ups (acc ++ "M") a) b
  | .imax a b => level ups (level ups (acc ++ "I") a) b
  | .param p =>
    match ups.idxOf? p with
    | some i => acc ++ "P" ++ toString i ++ ";"
    | none => name (acc ++ "Q") p
  | .mvar _ => acc ++ "?"

/-- The compound subterms printed in full so far, numbered in order of first occurrence. -/
abbrev PrintM := StateM (Std.HashMap Expr Nat)

partial def expr (ups : List Name) (acc : String) (e : Expr) : PrintM String := do
  match e with
  | .bvar i => return acc ++ "b" ++ toString i ++ ";"
  | .sort l => return level ups (acc ++ "s") l
  | .const c us => return us.foldl (level ups) (name (acc ++ "c") c ++ toString us.length ++ ";")
  | .lit (.natVal n) => return acc ++ "N" ++ toString n ++ ";"
  | .lit (.strVal s) => return netstr (acc ++ "T") s
  | .mdata _ e => expr ups acc e
  | .mvar _ => return if Erase.isProofMarker e then acc ++ "e" else acc ++ "?"
  | .fvar _ => return acc ++ "?"
  | _ =>
    if let some i := (← get)[e]? then return acc ++ "r" ++ toString i ++ ";"
    modify fun seen => seen.insert e seen.size
    match e with
    | .app f a => expr ups (← expr ups (acc ++ "a") f) a
    | .lam _ d b _ => expr ups (← expr ups (acc ++ "l") d) b
    | .forallE _ d b _ => expr ups (← expr ups (acc ++ "p") d) b
    | .letE _ t v b _ => expr ups (← expr ups (← expr ups (acc ++ "z") t) v) b
    | .proj s i e => expr ups (name (acc ++ "j") s ++ toString i ++ ";") e
    | _ => unreachable!

/-- The canonical printing of a closed term. -/
def print (ups : List Name) (e : Expr) : String := (expr ups "" e).run' {}

/-- Hex SHA-256 of the canonical printing of a term. -/
def exprHash (ups : List Name) (e : Expr) : String :=
  Sha256.hexOfString (print ups e)

/-- SHA-256 over a domain tag and a list of fields, each as `<len>:<bytes>`. -/
def hashFields (tag : String) (fields : List String) : String :=
  mkHash (Sha256.hexOfString (fields.foldl netstr (netstr "" tag)))

def optField : Option String → String
  | some s => netstr "+" s
  | none => "-"

/-- What enters `own` and `spec` for one constant. `status` compares them to charge `own-body`. -/
structure Fields where
  kind : Kind
  name : Name
  uparams : Nat
  /-- Hex hash of the canonical type, proofs erased. -/
  typeHash : String
  /-- Hex hash of the canonical body, proofs erased; `none` when no body is hashed
  (theorems, axioms, `opaque` and `partial` definitions, constructors, recursors). -/
  bodyHash : Option String
  safety : Safety
  deriving Inhabited, BEq

/-- `own(c) = H(kind, name, uparams, type, body, safety, informal-if-tagged)`, type and body with
proofs erased. -/
def own (f : Fields) (informal? : Option String) : String :=
  hashFields "leanblame.own.1"
    [toString f.kind, name "" f.name, toString f.uparams, f.typeHash, optField f.bodyHash,
     toString f.safety, optField informal?]

/-- `spec(c) = H(kind, name, uparams, type, informal-text)`. -/
def spec (f : Fields) (informal : String) : String :=
  hashFields "leanblame.spec.1"
    [toString f.kind, name "" f.name, toString f.uparams, f.typeHash, informal]

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
  hashFields "leanblame.claim.1" (ownHash :: deps.map (·.encode))

/-- A cycle hashed as one unit: members' own hashes (sorted by name), then the dependencies
outside the group (sorted by name). -/
def group (memberOwns : List String) (external : List DepEntry) : String :=
  hashFields "leanblame.group.1"
    (toString memberOwns.length :: memberOwns ++ external.map (·.encode))

/-- Each member's hash is the group hash plus its name. -/
def member (groupHash : String) (n : Name) : String :=
  hashFields "leanblame.member.1" [groupHash, name "" n]

end LeanBlame.Canon
