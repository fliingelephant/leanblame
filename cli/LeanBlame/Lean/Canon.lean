/-
Canonical printing of exported terms (docs/design/03-trust-model.md, "The hash,
precisely"). The Lean frontend hashes a type or a body as the SHA-256 of its
printing (docs/design/04-architecture.md, "Beyond Lean").

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
-/
import LeanBlame.Core.Hash
import LeanBlame.Lean.Erase

namespace LeanBlame.Canon

open Lean

/-- `n`, the components root first, `.`. -/
def name (acc : String) (n : Name) : String :=
  n.components.foldl (init := acc ++ "n") component ++ "."
where component (acc : String) : Name → String
  | .str _ s => Hash.netstr (acc ++ "s") s
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
  | .lit (.strVal s) => return Hash.netstr (acc ++ "T") s
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

end LeanBlame.Canon
