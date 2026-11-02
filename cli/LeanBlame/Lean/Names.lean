/-
Names read back from the form `Name.toString` prints.
-/
namespace LeanBlame

open Lean

/-- A name as `Name.toString` prints it, read back as Lean reads a name literal: as boundary lists
and blueprints name constants. -/
def constName? (s : String) : Option Name := Syntax.decodeNameLit ("`" ++ s)

/-- A name as `Name.toString` prints it (as `.ilean` files have them), read back; a component of
digits only is a number, as in private names. -/
def nameOf? (text : String) : Option Name :=
  (constName? text).map fix
where
  fix : Name → Name
    | .str p s => if !s.isEmpty && s.all Char.isDigit then .num (fix p) s.toNat! else .str (fix p) s
    | .num p k => .num (fix p) k
    | .anonymous => .anonymous

/-- Whether constant name `n` reads back from its printed form, as boundary lists name constants. -/
def roundTrips (n : Name) : Bool :=
  constName? n.toString == some n

end LeanBlame
