/-
JSON helpers. `Lean.Json` keeps object keys sorted, so output goes through
`OJson`, which keeps fields in the order the schemas in docs/14 list them.
Input is parsed with `Lean.Json`, where order does not matter.
-/
import Lean.Data.Json

namespace LeanBlame

open Lean (Json)

/-- JSON with ordered object fields, for output. -/
inductive OJson where
  | null
  | num (n : Int)
  | str (s : String)
  | arr (xs : Array OJson)
  | obj (kvs : Array (String × OJson))
  deriving Inhabited

namespace OJson

def strs (xs : Array String) : OJson := .arr (xs.map .str)

def optStr : Option String → OJson
  | some s => .str s
  | none => .null

/-- A string map, keys in the given order. -/
def strMap (kvs : Array (String × String)) : OJson := .obj (kvs.map fun (k, v) => (k, .str v))

private def indentStr (n : Nat) : String := "".pushn ' ' n

/-- Render with two-space indentation and a trailing newline-free result. -/
partial def render (j : OJson) (indent : Nat := 0) : String :=
  match j with
  | .null => "null"
  | .num n => toString n
  | .str s => Json.renderString s
  | .arr xs =>
    if xs.isEmpty then "[]" else
      let inner := xs.toList.map fun x => indentStr (indent + 2) ++ render x (indent + 2)
      "[\n" ++ ",\n".intercalate inner ++ "\n" ++ indentStr indent ++ "]"
  | .obj kvs =>
    if kvs.isEmpty then "{}" else
      let inner := kvs.toList.map fun (k, v) =>
        indentStr (indent + 2) ++ Json.renderString k ++ ": " ++ render v (indent + 2)
      "{\n" ++ ",\n".intercalate inner ++ "\n" ++ indentStr indent ++ "}"

/-- Render followed by a newline: the exact bytes written to files. -/
def renderFile (j : OJson) : String := j.render ++ "\n"

end OJson

/-! Reading `Lean.Json` with error messages that name the field. -/

namespace JsonRead

def obj (j : Json) (what : String) : Except String (Std.TreeMap.Raw String Json) :=
  match j with
  | .obj kvs => .ok kvs
  | _ => .error s!"{what}: expected an object"

def field (o : Std.TreeMap.Raw String Json) (k : String) (what : String) : Except String Json :=
  match o.get? k with
  | some v => .ok v
  | none => .error s!"{what}: missing field `{k}`"

def str (j : Json) (what : String) : Except String String :=
  match j with
  | .str s => .ok s
  | _ => .error s!"{what}: expected a string"

def arr (j : Json) (what : String) : Except String (Array Json) :=
  match j with
  | .arr xs => .ok xs
  | _ => .error s!"{what}: expected an array"

def strField (o : Std.TreeMap.Raw String Json) (k : String) (what : String) : Except String String := do
  str (← field o k what) s!"{what}.{k}"

/-- An object whose values are all strings, in key order. -/
def strMap (j : Json) (what : String) : Except String (Array (String × String)) := do
  let o ← obj j what
  o.toList.toArray.mapM fun (k, v) => do return (k, ← str v s!"{what}.{k}")

end JsonRead

end LeanBlame
