/-
The statements of the boundary list (docs/design/14-schemas.md §1), printed in this process from the
environment `export` imports with the environment extensions of the library and its dependencies
(their notations and delaborators), as doc-gen4 renders signatures: each signature pretty-printed
with every constant reference tagged (`Widget.tagCodeInfos`) and flattened to segments. A reference
prints with its surrounding spaces (` + ` for `HAdd.hAdd`), which stay outside its segment;
`pp.tagAppFns` gives the head of an application a tag of its own, so it becomes a segment.
-/
import Lean
import LeanBlame.Core.Schema

namespace LeanBlame.Statements

open Lean Meta Widget

def constOf (i : SubexprInfo) : Option Name :=
  match i.info.val.info with
  | .ofTermInfo t => match t.expr.consumeMData with
    | .const n _ => some n
    | _ => none
  | _ => none

/-- The text directly under a tag belongs to the constant that tag refers to, if any: the name of a
constant, or the symbol of a notation whose head it is (` = ` for `Eq`). Nested tags decide for
their own text. -/
partial def flatten (cur : Option Name) : CodeWithInfos → Array Segment → Array Segment
  | .text s, acc =>
    match cur with
    | none => if s.isEmpty then acc else acc.push { text := s }
    | some n =>
      let chars := s.toList
      let lead := chars.takeWhile Char.isWhitespace
      let trail := (chars.reverse.takeWhile Char.isWhitespace).reverse
      let core := String.ofList ((chars.drop lead.length).take (chars.length - lead.length - trail.length))
      let acc := if lead.isEmpty then acc else acc.push { text := String.ofList lead }
      let acc := if core.isEmpty then acc else acc.push { text := core, const := some n.toString }
      if trail.isEmpty then acc else acc.push { text := String.ofList trail }
  | .append xs, acc => xs.foldl (fun acc x => flatten cur x acc) acc
  | .tag i t, acc => flatten (constOf i) t acc

def segments (c : Name) : MetaM (Array Segment) := do
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppSignature c
  let ctx : Elab.ContextInfo := {
    env := ← getEnv, fileMap := default, mctx := ← getMCtx, options := ← getOptions
    currNamespace := ← getCurrNamespace, openDecls := ← getOpenDecls, ngen := ← getNGen }
  let code ← tagCodeInfos ctx infos (TaggedText.prettyTagged fmt (w := 100))
  return flatten none code #[]

/-- The statements of `names`, in `env`; a printer error stops `export`. -/
def print (env : Environment) (names : Array Name) : IO (Array (Array Segment)) := do
  let opts := ({} : Options).setBool `pp.tagAppFns true
  let run : MetaM (Array (Array Segment)) := names.mapM segments
  let (out, _) ← (run.run' {} {}).toIO { fileName := "<statements>", fileMap := default, options := opts } { env }
  return out

end LeanBlame.Statements
