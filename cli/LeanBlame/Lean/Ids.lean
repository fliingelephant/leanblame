/-
`leanblame id [--lib NAME]...`: give each `@[trusted]` declaration of the library that has no id a new
one, written into its source as `@[trusted "id"]` (docs/design/02-concepts.md, "Id"). An id is a
random UUID, version 4. It is never hashed, so writing one changes no claim. Imported libraries are
not touched.

The attribute is found through Lean's declaration ranges: between the start of the declaration
(its docstring) and its name, outside comments and string literals, inside `@[…]`. A tag added
later by `attribute [trusted] X` is not there; the command prints the id to write by hand.
-/
import LeanBlame.Lean.Export

namespace LeanBlame.Ids

open Lean

/-- A new id: a random UUID, version 4 (RFC 9562). -/
def newId : IO String := do
  let b ← IO.getRandomBytes 16
  let b := (b.set! 6 ((b.get! 6 &&& 0x0f) ||| 0x40)).set! 8 ((b.get! 8 &&& 0x3f) ||| 0x80)
  let cs := (Sha256.toHex b).toList
  let group (start len : Nat) := String.ofList ((cs.drop start).take len)
  return s!"{group 0 8}-{group 8 4}-{group 12 4}-{group 16 4}-{group 20 12}"

/-- The index after the block comment that opens at `i` (docstrings too); comments nest. -/
def skipComment (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i + 2
  let mut depth := 1
  while j < cs.size && depth > 0 do
    if cs[j]! == '/' && cs[j + 1]? == some '-' then depth := depth + 1; j := j + 2
    else if cs[j]! == '-' && cs[j + 1]? == some '/' then depth := depth - 1; j := j + 2
    else j := j + 1
  return j

/-- The index after the string literal that opens at `i`. -/
def skipString (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i + 1
  while j < cs.size && cs[j]! != '"' do
    j := j + if cs[j]! == '\\' then 2 else 1
  return j + 1

/-- The index just after the attribute name `trusted` inside an `@[…]` between `start` and `stop`,
outside comments and string literals. -/
def findTrusted (cs : Array Char) (start stop : Nat) : Option Nat := Id.run do
  let mut i := start
  -- `[` nesting inside `@[…]`; 0 outside.
  let mut depth := 0
  while i < stop do
    let c := cs[i]!
    let next := cs[i + 1]?
    if c == '/' && next == some '-' then i := skipComment cs i
    else if c == '-' && next == some '-' then
      while i < stop && cs[i]! != '\n' do i := i + 1
    else if c == '"' then i := skipString cs i
    else if c == '@' && next == some '[' then depth := 1; i := i + 2
    else if depth > 0 && c == '[' then depth := depth + 1; i := i + 1
    else if depth > 0 && c == ']' then depth := depth - 1; i := i + 1
    else if depth > 0 && isIdFirst c then
      let mut j := i + 1
      while j < stop && (isIdRest cs[j]! || cs[j]! == '.') do j := j + 1
      if String.ofList (cs.extract i j).toList == "trusted" then return some j
      i := j
    else i := i + 1
  return none

/-- The character index of `pos` (line from 1, column in characters from 0) in `cs`. -/
def offsetOf (cs : Array Char) (pos : Position) : Nat := Id.run do
  let mut line := 1
  let mut i := 0
  while line < pos.line && i < cs.size do
    if cs[i]! == '\n' then line := line + 1
    i := i + 1
  return i + pos.column

/-- `cs` with each of `texts` inserted at the offset of the same index in `offsets`. -/
def insertAll (cs : Array Char) (offsets : Array Nat) (texts : Array String) : String := Id.run do
  let pairs := (offsets.zip texts).qsort (·.1 < ·.1)
  let mut out := ""
  let mut last := 0
  for (k, t) in pairs do
    out := out ++ String.ofList (cs.extract last k).toList ++ t
    last := k
  return out ++ String.ofList (cs.extract last cs.size).toList

def run (root : System.FilePath) (libsGiven : Array String) : IO UInt32 := do
  let l ← Export.load root libsGiven
  let own : NameSet := l.mods.foldl (·.insert ·) {}
  let missing ← (trustedDecls l.env).filterM fun (n, id) => do
    return id.isNone && own.contains (← IO.ofExcept (Export.moduleOf l.env n))
  if missing.isEmpty then
    IO.eprintln "leanblame: every tagged declaration of this library has an id"
    return 0
  let shown (f : System.FilePath) : String := ((f.toString.dropPrefix? (root.toString ++ "/")).map (·.copy)).getD f.toString
  -- Per source file: where to insert, and what.
  let mut edits : Std.HashMap System.FilePath (Array (Name × Nat × String)) := {}
  let mut texts : Std.HashMap System.FilePath (Array Char) := {}
  let mut problems := #[]
  for (n, _) in missing.qsort (·.1.cmp ·.1 == .lt) do
    let id ← newId
    let mod ← IO.ofExcept (Export.moduleOf l.env n)
    let some file ← Lean.SearchPath.findWithExt l.srcPath "lean" mod
      | problems := problems.push s!"{n}: cannot find the source of {mod}; write @[trusted \"{id}\"] by hand"
    let some r := declRangeExt.find? (level := .exported) l.env n <|> declRangeExt.find? (level := .server) l.env n
      | problems := problems.push s!"{n}: Lean has no source position for it; write @[trusted \"{id}\"] by hand"
    let cs ← match texts[file]? with
      | some cs => pure cs
      | none => pure (← IO.FS.readFile file).toList.toArray
    texts := texts.insert file cs
    let some k := findTrusted cs (offsetOf cs r.range.pos) (offsetOf cs r.selectionRange.pos)
      | problems := problems.push s!"{n}: no @[trusted] at {shown file}:{r.range.pos.line}; where it is tagged, write: trusted \"{id}\""
    edits := edits.insert file ((edits.getD file #[]).push (n, k, id))
  let mut written := #[]
  for (file, es) in edits do
    IO.FS.writeFile file (insertAll texts[file]! (es.map (·.2.1)) (es.map fun e => s!" \"{e.2.2}\""))
    written := written ++ es.map fun (n, _, id) => (n, id)
  for (n, id) in written.qsort (·.1.cmp ·.1 == .lt) do IO.println s!"{id} {n}"
  unless written.isEmpty do
    let files := (edits.toArray.map (shown ·.1)).qsort (· < ·)
    IO.eprintln s!"leanblame: wrote {written.size} ids into {", ".intercalate files.toList}; commit them"
  for p in problems do IO.eprintln p
  return if problems.isEmpty then 0 else 1

end LeanBlame.Ids
