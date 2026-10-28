/-
`leanblame id [--lib NAME]...`: give each tag written in the library without an id a new one,
written into its source just after `trusted`: `@[trusted "id"]` on a declaration, or `attribute
[trusted "id"] Name` for one tagged after the fact, also a declaration of another library
(docs/design/02-concepts.md, "Id"). An id is a random UUID, version 4. It is never hashed, so writing
one changes no claim. Tags written in imported libraries are not touched.

Where to write is where the attribute recorded that `trusted` ends (`Tag.pos`), in the module that
wrote the tag; the library was just built from that source.
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
  let missing := (tags l.env).filter fun (m, t) => t.id.isNone && own.contains m
  if missing.isEmpty then
    IO.eprintln "leanblame: every tagged declaration of this library has an id"
    return 0
  let shown (f : System.FilePath) : String := ((f.toString.dropPrefix? (root.toString ++ "/")).map (·.copy)).getD f.toString
  -- Per source file: where to insert, and what.
  let mut edits : Std.HashMap System.FilePath (Array (Name × Nat × String)) := {}
  let mut texts : Std.HashMap System.FilePath (Array Char) := {}
  let mut problems := #[]
  for (m, t) in missing.qsort (·.2.decl.cmp ·.2.decl == .lt) do
    let (n, id) := (t.decl, ← newId)
    let some file ← Lean.SearchPath.findWithExt l.srcPath "lean" m
      | problems := problems.push s!"{n}: cannot find the source of {m}; write trusted \"{id}\" by hand"
    let some pos := t.pos
      | problems := problems.push s!"{n}: its tag in {m} has no source position; write trusted \"{id}\" by hand"
    let cs ← match texts[file]? with
      | some cs => pure cs
      | none => pure (← IO.FS.readFile file).toList.toArray
    texts := texts.insert file cs
    let k := offsetOf cs pos
    unless k ≥ 7 && String.ofList (cs.extract (k - 7) k).toList == "trusted" do
      problems := problems.push s!"{n}: no `trusted` at {shown file}:{pos.line}:{pos.column}; write trusted \"{id}\" there"
      continue
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
