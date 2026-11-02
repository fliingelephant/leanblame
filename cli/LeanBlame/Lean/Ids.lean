/-
`leanblame id [--lib NAME]...`: give each tag written in the library without an id a new one,
written into its source just after `trusted`: `@[trusted "id"]` on a declaration, or `attribute
[trusted "id"] Name` for one tagged after the fact, also a declaration of another library
(trust-model.md, "Id"). An id is a random UUID, version 4. It is never hashed, so writing
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

def run (root : System.FilePath) (libsGiven : Array String) : IO UInt32 := do
  -- The tags are entries the modules hold, which need no environment extension loaded.
  let l ← Export.load root libsGiven (loadExts := false)
  let own : NameSet := l.mods.foldl (·.insert ·) {}
  let missing := (tags l.env).filter fun (m, t) => t.id.isNone && own.contains m
  if missing.isEmpty then
    IO.eprintln "leanblame: every tagged declaration of this library has an id"
    return 0
  let shown (f : System.FilePath) : String := ((f.toString.dropPrefix? (root.toString ++ "/")).map (·.copy)).getD f.toString
  -- Per source file: its text, and each tagged declaration with its id and where to insert it.
  let mut texts : Std.HashMap System.FilePath FileMap := {}
  let mut edits : Std.HashMap System.FilePath (Array (Name × String × String.Pos.Raw)) := {}
  let mut problems := #[]
  for (m, t) in missing.qsort (·.2.decl.cmp ·.2.decl == .lt) do
    let (n, id) := (t.decl, ← newId)
    let some file ← Lean.SearchPath.findWithExt l.srcPath "lean" m
      | problems := problems.push s!"{n}: cannot find the source of {m}; write trusted \"{id}\" by hand"
    let some pos := t.pos
      | problems := problems.push s!"{n}: its tag in {m} has no source position; write trusted \"{id}\" by hand"
    let text ← match texts[file]? with
      | some text => pure text
      | none => pure (FileMap.ofString (← IO.FS.readFile file))
    texts := texts.insert file text
    let k := text.ofPosition pos
    unless k.byteIdx ≥ 7 && String.Pos.Raw.extract text.source ⟨k.byteIdx - 7⟩ k == "trusted" do
      problems := problems.push s!"{n}: no `trusted` at {shown file}:{pos.line}:{pos.column}; write trusted \"{id}\" there"
      continue
    edits := edits.insert file ((edits.getD file #[]).push (n, id, k))
  let mut written := #[]
  for (file, es) in edits do
    let source := texts[file]!.source
    IO.FS.writeFile file <| Pieces.apply source.toUTF8 0 source.rawEndPos <|
      es.map fun (_, id, k) => { start := k, stop := k, text := s!" \"{id}\"" }
    written := written ++ es.map fun (n, id, _) => (n, id)
  for (n, id) in written.qsort (·.1.cmp ·.1 == .lt) do IO.println s!"{id} {n}"
  unless written.isEmpty do
    let files := (edits.toArray.map (shown ·.1)).qsort (· < ·)
    IO.eprintln s!"leanblame: wrote {written.size} ids into {", ".intercalate files.toList}; commit them"
  for p in problems do IO.eprintln p
  return if problems.isEmpty then 0 else 1

end LeanBlame.Ids
