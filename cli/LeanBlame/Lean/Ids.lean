/-
`leanblame id`: tag every declaration of the library, each with a new id (trust-model.md, "Id"). A
tag written without an id gets one, just after `trusted`: `@[trusted "id"]` on a declaration, or
`attribute [trusted "id"] Name` for one tagged after the fact, also a declaration of another
library. A declaration with no tag gets `attribute [trusted "id"] Name`, at the end of its module;
or, when a library `leanblame.toml` lists declares nothing, at the end of that library's last module
that imports it: a library one does not own is tagged in a library of one's own. A structure's
projections, an inductive's constructors and what Lean generates come with their parent, and a
deprecated alias with what it renames (`Export.taggable`). An id is a random
UUID, version 4. It is never hashed, so writing one changes no claim. Tags written in imported
libraries are not touched.

Where an id goes into a tag is where the attribute recorded that `trusted` ends (`Tag.pos`), in the
module that wrote the tag; the library was just built from that source.
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
  let l ← Export.load root libsGiven
  let own : NameSet := l.mods.foldl (·.insert ·) {}
  let found := tags l.env
  let missing := found.filter fun (m, t) => t.id.isNone && own.contains m
  let tagged : NameSet := found.foldl (fun s (_, t) => s.insert t.decl) {}
  let untagged := (← Export.taggableIn l.env l.mods).filter fun n =>
    !tagged.contains n && !l.env.isProjectionFn n && (l.env.getAuxParentProjectionInfo? n).isNone
  if missing.isEmpty && untagged.isEmpty then
    IO.eprintln "leanblame: every declaration of this library is tagged, with an id"
    return 0
  -- The modules of the listed libraries that declare nothing, each with the modules it imports.
  let libs ← Export.libraries (← Export.lakePackage root) libsGiven
  let declaresNothing (m : Name) := ((moduleData? l.env m).map (·.constNames.isEmpty)).getD false
  let holders := (libs.filter fun lib => (l.mods.filter lib.isLocalModule).all declaresNothing).flatMap
    fun lib => l.mods.filter lib.isLocalModule
  let sees : Array (Name × NameSet) := holders.reverse.map fun t =>
    (t, (Id.run <| reach #[t] fun x => pure (importsOf l.env x)).foldl (·.insert ·) {})
  let shown (f : System.FilePath) : String := ((f.toString.dropPrefix? (root.toString ++ "/")).map (·.copy)).getD f.toString
  let mut problems := #[]
  let mut sources : Std.HashMap Name System.FilePath := {}
  let mut texts : Std.HashMap System.FilePath FileMap := {}
  -- Per source file: each tag with its new id and where to insert it, and the tags to append.
  let mut edits : Std.HashMap System.FilePath (Array (Name × String × String.Pos.Raw)) := {}
  let mut appends : Std.HashMap System.FilePath (Array (Name × String)) := {}
  let mut files : Array System.FilePath := #[]
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
    unless files.contains file do files := files.push file
    edits := edits.insert file ((edits.getD file #[]).push (n, id, k))
  for n in untagged do
    let id ← newId
    let some m := moduleOf? l.env n | problems := problems.push s!"{n} is in no module"; continue
    let holder := if holders.isEmpty then some m else (sees.find? (·.2.contains m)).map (·.1)
    let some h := holder
      | problems := problems.push s!"{n}: no module of the library that declares nothing imports {m}"; continue
    let file ← match sources[h]? with
      | some f => pure (some f)
      | none => Lean.SearchPath.findWithExt l.srcPath "lean" h
    let some file := file
      | problems := problems.push s!"{n}: cannot find the source of {h}; write attribute [trusted \"{id}\"] {n} by hand"
    sources := sources.insert h file
    unless texts.contains file do texts := texts.insert file (FileMap.ofString (← IO.FS.readFile file))
    unless files.contains file do files := files.push file
    appends := appends.insert file ((appends.getD file #[]).push (n, id))
  let mut written := #[]
  for file in files do
    let source := texts[file]!.source
    let es := edits.getD file #[]
    let text := Pieces.apply source.toUTF8 0 source.rawEndPos <|
      es.map fun (_, id, k) => { start := k, stop := k, text := s!" \"{id}\"" }
    let added := appends.getD file #[]
    let block := added.foldl (fun acc (n, id) => acc ++ s!"attribute [trusted \"{id}\"] {n}\n") ""
    let text := if added.isEmpty then text
      else text ++ (if text.isEmpty || text.endsWith "\n" then "" else "\n") ++ "\n" ++ block
    IO.FS.writeFile file text
    written := written ++ es.map (fun (n, id, _) => (n, id)) ++ added
  for (n, id) in written.qsort (·.1.cmp ·.1 == .lt) do IO.println s!"{id} {n}"
  unless written.isEmpty do
    IO.eprintln s!"leanblame: wrote {written.size} ids into {", ".intercalate ((files.map shown).qsort (· < ·)).toList}; commit them"
  for p in problems do IO.eprintln p
  return if problems.isEmpty then 0 else 1

end LeanBlame.Ids
