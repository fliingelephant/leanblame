/-
Sorried copies (docs/design/04-architecture.md, "Sorried copies"): each of the library's modules with
the proofs of its theorems replaced by `sorry`. A comparator challenge for some theorems carries the
copies of the modules they need and requires what the library requires, not the library.

A proof stays when the type of a library constant or the value of a library definition reaches its
theorem, or something its elaboration made, such as a matcher (`kept`): with `sorry` there, `sorryAx`
would reach every proof of a statement that uses that definition, and the comparator would refuse
them all; without what the proof made, the definition would not be the same.

`export` makes the copies with `SorriedScript`: one `lean --run` per module, as many at once as the
machine has hardware threads. Each copy is stored as `sorried/<key hex>.json`; the key hashes the
script, the module, Lake's hash of everything the module's build depends on (`depHash`), its Lean
options and the proofs it keeps, so a module whose key is stored is not copied again. Each copy is
checked against the module's `.olean` by the script; then a reference from what a copy keeps (every
type, every definition, every kept proof) to a constant that another module's copy lacks is an
error, since the copies would not build together.
-/
import Lean
import LeanBlame.Core.Store
import LeanBlame.Lean.SorriedScript

namespace LeanBlame.Sorried

open Lean

/-- The script `export` runs, with the `main` that `lean --run` calls. -/
def script : String :=
  (include_str "SorriedScript.lean") ++
    "\nunsafe def main (args : List String) : IO UInt32 := LeanBlameSorried.main args\n"

/-- Where Lean's declaration ranges put `n` in its source, as `Ids` and the copies need. -/
def declRange? (env : Environment) (n : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .exported) env n <|> declRangeExt.find? (level := .server) env n

/-- The theorem of `own` whose proof made `n`, when `n` is an auxiliary constant (a matcher, an
auxiliary lemma) named under it: Lean names what it makes while elaborating a declaration after that
declaration. -/
def madeBy? (own : Std.HashMap Name ConstantInfo) (n : Name) : Option Name :=
  if n.isInternalDetail then go n.getPrefix else none
where
  go : Name → Option Name
    | .anonymous => none
    | p@(.str q _) | p@(.num q _) => match own[p]? with
      | some ci => if ci.isTheorem then some p else none
      | none => go q

/-- The theorems of `own` whose proofs the copies keep: those that the type of a constant of `own`
or the value of a definition of `own` reaches, those whose proofs made what these reach, and what
their proofs reach. -/
def kept (own : Std.HashMap Name ConstantInfo) : NameSet := Id.run do
  let mut todo : Array Name := #[]
  for (n, ci) in own do
    -- What a proof made exists only with that proof, so it counts only when reached.
    if (madeBy? own n).isSome then continue
    todo := todo ++ ci.type.getUsedConstants
    unless ci.isTheorem do
      if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
  let mut seen : NameSet := {}
  let mut keep : NameSet := {}
  repeat
    let some n := todo.back? | break
    todo := todo.pop
    if seen.contains n then continue
    let some ci := own[n]? | continue
    seen := seen.insert n
    if ci.isTheorem then keep := keep.insert n
    todo := todo ++ ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    if let some m := madeBy? own n then todo := todo.push m
  return keep

/-- What a copy keeps of the constant `n`: its type and, unless it is a theorem whose proof is
not kept, its value. -/
def keptUses (keep : NameSet) (n : Name) (ci : ConstantInfo) : Array Name :=
  let value := if ci.isTheorem && !keep.contains n then none else ci.value? (allowOpaque := true)
  ci.type.getUsedConstants ++ (value.map (·.getUsedConstants)).getD #[]

/-- A stored copy: the module's source with proofs replaced by `sorry`, and the module's constants
that the copy lacks, other than those Lean makes again on demand. -/
structure Copy where
  module : String
  text : String
  missing : Array String

def Copy.schemaId : String := "leanblame.sorried.1"

instance : ToJson Copy where
  toJson c := Json.mkObj [("schema", Copy.schemaId), ("module", c.module), ("text", c.text),
    ("missing", toJson c.missing)]

def Copy.fromJson? (j : Json) : Except String Copy := do
  let o ← JsonObj.read j "sorried copy" ["schema", "module", "text", "missing"]
  o.schema Copy.schemaId
  return { module := ← o.get String "module", text := ← o.get String "text",
           missing := ← o.get (Array String) "missing" }

def path (root : System.FilePath) (key : String) : System.FilePath :=
  Store.kindDir root .sorried / s!"{hashHex key}.json"

def read (root : System.FilePath) (key : String) : IO Copy := do
  let p := path root key
  match Json.parse (← IO.FS.readFile p) >>= Copy.fromJson? with
  | .ok c => return c
  | .error e => fail s!"{p}: {e}"

/-- What the script needs to copy one module, and the key of the copy. -/
structure Job where
  module : Name
  source : System.FilePath
  olean : System.FilePath
  /-- Where the theorems whose proofs stay begin: line and column. -/
  keep : Array (Nat × Nat)
  keepNames : Array Name
  options : Json
  key : String

/-- Copy one module with the library's `lean`, whose search path is `leanPath`; a problem the
script reports is an error. -/
def runJob (root lean scriptFile : System.FilePath) (leanPath : String) (j : Job) : IO Copy := do
  let input ← Store.tmpPath root s!"sorried-{j.module}-in"
  let out ← Store.tmpPath root s!"sorried-{j.module}-out"
  IO.FS.writeFile input (Json.mkObj [("module", toString j.module), ("source", j.source.toString),
    ("olean", j.olean.toString), ("keep", toJson j.keep), ("keep_names", toJson (j.keepNames.map toString)),
    ("options", j.options), ("out", out.toString)]).compress
  let r ← IO.Process.output { cmd := lean.toString, args := #["--run", scriptFile.toString, input.toString],
                              cwd := root, env := #[("LEAN_PATH", some leanPath)] }
  let text? ← readFileIfExists out
  for f in [input, out] do
    if ← f.pathExists then IO.FS.removeFile f
  let some text := text?
    | fail s!"{j.module}: copying failed (exit {r.exitCode}):\n{r.stdout}{r.stderr}"
  let o ← IO.ofExcept (Json.parse text >>= (JsonObj.read · s!"{j.module}: the script's output" ["text", "problems", "missing"]))
  let problems ← IO.ofExcept (o.get (Array String) "problems")
  unless problems.isEmpty do
    fail s!"{j.module}: the copy differs from the library:\n{"\n".intercalate problems.toList}"
  return { module := toString j.module, text := ← IO.ofExcept (o.get String "text"),
           missing := ← IO.ofExcept (o.get (Array String) "missing") }

/-- `f` on each of `xs`, at most `width` at a time, each result in its place. -/
def parallel (width : Nat) (xs : Array α) (f : α → IO β) : IO (Array (Except IO.Error β)) := do
  let next ← IO.mkRef 0
  let results ← IO.mkRef (Array.replicate xs.size (none : Option (Except IO.Error β)))
  let worker : IO Unit := do
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      let some x := xs[i]? | break
      let r ← (f x).toBaseIO
      results.modify (·.set! i (some r))
  let tasks ← (List.range (max 1 (min width xs.size))).mapM fun _ => IO.asTask worker .dedicated
  for t in tasks do
    if let .error e ← IO.wait t then throw e
  (← results.get).mapM fun
    | some r => pure r
    | none => fail "a copy was never made"

/-- From one `lake query`: Lake's hash of everything each module's build depends on, and each
module's Lean options, from the setup of its library's first module (Lake gives every module of a
library the same). -/
def lakeFacts (root : System.FilePath) (byLib : Array (String × Array Name)) :
    IO (Std.HashMap Name String × Std.HashMap Name Json) := do
  let mods := dedup (byLib.flatMap (·.2))
  let libs := byLib.filter (!·.2.isEmpty)
  let firsts := libs.map (·.2[0]!)
  let targets := mods.map (fun m => s!"+{m}:depHash") ++ firsts.map (fun m => s!"+{m}:setup")
  let out ← IO.Process.run { cmd := "lake", args := #["query", "--json"] ++ targets, cwd := root }
  let lines := (out.lines.toArray.map (·.copy)).filter (!·.trimAscii.isEmpty)
  unless lines.size == mods.size + firsts.size do
    fail s!"`lake query` gave {lines.size} answers for {mods.size + firsts.size} questions"
  let mut hashes : Std.HashMap Name String := {}
  for m in mods, line in lines do
    let .ok (.str h) := Json.parse line | fail s!"`lake query +{m}:depHash`: {line}"
    hashes := hashes.insert m h
  let mut options : Std.HashMap Name Json := {}
  for (_, ms) in libs, line in lines.extract mods.size lines.size do
    let some o := (Json.parse line).toOption.bind (·.getObjVal? "options" |>.toOption)
      | fail s!"`lake query +{ms[0]!}:setup` has no options"
    for m in ms do
      unless options.contains m do options := options.insert m o
  return (hashes, options)

/-- The library's modules (`byLib`, per library) with their sorried copies, made with the library's
`lean` (`sysroot`, `leanPath`) or found in the store, and checked to build together. `own` holds the
constants the library defines, `srcPath` where their sources are. -/
def make (root : System.FilePath) (env : Environment) (byLib : Array (String × Array Name))
    (own : Std.HashMap Name ConstantInfo) (srcPath : SearchPath) (sysroot : System.FilePath)
    (leanPath : String) : IO (Array OwnModule) := do
  let mods := dedup (byLib.flatMap (·.2))
  let ownMods : NameSet := mods.foldl (·.insert ·) {}
  let keep := kept own
  let moduleName (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).bind fun i => env.header.modules[i.toNat]?.map (·.module)
  let mut keeps : NameMap (Array (Nat × Nat) × Array Name) := {}
  for n in keep do
    let some m := moduleName n | fail s!"{n} is in no module"
    let (ps, ns) := (keeps.find? m).getD (#[], #[])
    let ps := match declRange? env n with
      | some r => ps.push (r.range.pos.line, r.range.pos.column)
      | none => ps
    keeps := keeps.insert m (ps, ns.push n)
  let (hashes, options) ← lakeFacts root byLib
  let mut jobs := #[]
  for m in mods do
    let some source ← srcPath.findWithExt "lean" m | fail s!"cannot find the source of {m}"
    let (keepAt, keepNames) := (keeps.find? m).getD (#[], #[])
    let keepAt := keepAt.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
    let keepNames := keepNames.qsort Name.quickLt
    let some depHash := hashes[m]? | fail s!"Lake gave no depHash for {m}"
    let some opts := options[m]? | fail s!"Lake gave no options for {m}"
    let key := mkHash <| Sha256.hexOfString <| script ++ "\n" ++ (Json.mkObj [("module", toString m),
      ("dep_hash", depHash), ("options", opts), ("keep", toJson keepAt),
      ("keep_names", toJson (keepNames.map toString))]).compress
    jobs := jobs.push { module := m, source, olean := ← findOLean m, keep := keepAt, keepNames, options := opts, key }
  let todo ← jobs.filterM fun j => return !(← (path root j.key).pathExists)
  unless todo.isEmpty do
    IO.eprintln s!"leanblame: copying {todo.size} of {jobs.size} modules with proofs replaced by sorry"
    let scriptFile ← Store.tmpPath root "sorried.lean"
    IO.FS.writeFile scriptFile script
    let width := (System.Platform.Internal.getHardwareConcurrency ()).toNat
    let made ← parallel width todo (runJob root (sysroot / "bin" / "lean") scriptFile leanPath)
    IO.FS.removeFile scriptFile
    let mut errors := #[]
    for j in todo, r in made do
      match r with
      | .ok c => writeFileMkdirs (path root j.key) (jsonText c)
      | .error e => errors := errors.push (toString e)
    unless errors.isEmpty do fail ("export failed:\n" ++ "\n".intercalate errors.toList)
  let mut out := #[]
  let mut missing : NameSet := {}
  for j in jobs do
    let c ← read root j.key
    unless c.module == toString j.module do fail s!"{path root j.key}: a copy of {c.module}, not {j.module}"
    for n in c.missing do
      let some n := Syntax.decodeNameLit ("`" ++ n) | fail s!"{path root j.key}: not a name: {n}"
      missing := missing.insert n
    let imports := match env.getModuleIdx? j.module >>= (env.header.moduleData[·.toNat]?) with
      | some d => dedup (d.imports.filterMap fun i => if ownMods.contains i.module then some (toString i.module) else none)
      | none => #[]
    out := out.push { name := toString j.module, imports, key := j.key, text := mkHash (Sha256.hexOfString c.text) }
  unless missing.isEmpty do
    let mut problems := #[]
    for (n, ci) in own do
      if missing.contains n then continue
      for u in keptUses keep n ci do
        if missing.contains u && moduleName u != moduleName n then
          problems := problems.push s!"{n} uses {u}, which the copy of {(moduleName u).getD .anonymous} lacks"
    unless problems.isEmpty do
      fail ("the sorried copies would not build together:\n" ++ "\n".intercalate (problems.qsort (· < ·)).toList)
  return out

end LeanBlame.Sorried
