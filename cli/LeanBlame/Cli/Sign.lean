/-
`leanblame init` and `leanblame sign` (docs/04-architecture.md, docs/05-records.md).

`sign` is the terminal dev path: it writes `local:` records only. Provider
logins (OpenReview, ORCID, GitHub) belong to the sign server.
-/
import LeanBlame.Cli.Status

namespace LeanBlame.Sign

/-- The CI job `init` writes: `validate` on every pull request. -/
def ciWorkflow : String :=
  "# Written by `leanblame init`. Make this a required check.
# A pull request runs this job as the pull request changed it, with its own lakefile and
# leanblame.toml. Protect .github/, the lakefile, lake-manifest.json and leanblame.toml
# with CODEOWNERS and required reviews.
name: leanblame validate
on: pull_request
jobs:
  validate:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
      - name: Install elan
        run: |
          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
          echo \"$HOME/.elan/bin\" >> \"$GITHUB_PATH\"
      - name: Validate records (schema, authority, append-only)
        run: lake exe leanblame validate --base-ref \"origin/${{ github.base_ref }}\"
"

def init (root : System.FilePath) : IO UInt32 := do
  let report (what : String) (created : Bool) :=
    IO.println s!"{if created then "created" else "exists "}  {what}"
  let cfgPath := root / Config.fileName
  if ← cfgPath.pathExists then report Config.fileName false
  else
    IO.FS.writeFile cfgPath Config.defaultText
    report Config.fileName true
  let recordsDir := root / "records"
  if ← recordsDir.isDir then report "records/" false
  else
    IO.FS.createDirAll recordsDir
    report "records/" true
  let wf := root / ".github" / "workflows" / "leanblame.yml"
  if ← wf.pathExists then report ".github/workflows/leanblame.yml" false
  else
    writeFileMkdirs wf ciWorkflow
    report ".github/workflows/leanblame.yml" true
  -- The object store is local and large; keep it out of git.
  let gi := root / ".gitignore"
  let old := (← readFileIfExists gi).getD ""
  unless (strLines old).any (fun l => strTrim l == ".leanblame/" || strTrim l == "/.leanblame/") do
    let sep := if old.isEmpty || old.endsWith "\n" then "" else "\n"
    IO.FS.writeFile gi (old ++ sep ++ ".leanblame/\n")
    IO.println "updated  .gitignore (.leanblame/)"
  return 0

/-- `--signer`, else `$LEANBLAME_SIGNER`, else `local:$USER`. Only `local:` ids in this slice. -/
def resolveSigner (given? : Option String) : IO String := do
  let s ← match given? with
    | some s => pure s
    | none => do
      match ← IO.getEnv "LEANBLAME_SIGNER" with
      | some s => pure s
      | none => pure ("local:" ++ ((← IO.getEnv "USER").getD "dev"))
  unless isSignerId s do fail s!"signer must be provider:id, got `{s}`"
  unless s.startsWith "local:" do
    fail s!"{s}: the terminal writes local: records only; provider logins go through the sign server"
  return s

/-- The first local records directory: where new records go. -/
def recordsDir (root : System.FilePath) (cfg : Config) : IO System.FilePath := do
  let some d := (← recordDirs root cfg)[0]? | fail "leanblame.toml lists no local records directory"
  return d

/-- Write a record under its hash; returns the record id and the path. -/
def writeRecord (dir : System.FilePath) (r : Record) : IO (String × System.FilePath) := do
  let text := r.toToml
  let hex := Sha256.hexOfString text
  let path := dir / (hex ++ ".toml")
  IO.FS.createDirAll dir
  if ← path.pathExists then fail s!"{path} already exists"
  IO.FS.writeFile path text
  return (mkHash hex, path)

/-- Approve: one record per module, at the claim hashes of the current export. -/
def approve (root : System.FilePath) (signer? : Option String) (module? : Option String)
    (names : Array String) (note? : Option String) : IO UInt32 := do
  let cfg ← Config.load root
  let signer ← resolveSigner signer?
  let cur ← Store.readCurrent root
  let boundary ← Status.loadBoundary root cur.boundary
  let cache : Status.Cache ← IO.mkRef {}
  let hashed ← Status.hashed root cache cur.exportHash cur.boundary
  let claimOf : Std.HashMap String String :=
    (hashed.boundary.zip boundary.declarations).foldl (init := {}) fun m (n, d) =>
      m.insert d.name hashed.nodes[n]!.claim
  let selected ← if !names.isEmpty then
      names.mapM fun n => do
        match boundary.declarations.find? (·.name == n) with
        | some d => pure d
        | none => fail s!"{n} is not on the boundary list"
    else if let some m := module? then do
      let ds := boundary.declarations.filter (·.module == m)
      if ds.isEmpty then fail s!"no tagged declarations in module {m}"
      pure ds
    else
      -- Default: every tagged declaration of the library's own modules.
      pure <| boundary.declarations.filter (cur.modules.contains ·.module)
  if selected.isEmpty then fail "nothing to sign"
  let modules := selected.foldl (fun acc d => if acc.contains d.module then acc else acc.push d.module) #[]
  let dir ← recordsDir root cfg
  let date ← UtcTime.now
  for m in modules.qsort (· < ·) do
    let constants := (selected.filter (·.module == m)).map (fun d => (d.name, claimOf[d.name]!))
      |>.qsort (fun a b => a.1 < b.1)
    let r : Record := .approve {
      signer, date, module := m, commit := boundary.commit, toolchain := boundary.toolchain
      deps := boundary.deps, exportHash := cur.exportHash, boundary := cur.boundary
      constants, note := note? }
    let (id, path) ← writeRecord dir r
    IO.println s!"approve {id} {path} ({constants.size} constants of {m})"
  return 0

/-- Find a record by id (`sha256:<hex>` or `<hex>`) or by file path. -/
def findRecord (root : System.FilePath) (cfg : Config) (ref : String) : IO LoadedRecord := do
  let (all, _) ← loadAllRecords root cfg
  let id ← if isHash ref then pure ref
    else if isHexDigest ref then pure (mkHash ref)
    else if ← (System.FilePath.mk ref).pathExists then
      pure (sha256OfBytes (← IO.FS.readBinFile ref))
    else fail s!"{ref}: not a record id or file"
  match all.find? (·.hash == id) with
  | some r => return r
  | none => fail s!"no record {id} in the records directories"

/-- Withdraw some or all constants of one of your approve records. -/
def withdraw (root : System.FilePath) (signer? : Option String) (ref : String)
    (constants? : Option (Array String)) (note? : Option String) : IO UInt32 := do
  let cfg ← Config.load root
  let signer ← resolveSigner signer?
  let target ← findRecord root cfg ref
  let .approve a := target.record | fail s!"{target.hash} is a withdraw; only approve records can be withdrawn"
  unless a.signer == signer do
    fail s!"{target.hash} was signed by {a.signer}; only its signer can withdraw it (pass --signer)"
  if let some cs := constants? then
    for c in cs do
      unless a.constants.any (·.1 == c) do fail s!"{c} is not in record {target.hash}"
  let r : Record := .withdraw {
    signer, date := ← UtcTime.now, refersTo := target.hash, constants := constants?, note := note? }
  let (id, path) ← writeRecord (← recordsDir root cfg) r
  IO.println s!"withdraw {id} {path} (refers to {target.hash})"
  return 0

end LeanBlame.Sign
