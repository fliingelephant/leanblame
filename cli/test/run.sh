#!/usr/bin/env bash
# End-to-end test of the leanblame CLI on test/Sample.
#
#   cli/test/run.sh            # from anywhere; needs elan (Lean 4.35.0), git, python3
#
# Copies the sample library to a scratch directory, makes it a git repository,
# and walks through: init -> export -> sign (records name declarations by id) ->
# status (valid; --json complete, nothing on stderr) -> challenge (the commands the
# named theorems need and nothing else, @[trusted] dropped, the theorems with proofs
# `sorry`, the library's Lean options; Lake builds it without the library; the
# piece graph cuts to the same files; the check finds it means what the library
# means, and finds a changed body; a tagged definition that uses a theorem brings
# its proof, so the two cannot be named together; a private one keeps its meaning,
# an `open` of a namespace nothing needed is declared first) -> release -> edit a body ->
# status (outdated, own-body) -> stored files read strictly; causes unknown
# without the signed export -> edit a dependency body -> status (blocked) -> more
# causes (untagged, own-text, dep-spec) -> diff since the first sign-off (the
# causes status gives, both docstrings, --json; a missing export, an unknown name
# and a withdraw record refused) -> withdraw -> status (withdrawn) ->
# exclude (a withdraw record, no record, an approve record) -> blame -> validate
# (and its append-only check) -> a boundary list from a verso-blueprint manifest,
# labels as ids -> equiv, in a copy made after the first signoff: a definitional
# change proven (evidence shown by status, the record carries the proof, valid),
# one that is not definitional, an own-body change refused -> ids, in another
# copy made after the first signoff: a rename keeps the id and the history (diff
# matches it by id), blame by id, a new id is a new declaration (diff: added and removed), a shared id and a malformed one refused
# -> tags written after the fact, `attribute [trusted] Name` in a library of their own: id writes
# into the attribute, a second tag refused, a rename with a deprecated alias followed with the id
# kept, a rename without one a build error.
# Before the first export, `id` writes the ids (export refuses a tag without
# one); after the first body edit, status fails out loud when a signed graph is
# missing or broken. Also out loud: export outside git, sign without --signer, a
# remote records repository, a file in records/ that is not a record; an export
# of uncommitted changes names no commit, so sign and release refuse it. Logs go
# to a directory outside the library.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cli="$(cd "$here/.." && pwd)"

pass=0
fail() { echo "FAIL: $*" >&2; echo "work directories kept: $work $logs" >&2; exit 1; }
ok() { pass=$((pass + 1)); echo "  ok: $*"; }

echo "== build leanblame"
(cd "$cli" && lake build) >/dev/null
lb="$cli/.lake/build/bin/leanblame"
(cd "$cli" && lake env lean --run test/Canon.lean) || fail "canonical printing (test/Canon.lean)"
ok "canonical printing is linear in the term as a graph"

work="$(mktemp -d "${TMPDIR:-/tmp}/leanblame-test.XXXXXX")"
# Outside the library: a file in the library would make every export one of uncommitted changes.
logs="$work-logs"
mkdir "$logs"
cp -R "$here/Sample/Sample" "$here/Sample/Sample.lean" "$here/Sample/lean-toolchain" "$work/"
# Point the dependency on the attribute at this checkout.
sed "s|path = \"../..\"|path = \"$cli\"|" "$here/Sample/lakefile.toml" > "$work/lakefile.toml"
cd "$work"
printf '/.lake/\n' > .gitignore
git init -q
git config user.name "LeanBlame test"
git config user.email "test@example.invalid"
commit() { git add -A && git commit -qm "$1"; }

# Run a leanblame command; its stdout goes to $out, its stderr to stderr.log.
run() { out="$("$lb" "$@" 2>>"$logs/stderr.log")" || { tail -20 "$logs/stderr.log" >&2; fail "leanblame $*"; }; }
# Assert that the status line of a declaration is exactly the given text.
expect_line() {
  local name="$1" want="$2" got
  got="$(grep "^$name " <<<"$out" || true)"
  [[ "$got" == "$want" ]] || fail "status line for $name: want '$want', got '$got'"
  ok "$want"
}
export_lib() { "$lb" export >/dev/null 2>"$logs/export.log" || { cat "$logs/export.log" >&2; fail "export"; }; }
# Edit a file in place with a sed expression.
edit() { sed -i.bak "$2" "$1" && rm "$1.bak"; }
# Run a command that must fail, and whose output (stdout and stderr) must match every pattern.
must_fail() {
  local patterns=()
  while [[ "$1" != "--" ]]; do patterns+=("$1"); shift; done
  shift
  if "$@" >"$logs/fail.log" 2>&1; then fail "should have failed: $*"; fi
  for p in "${patterns[@]}"; do
    grep -q -- "$p" "$logs/fail.log" || fail "$*: no '$p' in: $(cat "$logs/fail.log")"
  done
}
current_export() { python3 -c 'import json; print(json.load(open(".leanblame/current"))["export"])'; }

echo "== init"
run init
must_fail "not a git repository with commits" -- "$lb" export
ok "export outside a git repository with commits is an error"
for f in leanblame.toml records; do
  [[ -e "$f" ]] || fail "init did not create $f"
done
grep -qx ".leanblame/" .gitignore || fail "init did not ignore .leanblame/"
grep -qx "/.lake/" .gitignore || fail "init dropped the existing .gitignore entries"
ok "init created leanblame.toml, records/, .gitignore entry"
commit "sample library"

echo "== id: a random id per tagged declaration, written into its source"
must_fail "Sample.energy: tagged without an id; run" -- "$lb" export
ok "export refuses a tag without an id"
run id
ids="$out"
[[ "$(grep -cE '^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12} Sample\.' <<<"$ids")" -eq 8 ]] \
  || fail "id: want 8 version-4 UUIDs, one per @[trusted]: $ids"
id_of() { awk -v n="$1" '$2 == n {print $1}' <<<"$ids"; }
energy_id="$(id_of Sample.energy)"
grep -qF "@[trusted \"$energy_id\"] def energy" Sample/Basic.lean || fail "id: not written into the source"
ok "id wrote 8 random ids into the sources, e.g. @[trusted \"$energy_id\"] def energy"
"$lb" id >"$logs/id.log" 2>&1 || fail "id, second run: $(cat "$logs/id.log")"
grep -q "every tagged declaration of this library has an id" "$logs/id.log" || fail "id, second run: $(cat "$logs/id.log")"
ok "a second run writes nothing"
commit "ids"

echo "== export"
export_lib
[[ "$(current_export)" =~ ^sha256:[0-9a-f]{64}$ ]] || fail "no current export"
first_export="$(current_export)"
ok "export stored $first_export"
must_fail "Sample.energy unsigned" "Sample.one_site_pos unsigned" "11 of 11 tagged declarations are not valid" \
  -- "$lb" release --tag 2026.10
ok "release refuses unsigned declarations and names them"

echo "== sign"
must_fail "sign needs --signer local:NAME" -- "$lb" sign
ok "sign without --signer is an error"
run sign --signer local:alice --note "first review"
[[ "$(grep -c '^approve ' <<<"$out")" == 2 ]] || fail "expected one approve record per module: $out"
basic_record="$(awk '/of Sample.Basic\)$/ {print $2}' <<<"$out")"
energy_record="$(awk '/of Sample.Energy\)$/ {print $2}' <<<"$out")"
ok "two approve records, Sample.Basic is $basic_record"
grep -qF "\"$(id_of Sample.Point)/x\" = {name = \"Sample.Point.x\", claim = \"sha256:" "records/${basic_record#sha256:}.toml" \
  || fail "the record does not name Sample.Point.x by its structure's id: $(cat "records/${basic_record#sha256:}.toml")"
grep -qF "$energy_id = {name = \"Sample.energy\", claim = \"sha256:" "records/${basic_record#sha256:}.toml" \
  || fail "the record does not name Sample.energy by its id: $(cat "records/${basic_record#sha256:}.toml")"
ok "records name declarations by id; a field by its structure's id and its name: $(id_of Sample.Point)/x"
run validate
ok "validate: $out"
commit "first signoff"
work_equiv="$work-equiv"
cp -R "$work" "$work_equiv"
work_id="$work-id"
cp -R "$work" "$work_id"

echo "== status: everything valid"
out="$("$lb" status 2>"$logs/status.err")"
for n in Sample.Point Sample.Point.mk Sample.Point.x Sample.Point.y Sample.Point.norm \
         Sample.energy Sample.energy_even Sample.energy_pos Sample.one_site_pos Sample.pointEnergy \
         Sample.second_site; do
  expect_line "$n" "$n valid"
done
want="warning: untagged Sample.double of this library is used by tagged Sample.energy; tag it so it gets its own signer"
grep -qxF "$want" "$logs/status.err" || fail "no untagged-dependency warning: $(cat "$logs/status.err")"
[[ "$(grep -c '^warning' "$logs/status.err")" == 1 ]] || fail "unexpected warnings: $(cat "$logs/status.err")"
ok "status warns that tagged Sample.energy uses untagged Sample.double, and nothing else"
"$lb" status --json >"$logs/status.json" 2>"$logs/status-json.err" || fail "status --json: $(cat "$logs/status-json.err")"
[[ ! -s "$logs/status-json.err" ]] || fail "status --json wrote to stderr: $(cat "$logs/status-json.err")"
python3 - "$logs/status.json" "$ids" <<'PY' || fail "status --json does not match docs/schemas.md"
import json, sys
s = json.load(open(sys.argv[1]))
ids = {name: i for i, name in (line.split() for line in sys.argv[2].splitlines())}
assert set(s) == {"library", "commit", "toolchain", "deps", "export", "boundary", "generated",
                  "standard_axioms", "declarations", "records", "untagged_in_library"}, set(s)
assert len(s["commit"]) == 40, s["commit"]
assert s["toolchain"].startswith("v4.") and s["deps"] == {}, (s["toolchain"], s["deps"])
assert s["standard_axioms"] == ["propext", "Classical.choice", "Quot.sound"], s["standard_axioms"]
assert s["untagged_in_library"] == [{"name": "Sample.double", "used_by": ["Sample.energy"]}], s["untagged_in_library"]
keys = {"name", "id", "parent", "module", "kind", "role", "informal", "statement", "claim", "state", "change", "signers",
        "history", "blocked_by", "proof", "evidence", "tagged_deps", "untagged_deps", "closure_size"}
members = {"Sample.Point.mk": "mk", "Sample.Point.x": "x", "Sample.Point.y": "y"}
order = [d["name"] for d in s["declarations"]]
assert order == ["Sample.energy", "Sample.Point", "Sample.Point.mk", "Sample.Point.x", "Sample.Point.y",
                 "Sample.Point.norm", "Sample.pointEnergy", "Sample.second_site", "Sample.energy_even",
                 "Sample.energy_pos", "Sample.one_site_pos"], order
decls = {d["name"]: d for d in s["declarations"]}
kinds = {n: d["kind"] for n, d in decls.items()}
assert kinds == {"Sample.energy": "def", "Sample.Point": "structure", "Sample.Point.mk": "constructor",
                 "Sample.Point.x": "field", "Sample.Point.y": "field", "Sample.Point.norm": "def",
                 "Sample.pointEnergy": "def", "Sample.second_site": "theorem", "Sample.energy_even": "theorem",
                 "Sample.energy_pos": "axiom", "Sample.one_site_pos": "theorem"}, kinds
for name, d in decls.items():
    assert set(d) == keys, (name, set(d) ^ keys)
    assert d["state"] == "valid" and d["signers"] == ["local:alice"] and d["change"] == [], name
    want_id = ids["Sample.Point"] + "/" + members[name] if name in members else ids[name]
    assert d["id"] == want_id, (name, d["id"])
    assert d["parent"] == ("Sample.Point" if name in members else None), (name, d["parent"])
    want = {"Sample.energy_even": "open", "Sample.second_site": "proven",
            "Sample.one_site_pos": "proven"}.get(name, "n/a")
    assert d["proof"]["status"] == want and d["proof"]["unpermitted"] == [], (name, d["proof"])
    h = d["history"]
    assert len(h) == 1 and h[0]["action"] == "approve" and h[0]["claim"] == d["claim"], (name, h)
    assert h[0]["name"] == name and h[0]["standing"] == "current", (name, h)
assert decls["Sample.energy_even"]["tagged_deps"] == ["Sample.energy"]
assert {"name": "Sample.double", "module": "Sample.Basic"} in decls["Sample.energy"]["untagged_deps"]
text = lambda segs: "".join(seg["text"] for seg in segs)
even = decls["Sample.energy_even"]["statement"]
assert text(even["pretty"]) == "Sample.energy_even (n : Nat) : Sample.energy n % 2 = 0", text(even["pretty"])
assert "HMod.hMod" in text(even["plain"]), text(even["plain"])
assert {"const": "Sample.energy", "text": "Sample.energy"} in even["pretty"], even["pretty"]
assert all(set(seg) == {"text", "const"} for seg in even["pretty"] + even["plain"]), even
assert text(decls["Sample.energy"]["statement"]["pretty"]) == "Sample.energy (n : Nat) : Nat"
assert decls["Sample.energy_even"]["proof"]["axioms"] == ["sorryAx"]
assert decls["Sample.one_site_pos"]["proof"]["axioms"] == ["Sample.energy_pos"]
assert decls["Sample.energy"]["role"] == "defined"
assert decls["Sample.energy_even"]["role"] == "proved"
assert decls["Sample.energy_pos"]["role"] == "assumed"
records = s["records"]
assert len(records) == 2 and all(r["action"] == "approve" and r["signer"] == "local:alice" for r in records), records
basic = next(r for r in records if r["module"] == "Sample.Basic")
assert basic["path"] == "records/" + basic["record"][len("sha256:"):] + ".toml", basic["path"]
assert {c["name"] for c in basic["constants"]} == {"Sample.energy", "Sample.Point", "Sample.Point.mk", "Sample.Point.x",
                                                  "Sample.Point.y", "Sample.Point.norm"}, basic["constants"]
assert all(set(c) == {"id", "name", "claim", "evidence"} and c["evidence"] is None for c in basic["constants"])
PY
ok "status --json has the docs/schemas.md fields and nothing on stderr; members' ids come from their structure's"

echo "== challenge: what a comparator checks a solution against"
must_fail "a challenge states theorems: name at least one" -- "$lb" challenge --out "$work-base"
run challenge Sample.energy_even "$(id_of Sample.second_site)" --out "$work-challenge"
python3 - "$work-challenge" <<'PY' || fail "challenge: not the commands the theorems need"
import sys
d = sys.argv[1]
deps, chal = open(f"{d}/ChallengeDeps.lean").read(), open(f"{d}/Challenge.lean").read()
lake, toolchain = open(f"{d}/lakefile.toml").read(), open(f"{d}/lean-toolchain").read()
# What the theorems need, as written, in a section of its module's own; `Point` through the
# `variable` of the theorems' scope.
for kept in ["def double (n : Nat) : Nat := n + n", "def energy (n : Nat) : Nat := double n", "structure Point where"]:
    assert kept in deps, (kept, deps)
for left in ["trusted", "two_pos", "def two", "theorem", "import", "Point.norm", "pointEnergy", "energy_pos", "noncomputable"]:
    assert left not in deps, (left, deps)
assert deps.count("section\n") == 1 and deps.rstrip().endswith("end Sample\n\nend"), deps
# Each module's section sets the Lean options Lake builds the module with; the lakefile sets none.
for opt in ["set_option autoImplicit false", "set_option relaxedAutoImplicit false"]:
    assert deps.count(opt) == 1 and chal.count(opt) == 1, (opt, deps, chal)
# The theorems named, proofs sorry, among the scope commands of their module, closed.
assert "theorem energy_even (n : Nat) : energy n % 2 = 0 := sorry" in chal, chal
assert "theorem second_site : (⟨2, by decide⟩ : Fin 3).val = 2 := sorry" in chal, "a proof inside a statement stays"
assert chal.startswith("import ChallengeDeps\n") and "variable (q : Point)" in chal, chal
assert chal.rstrip().endswith("end Sample\n\nend\n\nend"), chal
assert "one_site_pos" not in chal and chal.count(":= sorry") == 2, chal
assert "leanOptions" not in lake and "require" not in lake, lake
assert toolchain.startswith("leanprover/lean4:v4."), toolchain
PY
(cd "$work-challenge" && lake build) >"$logs/challenge.log" 2>&1 || fail "Lake does not build the challenge: $(cat "$logs/challenge.log")"
ok "challenge writes what the theorems named (by name or id) need and nothing else, the theorems with proofs sorry, each module with its Lean options; Lake builds it"
run challenge --graph
printf '%s' "$out" >"$logs/graph.json"
python3 - "$work-challenge" "$logs/graph.json" <<'PY' || fail "challenge --graph: the cut of its graph is not the challenge"
import json, sys
g = json.load(open(sys.argv[2]))["pieces"]
assert all(set(p) == {"file", "text", "needs", "theorem", "problem"} for p in g), g[0]
assert all(n < len(g) for p in g for n in p["needs"]), "a piece needs a piece the graph lacks"
statements = {p["theorem"]: i for i, p in enumerate(g) if p["file"] == "Challenge.lean" and p["theorem"]}
assert set(statements) == {"Sample.second_site", "Sample.energy_even", "Sample.one_site_pos"}, statements
held, todo = set(), [statements["Sample.energy_even"], statements["Sample.second_site"]]
while todo:
    i = todo.pop()
    if i not in held:
        held.add(i)
        todo += g[i]["needs"]
assert not any(g[i]["problem"] for i in held), [g[i]["problem"] for i in held]
for f in ["lakefile.toml", "lean-toolchain", "ChallengeDeps.lean", "Challenge.lean"]:
    cut = "".join(g[i]["text"] for i in sorted(held) if g[i]["file"] == f)
    assert cut == open(f"{sys.argv[1]}/{f}").read(), (f, cut)
PY
ok "challenge --graph prints the piece graph: the statements, what they need and what that needs make the challenge"
run challenge --check "$work-challenge"
[[ "$out" == "challenge $work-challenge: the 7 tagged declarations it holds mean what the library's do" ]] || fail "check: $out"
ok "the check builds the challenge against the library: its 7 tagged declarations have the library's claims"
edit "$work-challenge/ChallengeDeps.lean" 's/def double (n : Nat) : Nat := n + n/def double (n : Nat) : Nat := 2 * n/'
must_fail "does not mean what the library means" "Sample.energy change=untagged:Sample.double" \
  "^  Sample.double: not definitionally equal$" -- "$lb" challenge --check "$work-challenge"
ok "a challenge whose helper differs fails the check, with the cause status would give and the kernel's answer"
edit "$work-challenge/ChallengeDeps.lean" 's/def double (n : Nat) : Nat := 2 \* n/def double (n : Nat) : Nat := Nat.add n n/'
run challenge --check "$work-challenge"
[[ "$out" == "challenge $work-challenge: the 7 tagged declarations it holds mean what the library's do, 1 of them by definitional equality" ]] \
  || fail "check: $out"
ok "a helper written differently, Nat.add n n for n + n, has another claim but passes: the kernel finds it definitionally equal"
must_fail "Sample.energy (def) is not a theorem: a challenge states theorems" -- "$lb" challenge Sample.energy --out "$work-challenge-x"
must_fail "exists; a challenge goes into a new directory" -- "$lb" challenge Sample.energy_even --out "$work-challenge"
ok "challenge refuses a declaration that is not a theorem, and a directory that exists"
python3 - <<'PY'
basic = open("Sample/Basic.lean").read()
open("Sample/Basic.lean", "w").write(basic.replace("\nend Sample", "\n/-- One less, or zero. -/\ndef down : Nat → Nat\n  | 0 => 0\n  | n + 1 => n\n\n"
    "/-- Zero, kept to this file. -/\nprivate def secret : Nat := 0\n\n"
    "namespace Extra\n/-- Nothing tagged uses this. -/\ndef unused : Nat := 0\nend Extra\n\n"
    "namespace More.Inner\n/-- Nor this. -/\ndef hidden : Nat := 0\nend Inner\n\n/-- Zero, in More. -/\ndef zero : Nat := secret\n\nend More\n\n"
    "namespace Far.Away\n/-- One, far away. -/\ndef one : Nat := 1\nend Far.Away\n\nend Sample"))
energy = open("Sample/Energy.lean").read()
at = energy.index("/-- The energy of a point")
energy = (energy[:at] + "open Extra\n\n/-- Zero, kept to this file too. -/\nprivate def secret : Nat := 0\n\n"
          "/-- One less, or zero, matched as `down` matches. -/\ndef below : Nat → Nat\n  | 0 => 0\n  | n + 1 => n\n\n" + energy[at:])
energy = energy.replace(":= energy p.norm\n", ":= energy p.norm + 0 * two.val + secret + More.zero + 0 * Far.Away.one + down 0 + below 0\n")
at = energy.index("/-- The energy of every chain is even.")
energy = (energy[:at] + "/-- Site two, as a number proven to be two. -/\n"
          '@[trusted "5f0c6a8e-2d1b-4c3a-9e7f-1a2b3c4d5e6f"] def siteTwo : {n : Nat // n = 2} := ⟨_, second_site⟩\n\n'
          "/-- The energy of a point is even. -/\n"
          '@[trusted "6a1d7b9f-3e2c-4d4b-8f80-2b3c4d5e6f70"] theorem pointEnergy_even (p : Point) : pointEnergy p % 2 = 0 := by\n  sorry\n\n'
          "/-- Site two is two. -/\n"
          '@[trusted "7b2e8c0a-4f3d-4e5c-9a91-3c4d5e6f7081"] theorem siteTwo_val : siteTwo.val = 2 := siteTwo.property\n\n' + energy[at:])
open("Sample/Energy.lean", "w").write(energy + "\nvariable (late : Nat)\n")
PY
export_lib
run challenge Sample.pointEnergy_even Sample.siteTwo_val --out "$work-challenge-two"
deps="$(cat "$work-challenge-two/ChallengeDeps.lean")"
for kept in "theorem two_pos : 0 < 2 := by decide" "theorem second_site : (⟨2, by decide⟩ : Fin 3).val = 2 := rfl" \
            "private def «secret (Sample.Basic)» : Nat := 0" "def zero : Nat := «secret (Sample.Basic)»" \
            "private def «secret (Sample.Energy)» : Nat := 0" "+ «secret (Sample.Energy)» + More.zero" \
            $'namespace Sample.Extra\nend Sample.Extra' "open Extra" "namespace More.Inner" "end Inner" "end More" \
            $'namespace Far.Away\n\n/-- One, far away. -/\ndef one : Nat := 1\n\nend Far.Away\n\nend Sample\n\nend\n\nsection'; do
  [[ "$deps" == *"$kept"* ]] || fail "want '$kept' in: $deps"
done
for left in "def unused" "def hidden" "variable (late" "energy_even" "one_site_pos"; do
  [[ "$deps" != *"$left"* ]] || fail "'$left' is not needed: $deps"
done
must_fail "this challenge cannot be made" "  Sample.second_site: the other theorems need its proof, so the challenge cannot state it" \
  -- "$lb" challenge Sample.second_site Sample.siteTwo_val --out "$work-challenge-three"
run challenge Sample.second_site --out "$work-challenge-three"
[[ "$(cat "$work-challenge-three/ChallengeDeps.lean")" != *"siteTwo"* ]] || fail "second_site alone needs nothing of siteTwo"
run challenge --check "$work-challenge-two"
[[ "$out" == *", 1 of them by definitional equality" ]] || fail "below shares down's match in one file: $out"
[[ ! -e "$work-challenge-two/.lake" ]] && ! compgen -G ".leanblame/store/.tmp-*" >/dev/null \
  || fail "the check leaves files behind: $(ls -a "$work-challenge-two" .leanblame/store)"
git checkout -q -- Sample
export_lib
ok "a tagged definition that uses theorems brings their proofs, so second_site has no challenge with siteTwo_val, but one alone; two private secrets are written with their modules and mean the same; an open of Extra, of which nothing is needed, has Extra declared first; namespace More.Inner comes with end Inner, and end Far.Away closes two scopes; a variable after the needed commands stays out; below, which in one file uses the match Lean made for down, is definitionally equal; the check leaves no files"

echo "== release"
run release --tag 2026.10 --out "$logs/release.json"
release_hash="$(awk '/^release /{print $2}' <<<"$out")"
cmp -s "$logs/release.json" ".leanblame/store/manifests/${release_hash#sha256:}" || fail "--out differs from the stored manifest"
python3 - "$logs/release.json" "$release_hash" "$(current_export)" "$basic_record" "$energy_record" <<'PY' \
  || fail "release manifest does not match docs/schemas.md"
import hashlib, json, sys
path, h, export, basic, energy = sys.argv[1:]
text = open(path).read()
assert "sha256:" + hashlib.sha256(text.encode()).hexdigest() == h
m = json.loads(text)
assert m["tag"] == "2026.10" and m["export"] == export
assert m["kernel"] == {"checker": "leanchecker", "version": m["toolchain"], "passed": True}, m["kernel"]
assert m["records"] == sorted([basic, energy]), m["records"]
t = m["theorems"]
assert set(t) == {"Sample.energy_even", "Sample.second_site", "Sample.one_site_pos"}, t
assert t["Sample.energy_even"] == {"status": "open", "axioms": ["sorryAx"]}, t
assert t["Sample.second_site"]["status"] == "proven", t
assert t["Sample.one_site_pos"] == {"status": "proven", "axioms": ["Sample.energy_pos"]}, t
assert m["counts"] == {"proven": 2, "open": 1}, m["counts"]
PY
ok "release: leanchecker passed; energy_even open (sorryAx), one_site_pos proven from the tagged axiom"

echo "== an export of uncommitted changes names no commit"
touch notes.txt
export_lib
grep -q "warning: uncommitted changes in the library" "$logs/export.log" || fail "no warning: $(cat "$logs/export.log")"
run status --json
python3 -c 'import json, sys; assert json.loads(sys.argv[1])["commit"] is None' "$out" \
  || fail "status --json: an export of uncommitted changes names a commit"
must_fail "the current export has uncommitted changes" -- "$lb" sign --signer local:alice
must_fail "release: the current export has uncommitted changes" -- "$lb" release --tag 2026.10.2
rm notes.txt
export_lib
ok "an untracked file: the export names no commit; sign and release refuse it"

echo "== release refuses an axiom that is neither standard nor tagged"
cat >> Sample/Basic.lean <<'EOF'

/-- Not tagged: nobody signs it. -/
axiom Sample.unsigned_pos (n : Nat) : 0 < Sample.energy (n + 1)
EOF
edit Sample/Energy.lean 's/:= energy_pos 0$/:= unsigned_pos 0/'
grep -q ":= unsigned_pos 0" Sample/Energy.lean || fail "test setup: proof not swapped"
export_lib
want="theorem Sample.one_site_pos rests on axiom Sample.unsigned_pos, which is neither standard nor tagged and signed"
must_fail "release: $want" -- "$lb" release --tag 2026.10.1
out="$("$lb" status 2>"$logs/status.err")"
expect_line Sample.one_site_pos "Sample.one_site_pos valid"
grep -qxF "warning: $want" "$logs/status.err" || fail "status did not warn: $(cat "$logs/status.err")"
git checkout -q -- Sample
export_lib
ok "a theorem resting on an untagged axiom fails release and gets a status warning"

echo "== edit a proof inside a statement: second_site"
edit Sample/Energy.lean 's/2, by decide/2, by omega/'
grep -q "by omega" Sample/Energy.lean || fail "test setup: proof not swapped"
commit "second_site: another proof of 2 < 3 in the statement"
before="$(current_export)"
statement_of() { python3 -c 'import json, sys; print(next(p["text"] for p in json.load(sys.stdin)["pieces"] if p["file"] == "Challenge.lean" and p["theorem"] == sys.argv[1]))' "$1"; }
export_lib
[[ "$(current_export)" != "$before" ]] || fail "the proof edit did not change the export"
run challenge --graph
[[ "$(statement_of Sample.second_site <<<"$out")" == *"(⟨2, by omega⟩ : Fin 3).val = 2 := sorry"* ]] \
  || fail "the piece graph states second_site as it was: $(statement_of Sample.second_site <<<"$out")"
run status
expect_line Sample.second_site "Sample.second_site valid"
ok "a proof inside a statement is not part of the hash; a challenge states it as written now"

echo "== edit a body: pointEnergy"
edit Sample/Energy.lean 's/:= energy p.norm$/:= energy p.norm * 1/'
commit "pointEnergy: new body"
export_lib
# The store keeps the signed export and the current one; the unsigned export in between is gone.
[[ "$(ls .leanblame/store/exports | wc -l)" -eq 2 ]] || fail "store sweep: $(ls .leanblame/store/exports)"
[[ "$(ls .leanblame/store/graphs | wc -l)" -eq 2 ]] || fail "graph sweep: $(ls .leanblame/store/graphs)"
ok "export removes exports and graphs that no record names"
run status
expect_line Sample.pointEnergy "Sample.pointEnergy outdated change=own-body:Sample.pointEnergy"
expect_line Sample.energy_even "Sample.energy_even valid"
# The causes come from the signed export's graph, which `export` stored: missing or broken, status stops.
signed_graph="$(ls .leanblame/store/graphs | grep -v "^$(current_export | sed 's/^sha256://')-")"
mv ".leanblame/store/graphs/$signed_graph" "$logs/graph.json"
must_fail "the store has its export and boundary list but no graph of them" -- "$lb" status
printf 'not json\n' > ".leanblame/store/graphs/$signed_graph"
must_fail "not the graph of export" -- "$lb" status
mv "$logs/graph.json" ".leanblame/store/graphs/$signed_graph"
ok "status fails out loud when a signed graph is missing or broken"

echo "== stored files are read strictly"
cp .leanblame/current "$logs/current"
python3 -c 'import json; p = ".leanblame/current"; c = json.load(open(p)); c["extra"] = 1; json.dump(c, open(p, "w"))'
must_fail 'current: unknown key `extra`' -- "$lb" status
python3 -c 'import json; p = ".leanblame/current"; c = json.load(open(p)); del c["extra"], c["toolchain"]; json.dump(c, open(p, "w"))'
must_fail 'current: missing key `toolchain`' -- "$lb" status
cp "$logs/current" .leanblame/current
graph=".leanblame/store/graphs/$(current_export | sed 's/^sha256://')-$(python3 -c 'import json; print(json.load(open(".leanblame/current"))["boundary"][7:])').json"
cp "$graph" "$logs/graph-current.json"
python3 - "$graph" <<'PY'
import json, sys
g = json.load(open(sys.argv[1]))
g["nodes"] = [n for n in g["nodes"] if n["name"] != "Sample.double"]
json.dump(g, open(sys.argv[1], "w"))
PY
must_fail "depends on Sample.double, which has no node" -- "$lb" status
cp "$logs/graph-current.json" "$graph"
edit leanblame.toml '/^required_signers/d'
must_fail "missing required key: required_signers" -- "$lb" status
git checkout -q -- leanblame.toml
ok "an unknown or missing key, and a graph without a node a declaration uses, stop status"
signed_export=".leanblame/store/exports/${first_export#sha256:}"
mv "$signed_export" "$logs/signed-export"
run status
expect_line Sample.pointEnergy "Sample.pointEnergy outdated change=unknown"
mv "$logs/signed-export" "$signed_export"
ok "without the signed export in the store, the causes are unknown, and status says so"

echo "== edit a dependency body: energy"
edit Sample/Basic.lean 's/def energy (n : Nat) : Nat := double n$/def energy (n : Nat) : Nat := double n + 0/'
commit "energy: new body"
export_lib
run status
expect_line Sample.energy "Sample.energy outdated change=own-body:Sample.energy"
expect_line Sample.energy_even "Sample.energy_even valid blocked-by=Sample.energy"
expect_line Sample.pointEnergy \
  "Sample.pointEnergy outdated blocked-by=Sample.energy change=own-body:Sample.pointEnergy"

echo "== edit an untagged helper: double"
edit Sample/Basic.lean 's/def double (n : Nat) : Nat := n + n/def double (n : Nat) : Nat := 2 * n/'
commit "double: new body"
export_lib
run status
expect_line Sample.energy "Sample.energy outdated change=own-body:Sample.energy;untagged:Sample.double"

echo "== edit informal text: energy's docstring"
edit Sample/Basic.lean 's/two units per site\./two units of energy per site./'
commit "energy: new docstring"
before="$(current_export)"
export_lib
[[ "$(current_export)" == "$before" ]] || fail "a docstring edit changed the export"
ok "a docstring edit keeps the export"
run status
expect_line Sample.energy \
  "Sample.energy outdated change=own-text:Sample.energy;own-body:Sample.energy;untagged:Sample.double"
expect_line Sample.energy_even \
  "Sample.energy_even outdated blocked-by=Sample.energy change=dep-spec:Sample.energy"

echo "== diff: what changed since a sign-off, as the kernel sees it"
run status
status_out="$out"
run diff --from "$basic_record"
python3 - "$status_out" "$out" <<'PY2' || fail "diff and status disagree: $out"
import sys
status, diff = sys.argv[1].splitlines(), sys.argv[2].splitlines()
# Every declaration was last approved on the first sign-off's export, so status compares with it too.
want = {l.split()[0]: next(p for p in l.split() if p.startswith("change=")) for l in status if " outdated " in l}
got = {l.split()[0]: l.split()[1] for l in diff if not l.startswith(" ") and " change=" in l}
assert want and want == got, (want, got)
assert diff[-1] == f"{len(want)} changed, 0 added, 0 removed", diff[-1]
PY2
grep -qxF "  - The energy of a chain of \`n\` sites: two units per site." <<<"$out" \
  && grep -qxF "  + The energy of a chain of \`n\` sites: two units of energy per site." <<<"$out" \
  || fail "diff does not show both docstrings: $out"
ok "diff --from the first sign-off: what status calls outdated, with the same causes, and both docstrings"
run diff --from "$basic_record" --json Sample.energy Sample.second_site
python3 - "$out" "$basic_record" <<'PY2' || fail "diff --json: $out"
import json, sys
d = json.loads(sys.argv[1])
assert d["from"]["record"] == sys.argv[2] and d["to"]["record"] is None, d
energy, site = d["declarations"]
assert energy["to"]["name"] == "Sample.energy" and energy["from"]["claim"] != energy["to"]["claim"], energy
c = energy["changes"]
assert (c["informal"], c["statement"], c["body"]) == (True, False, True), c
assert c["untagged"] == ["Sample.double"] and c["relies_on"] == {"added": [], "removed": [], "changed": []}, c
assert site["to"]["name"] == "Sample.second_site" and site["from"]["claim"] == site["to"]["claim"], site
assert not any(site["changes"][k] for k in ("informal", "statement", "body")), site
PY2
ok "diff --json: energy's docstring and body, and the untagged double under it; second_site's proof edit is no change"
mv "$signed_export" "$logs/signed-export"
must_fail "which this store lacks; run .leanblame export. at commit" -- "$lb" diff --from "$basic_record"
mv "$logs/signed-export" "$signed_export"
must_fail "Sample.nothing is on neither boundary list" -- "$lb" diff --from "$basic_record" Sample.nothing
run diff --from "$basic_record" --to "$energy_record"
[[ "$out" == "0 changed, 0 added, 0 removed" ]] || fail "two records of one export: $out"
ok "diff fails out loud without the signed export or for an unknown name; two records of one export differ in nothing"

echo "== withdraw"
run sign --withdraw "$basic_record" --signer local:alice --note "energy was wrong"
grep -q "^withdraw sha256:" <<<"$out" || fail "no withdraw record: $out"
withdraw_record="$(awk '/^withdraw /{print $2}' <<<"$out")"
must_fail "only its signer can withdraw it" -- "$lb" sign --withdraw "$basic_record" --signer local:bob
ok "only the signer can withdraw"
must_fail "is a withdraw; compare with the approve record it withdraws, $basic_record" -- "$lb" diff --from "$withdraw_record"
ok "diff refuses a withdraw record as a point"
run validate
ok "validate: $out"
commit "withdraw Sample.Basic"
run status
expect_line Sample.energy "Sample.energy unsigned"
expect_line Sample.Point "Sample.Point unsigned blocked-by=Sample.Point.mk"
expect_line Sample.energy_even \
  "Sample.energy_even outdated blocked-by=Sample.energy change=dep-spec:Sample.energy"

echo "== exclude"
edit leanblame.toml "s|^exclude = \[\]|exclude = [\"$withdraw_record\"]|"
grep -q '^exclude = \["sha256:' leanblame.toml || fail "test setup: exclude not set"
must_fail "withdrawals cannot be excluded" -- "$lb" validate
must_fail "withdrawals cannot be excluded" -- "$lb" status
git checkout -q -- leanblame.toml
ok "excluding a withdraw record fails validate and status"
edit leanblame.toml "s|^exclude = \[\]|exclude = [\"sha256:$(printf '0%.0s' {1..64})\"]|"
must_fail "which is no record here" -- "$lb" status
git checkout -q -- leanblame.toml
ok "excluding a record that does not exist fails status"
edit leanblame.toml "s|^exclude = \[\]|exclude = [\"$energy_record\"]|"
run status --json
python3 - "$out" "$energy_record" <<'PY' || fail "status --json: an excluded approval"
import json, sys
d = {x["name"]: x for x in json.loads(sys.argv[1])["declarations"]}["Sample.second_site"]
assert d["state"] == "unsigned", d["state"]
assert [(h["record"], h["standing"]) for h in d["history"]] == [(sys.argv[2], "excluded")], d["history"]
PY
git checkout -q -- leanblame.toml
ok "an excluded approval stays in the history, as excluded"

echo "== blame"
run blame Sample.energy
grep -q "approve  local:alice" <<<"$out" || fail "blame lacks the approval: $out"
grep -q "withdraw  local:alice" <<<"$out" || fail "blame lacks the withdrawal: $out"
grep -q "record $basic_record withdrawn" <<<"$out" || fail "blame does not mark the record withdrawn: $out"
ok "blame shows the approval and the withdrawal"

echo "== validate: append-only"
first="$(git rev-list --max-parents=0 HEAD)"
run validate --base-ref "$first"
ok "records added since $first: $out"
record_file="records/${basic_record#sha256:}.toml"
printf 'note = "edited"\n' >> "$record_file"
must_fail "record $basic_record of the merge base is missing" "file name must be the sha256" \
  -- "$lb" validate --base-ref HEAD
git checkout -q -- "$record_file"
git rm -q "$record_file"
must_fail "record $basic_record of the merge base is missing" -- "$lb" validate --base-ref HEAD
git checkout -q HEAD -- "$record_file"
ok "validate refuses modified and deleted records"
printf 'not a record\n' > records/notes.toml
must_fail "records/notes.toml: not a record: the file name must be the sha256" -- "$lb" validate
must_fail "records/notes.toml: not a record: the file name must be the sha256" -- "$lb" status
rm records/notes.toml
ok "a misnamed file in records/ fails validate and status"
# Renaming the records directory in leanblame.toml must not hide a deletion.
git mv records r
edit leanblame.toml 's|^records = \["records/"\]|records = ["r/"]|'
grep -q '^records = \["r/"\]' leanblame.toml || fail "test setup: records directory not renamed"
git rm -q -f "r/${basic_record#sha256:}.toml"
must_fail "records/${basic_record#sha256:}.toml: record $basic_record of the merge base is missing" \
  -- "$lb" validate --base-ref HEAD
git reset -q --hard HEAD
ok "validate checks the merge base's records directories too"
git mv records r
edit leanblame.toml 's|^records = \["records/"\]|records = ["r/"]|'
run validate --base-ref HEAD
git reset -q --hard HEAD
ok "moving every record to a new records directory passes"
mkdir r && cp records/*.toml r/ && rm "r/${withdraw_record#sha256:}.toml"
edit leanblame.toml 's|^records = \["records/"\]|records = ["r/"]|'
must_fail "record $withdraw_record of the merge base is missing" -- "$lb" validate --base-ref HEAD
rm -rf r && git checkout -q -- leanblame.toml
ok "repointing the records directory to one without the withdraw fails"
edit leanblame.toml 's|^records = \["records/"\]|records = ["https://example.invalid/records.git"]|'
must_fail "https://example.invalid/records.git: only local directories are supported" -- "$lb" status
git checkout -q -- leanblame.toml
ok "a remote records repository is an error"

echo "== export refuses undocumented and unsafe tagged declarations"
cat >> Sample/Basic.lean <<'EOF'

namespace Sample
@[trusted] def undocumented (n : Nat) : Nat := n
/-- Unsafe code never reaches the kernel. -/
@[trusted] unsafe def unsafeEnergy (n : Nat) : Nat := n
end Sample
EOF
must_fail "Sample.undocumented: tagged declarations need a docstring" \
  'Sample.unsafeEnergy: `unsafe` declarations cannot be tagged' -- "$lb" export
git checkout -q -- Sample/Basic.lean
ok "export refuses a tagged declaration without docstring and an unsafe one"

echo "== blueprint: a verso-blueprint manifest (hand-written from verso-blueprint's sources)"
stored_boundary() { echo ".leanblame/store/boundaries/$(awk '/^boundary /{print $2}' <<<"$out" | sed 's/^sha256://')"; }
run export --boundary "$here/blueprint/blueprint-manifest.json"
python3 - "$(stored_boundary)" <<'PY' || fail "boundary list from the blueprint manifest"
import json, sys
d = {x["name"]: x for x in json.load(open(sys.argv[1]))["declarations"]}
assert set(d) == {"Sample.energy", "Sample.energy_even", "Sample.Point", "Sample.Point.mk", "Sample.Point.x",
                  "Sample.Point.y", "Sample.Point.norm", "Sample.pointEnergy"}, sorted(d)
ids = {n: x["id"] for n, x in d.items()}
assert ids == {"Sample.energy": "def:energy", "Sample.energy_even": "thm:even", "Sample.Point": "def:point",
               "Sample.pointEnergy": "def:pointEnergy", "Sample.Point.mk": "def:point/mk", "Sample.Point.x": "def:point/x",
               "Sample.Point.y": "def:point/y", "Sample.Point.norm": "def:point/norm"}, ids
parents = {n: x["parent"] for n, x in d.items() if x["parent"]}
assert parents == {n: "Sample.Point" for n in ["Sample.Point.mk", "Sample.Point.x", "Sample.Point.y", "Sample.Point.norm"]}, parents
assert d["Sample.energy"]["informal"] == "The energy of a chain of $n$ sites is $2n$: two units per site."
assert d["Sample.energy_even"]["informal"] == '<div class="theorem-body"><p>The energy of every chain is even.</p></div>'
assert d["Sample.Point.norm"]["informal"] == d["Sample.Point"]["informal"]
assert d["Sample.Point.x"]["informal"] != d["Sample.Point"]["informal"]
PY
run status
grep -q "^8 tagged: " <<<"$out" || fail "status on the blueprint boundary list: $out"
run blame def:point
grep -q "^Sample.Point  structure  " <<<"$out" || fail "blame by label: $out"
ok "a label is the id of its first declaration; the others and the structure's members name it as parent: def:point/x"
mkdir "$logs/bp"
cp "$here/blueprint/blueprint-html-cache.json" "$logs/bp/"
python3 - "$here/blueprint/blueprint-manifest.json" "$logs/bp/blueprint-manifest.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
m["previews"] += [
  {"label": "«def:energy2»", "key": "def:energy2--statement", "targetKind": "block", "facet": "statement",
   "codeData": {"externalDecls": [{"canonical": "Sample.energy"}]},
   "externalMarkup": [{"language": "tex", "slot": "statement", "raw": "The energy, again."}]},
  {"label": "«thm:silent»", "key": "thm:silent--statement", "targetKind": "block", "facet": "statement",
   "codeData": {"literateDeclarations": {"definedTheorems": [{"name": "Sample.second_site"}]}}},
  {"key": "nolabel--statement", "targetKind": "block", "facet": "statement",
   "codeData": {"externalDecls": [{"canonical": "Sample.one_site_pos"}]}}]
json.dump(m, open(sys.argv[2], "w"))
PY
must_fail "Sample.energy is claimed by labels def:energy and def:energy2" "no statement text for label thm:silent" \
  "a statement entry for \[Sample.one_site_pos\] has no label" -- "$lb" export --boundary "$logs/bp/blueprint-manifest.json"
printf '{"declarations": []}\n' > "$logs/other.json"
must_fail "takes a verso-blueprint blueprint-manifest.json" -- "$lb" export --boundary "$logs/other.json"
ok "a name claimed by two labels, a statement without text or label, and other files are errors"

echo "== equiv: a definitional change under two tagged declarations"
rm -rf "$work"
work="$work_equiv"
cd "$work"
cat >> Sample/Basic.lean <<'EOF'

/-- Twice zero is zero. -/
@[trusted "5d1c1d36-7a3e-4b8e-9f0a-2b6c8d9e0f11"] theorem Sample.double_zero : Sample.double 0 = 0 := rfl
EOF
commit "double_zero"
export_lib
run sign --signer local:alice Sample.energy Sample.double_zero
commit "sign energy and double_zero at one export"
edit Sample/Basic.lean 's/def double (n : Nat) : Nat := n + n/def double (n : Nat) : Nat := Nat.add n n/'
commit "double: Nat.add"
export_lib
run status
expect_line Sample.energy "Sample.energy outdated change=untagged:Sample.double"
expect_line Sample.double_zero "Sample.double_zero outdated change=untagged:Sample.double"
run equiv
proof="$(awk '/^Sample.energy proven /{print $3}' <<<"$out")"
[[ "$proof" =~ ^sha256:[0-9a-f]{64}$ ]] || fail "equiv did not prove Sample.energy: $out"
grep -qxF "Sample.double_zero proven $proof" <<<"$out" || fail "equiv did not prove Sample.double_zero: $out"
[[ -f ".leanblame/store/proofs/${proof#sha256:}" ]] || fail "the proof $proof is not in the object store"
# The proof is an export anyone can replay with the toolchain's checker.
"$(lean --print-prefix)/bin/leanchecker" --silent --from-export ".leanblame/store/proofs/${proof#sha256:}" \
  || fail "leanchecker rejects the proof export $proof"
ok "equiv: Old.Sample.double = Sample.double by the kernel; leanchecker replays the proof export $proof"
run status
expect_line Sample.energy "Sample.energy outdated evidence=$proof change=untagged:Sample.double"
expect_line Sample.double_zero "Sample.double_zero outdated evidence=$proof change=untagged:Sample.double"
run sign --signer local:alice Sample.energy Sample.double_zero
record="$(awk '/^approve /{print $3}' <<<"$out")"
[[ "$(grep -cF "evidence = \"$proof\"}" "$record")" -eq 2 ]] || fail "the approve record does not carry the proof: $(cat "$record")"
run status
expect_line Sample.energy "Sample.energy valid"
expect_line Sample.double_zero "Sample.double_zero valid"
ok "sign puts the proof in the record as each declaration's evidence; both are valid again"
commit "sign after equiv"

echo "== equiv: a change that is not definitional"
edit Sample/Basic.lean 's/def double (n : Nat) : Nat := Nat.add n n/def double (n : Nat) : Nat := 2 * n/'
commit "double: 2 * n"
export_lib
must_fail "^Sample.double: not definitionally equal; a human reads$" "^  old: fun n => Nat.add n n$" \
  "^  new: fun n => HMul.hMul 2 n$" "^Sample.energy: not proven, because of Sample.double; a human reads$" \
  "^Sample.double_zero proven sha256:" "^equiv: 1 proven, 1 left to a human$" -- "$lb" equiv
proof2="$(awk '/^Sample.double_zero proven /{print $3}' "$logs/fail.log")"
run status
expect_line Sample.energy "Sample.energy outdated change=untagged:Sample.double"
expect_line Sample.double_zero "Sample.double_zero outdated evidence=$proof2 change=untagged:Sample.double"
ok "n + n and 2 * n are not definitionally equal: both bodies shown; double_zero still holds by evaluation"
run sign --withdraw "$record" --signer local:alice --constants Sample.double_zero
run status
expect_line Sample.double_zero "Sample.double_zero outdated change=untagged:Sample.double"
ok "a proof against a withdrawn approval does not count"
edit Sample/Energy.lean 's/:= energy p.norm$/:= energy p.norm * 1/'
commit "pointEnergy: new body"
export_lib
must_fail '^Sample.pointEnergy: no goal: a cause other than `untagged`; a human reads$' -- "$lb" equiv Sample.pointEnergy
ok "equiv refuses an own-body change"

echo "== id: renames, a new id, shared and malformed ids"
rm -rf "$work"
work="$work_id"
cd "$work"
edit Sample/Energy.lean 's/theorem second_site /theorem site_two /'
export_lib
run status
expect_line Sample.site_two "Sample.site_two outdated change=own-body:Sample.site_two"
run diff --from "$basic_record" Sample.site_two
expect_line Sample.site_two "Sample.site_two renamed-from=Sample.second_site change=own-body:Sample.site_two"
grep -qxF "  statement:" <<<"$out" || fail "diff, rename: no statement lines: $out"
ok "diff matches a renamed declaration by its id and shows both statements"
run status --json
python3 - "$out" "$(id_of Sample.second_site)" <<'PY' || fail "rename: $out"
import json, sys
d = {x["name"]: x for x in json.loads(sys.argv[1])["declarations"]}
assert "Sample.second_site" not in d
t = d["Sample.site_two"]
assert t["id"] == sys.argv[2] and t["state"] == "outdated", t
assert [(h["name"], h["standing"]) for h in t["history"]] == [("Sample.second_site", "superseded")], t["history"]
PY
git checkout -q -- Sample
ok "a renamed declaration keeps its id and its sign-off history; it is outdated, as the name is hashed"
run blame "$energy_id"
grep -q "^Sample.energy  def  valid  claim " <<<"$out" || fail "blame by id: $out"
grep -qxF "  id: $energy_id" <<<"$out" || fail "blame by id: $out"
ok "blame takes an id"
edit Sample/Basic.lean "s/@\[trusted \"$energy_id\"\] def energy/@[trusted] def energy/"
run id
new_energy_id="$(awk '$2 == "Sample.energy" {print $1}' <<<"$out")"
[[ -n "$new_energy_id" && "$new_energy_id" != "$energy_id" && "$(wc -l <<<"$out")" -eq 1 ]] \
  || fail "id: want one new id, for Sample.energy: $out"
commit "energy: a new id"
export_lib
run status
expect_line Sample.energy "Sample.energy unsigned"
expect_line Sample.energy_even "Sample.energy_even valid blocked-by=Sample.energy"
expect_line Sample.Point.x "Sample.Point.x valid"
run diff --from "$basic_record"
{ grep -qxF "Sample.energy added" <<<"$out" && grep -qxF "Sample.energy removed" <<<"$out"; } \
  || fail "diff, a new id: $out"
ok "diff: a new id is a new declaration; the old id's declaration is removed"
run blame "$energy_id"
grep -qxF "$energy_id  (not on the current boundary list)" <<<"$out" || fail "blame by the old id: $out"
grep -q "approve  local:alice  as Sample.energy  claim " <<<"$out" || fail "blame by the old id: $out"
ok "a new id is a new declaration: the approvals stay with the old id"
edit Sample/Energy.lean "s/$(id_of Sample.pointEnergy)/$new_energy_id/"
must_fail "Sample.energy and Sample.pointEnergy have the same id $new_energy_id" -- "$lb" export
git checkout -q -- Sample
ok "export refuses two declarations with the same id"
edit Sample/Energy.lean "s/$(id_of Sample.pointEnergy)/x/"
must_fail "the id must be a UUID" -- "$lb" export
git checkout -q -- Sample
ok "a malformed id is a build error"

echo "== tags written after the fact, in a library of their own"
# As an instance tags a library it does not own: `attribute [trusted] Name` in a library of its own.
printf '\n[[lean_lib]]\nname = "Tags"\n' >> lakefile.toml
printf 'import Sample\n\nattribute [trusted] Sample.double\n' > Tags.lean
commit "tags in a library of their own"
libs=(--lib Sample --lib Tags)
must_fail "Sample.double: tagged without an id" -- "$lb" export "${libs[@]}"
ok "export refuses a tag written after the fact without an id"
run id "${libs[@]}"
double_id="$(awk '$2 == "Sample.double" {print $1}' <<<"$out")"
[[ -n "$double_id" && "$(wc -l <<<"$out")" -eq 1 ]] || fail "id, attribute: want one new id, for Sample.double: $out"
grep -qxF "attribute [trusted \"$double_id\"] Sample.double" Tags.lean || fail "id, attribute: $(cat Tags.lean)"
ok "id writes the id into the attribute command, in the library that tags"
commit "tags: an id"
"$lb" export "${libs[@]}" >/dev/null 2>"$logs/export.log" || { cat "$logs/export.log" >&2; fail "export with Tags"; }
run status --json
python3 - "$out" "$double_id" <<'PY' || fail "tags: $out"
import json, sys
d = {x["name"]: x for x in json.loads(sys.argv[1])["declarations"]}
t = d["Sample.double"]
assert t["id"] == sys.argv[2] and t["state"] == "unsigned", t
PY
ok "a declaration tagged from another library is on the boundary list, with its id"
printf 'attribute [trusted] Sample.energy\n' >> Tags.lean
must_fail "Sample.energy\` is already tagged" -- "$lb" export "${libs[@]}"
git checkout -q -- Tags.lean
ok "a second tag on one declaration is a build error"
printf 'attribute [trusted] Sample.two Sample.two_pos\n' >> Tags.lean
must_fail "a \`trusted\` tag names one declaration" -- "$lb" export "${libs[@]}"
git checkout -q -- Tags.lean
ok "one tag names one declaration: two names in one attribute command are a build error"
python3 - <<'PY'
p = "Sample/Basic.lean"
s = open(p).read()
s = s.replace("def double (n : Nat) : Nat := n + n", "def twice (n : Nat) : Nat := n + n\n\n"
  "/-- Twice a natural number. -/\n@[deprecated twice (since := \"2026-10-28\")] def double := @twice", 1)
open(p, "w").write(s.replace(":= double n", ":= twice n"))
PY
commit "double renamed twice, with a deprecated alias"
(lake build Tags 2>&1 || true) | grep -q "deprecated alias of \`Sample.twice\`" || fail "rename: no warning in the build of Tags"
"$lb" export "${libs[@]}" >/dev/null 2>"$logs/export.log" || { cat "$logs/export.log" >&2; fail "export, rename"; }
run status --json
python3 - "$out" "$double_id" <<'PY' || fail "rename with an alias: $out"
import json, sys
d = {x["name"]: x for x in json.loads(sys.argv[1])["declarations"]}
assert "Sample.double" not in d, d.keys()
assert d["Sample.twice"]["id"] == sys.argv[2], d["Sample.twice"]
PY
ok "a rename marked by a deprecated alias keeps the tag and its id, with a warning to update the name"
python3 - <<'PY'
p = "Sample/Basic.lean"
s = open(p).read()
s = s.replace('\n\n/-- Twice a natural number. -/\n@[deprecated twice (since := "2026-10-28")] def double := @twice', "", 1)
open(p, "w").write(s)
PY
commit "the alias removed"
must_fail "Tags.lean" "Unknown constant \`Sample.double\`" -- "$lb" export "${libs[@]}"
ok "a rename without an alias stops the build at the tag"

rm -rf "$work" "$logs"
echo "PASS ($pass checks)"
