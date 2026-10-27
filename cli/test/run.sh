#!/usr/bin/env bash
# End-to-end test of the leanblame CLI on test/Sample.
#
#   cli/test/run.sh            # from anywhere; needs elan (Lean 4.35.0), git, python3
#
# Copies the sample library to a scratch directory, makes it a git repository,
# and walks through: init -> export -> sign (records name declarations by id) ->
# status (valid; --json complete, nothing on stderr) -> sorried copies (proofs
# replaced by sorry but those a definition uses; one piece per command; merged
# into one file, they build without the library, whole or cut to what one theorem
# needs; copied again only where a module changed) -> release -> edit a body ->
# status (outdated, own-body) -> stored files read strictly; causes unknown
# without the signed export -> edit a dependency body -> status (blocked) -> more
# causes (untagged, own-text, dep-spec) -> withdraw -> status (withdrawn) ->
# exclude (a withdraw record, no record, an approve record) -> blame -> validate
# (and its append-only check) -> a boundary list from a verso-blueprint manifest,
# labels as ids -> equiv, in a copy made after the first signoff: a definitional
# change proven (evidence shown by status, the record carries the proof, valid),
# one that is not definitional, an own-body change refused -> ids, in another
# copy made after the first signoff: a rename keeps the id and the history, blame
# by id, a new id is a new declaration, a shared id and a malformed one refused.
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
python3 - "$logs/status.json" "$ids" <<'PY' || fail "status --json does not match docs/design/14"
import json, sys
s = json.load(open(sys.argv[1]))
ids = {name: i for i, name in (line.split() for line in sys.argv[2].splitlines())}
assert s["schema"] == "leanblame.status.6"
assert set(s) == {"schema", "library", "commit", "toolchain", "deps", "requires", "export", "boundary", "generated",
                  "modules", "standard_axioms", "declarations", "records", "untagged_in_library"}, set(s)
assert len(s["commit"]) == 40, s["commit"]
assert s["toolchain"].startswith("v4.") and s["deps"] == {}, (s["toolchain"], s["deps"])
assert s["requires"] == [{"name": "leanblame", "git": None, "rev": None, "sub_dir": None}], s["requires"]
modules = {m["name"]: m for m in s["modules"]}
assert sorted(modules) == ["Sample", "Sample.Basic", "Sample.Energy"], s["modules"]
assert all(set(m) == {"name", "imports", "sorried"} and m["sorried"].startswith("sha256:") for m in s["modules"])
assert modules["Sample"]["imports"] == ["Sample.Basic", "Sample.Energy"], modules["Sample"]
assert modules["Sample.Energy"]["imports"] == ["Sample.Basic"] and modules["Sample.Basic"]["imports"] == ["LeanBlame.Attr"]
assert s["standard_axioms"] == ["propext", "Classical.choice", "Quot.sound"], s["standard_axioms"]
assert s["untagged_in_library"] == [{"name": "Sample.double", "used_by": ["Sample.energy"]}], s["untagged_in_library"]
keys = {"id", "parent", "module", "kind", "role", "informal", "statement", "claim", "state", "change", "signers",
        "history", "blocked_by", "proof", "evidence", "tagged_deps", "untagged_deps", "closure_size"}
members = {"Sample.Point.mk": "mk", "Sample.Point.x": "x", "Sample.Point.y": "y"}
for name, d in s["declarations"].items():
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
assert s["declarations"]["Sample.energy_even"]["tagged_deps"] == ["Sample.energy"]
assert {"name": "Sample.double", "module": "Sample.Basic"} in s["declarations"]["Sample.energy"]["untagged_deps"]
text = lambda segs: "".join(seg["text"] for seg in segs)
even = s["declarations"]["Sample.energy_even"]["statement"]
assert text(even["pretty"]) == "Sample.energy_even (n : Nat) : Sample.energy n % 2 = 0", text(even["pretty"])
assert "HMod.hMod" in text(even["plain"]), text(even["plain"])
assert {"const": "Sample.energy", "text": "Sample.energy"} in even["pretty"], even["pretty"]
assert all(set(seg) == {"text", "const"} for seg in even["pretty"]), even["pretty"]
assert text(s["declarations"]["Sample.energy"]["statement"]["pretty"]) == "Sample.energy (n : Nat) : Nat"
assert s["declarations"]["Sample.energy_even"]["proof"]["axioms"] == ["sorryAx"]
assert s["declarations"]["Sample.one_site_pos"]["proof"]["axioms"] == ["Sample.energy_pos"]
assert s["declarations"]["Sample.energy"]["role"] == "defined"
assert s["declarations"]["Sample.energy_even"]["role"] == "proved"
assert s["declarations"]["Sample.energy_pos"]["role"] == "assumed"
records = s["records"]
assert len(records) == 2 and all(r["action"] == "approve" and r["signer"] == "local:alice" for r in records), records
basic = next(r for r in records if r["module"] == "Sample.Basic")
assert basic["path"] == "records/" + basic["record"][len("sha256:"):] + ".toml", basic["path"]
assert {c["name"] for c in basic["constants"]} == {"Sample.energy", "Sample.Point", "Sample.Point.mk", "Sample.Point.x",
                                                  "Sample.Point.y", "Sample.Point.norm"}, basic["constants"]
assert all(set(c) == {"id", "name", "claim", "evidence"} and c["evidence"] is None for c in basic["constants"])
PY
ok "status --json has the docs/design/14 fields and nothing on stderr; members' ids come from their structure's"

echo "== sorried: the library's modules with proofs replaced by sorry"
sorried_of() { python3 -c 'import json, sys; print(next(m["sorried"] for m in json.load(open(sys.argv[1]))["modules"] if m["name"] == sys.argv[2]))' "$logs/status.json" "$1"; }
run sorried "$(sorried_of Sample)" "$(sorried_of Sample.Basic)" "$(sorried_of Sample.Energy)"
printf '%s' "$out" > "$logs/sorried.json"
python3 - "$logs/sorried.json" "$logs/status.json" "$work-copies" "$work-cut" <<'PY' \
  || fail "sorried: the copies are not the modules with proofs replaced by sorry, in pieces"
import hashlib, json, os, sys
printed, status, whole, cut = sys.argv[1:]
copies = json.load(open(printed))
s = json.load(open(status))
modules = {m["name"]: m for m in s["modules"]}
assert set(copies) == {m["sorried"] for m in modules.values()}, set(copies)
pieces = {name: copies[m["sorried"]] for name, m in modules.items()}
assert all(set(p) == {"text", "keep", "declares", "uses"} for ps in pieces.values() for p in ps)
text = lambda name: "".join(p["text"] for p in pieces[name])
assert pieces["Sample"] == [], "a module of imports only has no pieces"
basic = open("Sample/Basic.lean").read()
assert text("Sample.Basic") == basic[basic.index("namespace Sample"):].rstrip(), "a definition uses two_pos, so its proof stays"
e = text("Sample.Energy")
assert e.startswith("noncomputable section\n"), "the copy starts after the imports"
assert e.endswith("\nend Sample\nend"), "a last piece closes the scopes left open, innermost first"
for kept in ["theorem second_site", "theorem energy_even (n : Nat) : energy n % 2 = 0 := sorry",
             "axiom energy_pos", "theorem one_site_pos : 0 < energy 1 := sorry"]:
    assert kept in e, (kept, e)
assert "rfl" not in e and "energy_pos 0" not in e and e.count(":= sorry") == 3, e
assert "(⟨2, by decide⟩ : Fin 3).val = 2 := sorry" in e, "a proof inside a statement stays"
E = pieces["Sample.Energy"]
assert [p["keep"] for p in E] == [True, True, True, False, False, False, False, False, True], [p["keep"] for p in E]
assert E[2]["text"].endswith("variable (q : Point)") and E[2]["uses"] == ["Sample.Point"], E[2]
assert E[3]["declares"] == ["Sample.pointEnergy"], E[3]
assert E[3]["uses"] == ["Sample.Point", "Sample.Point.norm", "Sample.energy"], E[3]
assert E[3]["text"].startswith("\n\n/-- The energy of a point"), "the docstring goes with its declaration"
# Lean reads the section's `variable` again for each declaration after it, used or not.
assert E[5]["declares"] == ["Sample.energy_even"] and E[5]["uses"] == ["Sample.Point", "Sample.energy"], E[5]
assert pieces["Sample.Basic"][2]["uses"] == ["Sample.double"], pieces["Sample.Basic"][2]

# Merged as a comparator package merges them: every import that is not a module of the library,
# then each module after the ones it imports, in a section, with the pieces it needs.
def merge(order, need):
    imports = []
    for m in order:
        imports += [i for i in modules[m]["imports"] if i not in modules and i not in imports]
    parts = ""
    for m in order:
        body = "".join(p["text"] for k, p in enumerate(pieces[m]) if (m, k) in need).lstrip()
        if body:
            parts += f"\n-- {m}\nsection\n{body}\nend\n"
    return "".join(f"import {i}\n" for i in imports) + parts
def closure(roots):
    order = []
    def visit(name):
        if name in modules and name not in order:
            for i in modules[name]["imports"]:
                visit(i)
            order.append(name)
    for r in roots:
        visit(r)
    return order
def write(directory, files):
    os.makedirs(directory, exist_ok=True)
    for name, content in files.items():
        open(f"{directory}/{name}", "w").write(content)
# Whole: every piece of every module.
order = closure(sorted(modules))
write(whole, {"ChallengeDeps.lean": merge(order, {(m, k) for m in order for k in range(len(pieces[m]))})})
# Cut to what energy_even needs: what its piece uses, the pieces those use, and the pieces kept always.
theorem = "Sample.energy_even"
order = closure([s["declarations"][theorem]["module"]])
assert order == ["Sample.Basic", "Sample.Energy"], order
where = {n: (m, k) for m in order for k, p in enumerate(pieces[m]) for n in p["declares"]}
need = {(m, k) for m in order for k, p in enumerate(pieces[m]) if p["keep"]}
todo = [where[u] for m, k in need for u in pieces[m][k]["uses"]]
todo += [where[u] for p in pieces["Sample.Energy"] if theorem in p["declares"] for u in p["uses"]]
while todo:
    m, k = todo.pop()
    if (m, k) not in need:
        need.add((m, k))
        todo += [where[u] for u in pieces[m][k]["uses"]]
deps = merge(order, need)
for kept in ["def double", "def energy", "structure Point", "variable (q : Point)", "noncomputable section"]:
    assert kept in deps, (kept, deps)
for left in ["two_pos", "Point.norm", "pointEnergy", "second_site", "energy_pos", "theorem energy_even"]:
    assert left not in deps, (left, deps)
write(cut, {"ChallengeDeps.lean": deps, "Challenge.lean":
    "import ChallengeDeps\n\nnamespace Challenge\n\ntheorem energy_even (n : Nat) : Sample.energy n % 2 = 0 := sorry\n\nend Challenge\n"})
PY
ok "sorried prints each copy by its hash, in pieces with what each declares and uses; three theorem proofs are sorry; two_pos keeps its proof"
for dir in "$work-copies" "$work-cut"; do
  cp lean-toolchain "$dir/"
  printf 'name = "copies"\ndefaultTargets = ["ChallengeDeps"]\n\n[[require]]\nname = "leanblame"\npath = "%s"\n\n[[lean_lib]]\nname = "ChallengeDeps"\n\n[[lean_lib]]\nname = "Challenge"\n' "$cli" > "$dir/lakefile.toml"
done
(cd "$work-copies" && lake build) >"$logs/copies.log" 2>&1 || fail "the merged copies do not build without the library: $(cat "$logs/copies.log")"
ok "the copies, merged into one file, build on their own"
(cd "$work-cut" && lake build ChallengeDeps Challenge) >"$logs/cut.log" 2>&1 || fail "the copies cut for energy_even do not build: $(cat "$logs/cut.log")"
ok "cut to what energy_even needs (two_pos, Point.norm and the other theorems left out), they build, and its challenge with them"
python3 - <<'PY'
p = "Sample/Energy.lean"
s = open(p).read()
at = s.index("\n", s.index("theorem second_site")) + 1
check = "/-- info: 'Sample.second_site' does not depend on any axioms -/\n#guard_msgs in\n#print axioms second_site\n"
open(p, "w").write(s[:at] + check + s[at:])
PY
must_fail "Sample.Energy: the copy differs from the library" "guard_msgs" -- "$lb" export
git checkout -q -- Sample/Energy.lean
ok "an error in the middle of a module's copy stops export (the copy of second_site rests on sorryAx)"
must_fail "is no module copy of the last export" -- "$lb" sorried "sha256:$(printf '0%.0s' {1..64})"
ok "sorried refuses a hash the last export does not list"

echo "== release"
run release --tag 2026.10 --out "$logs/release.json"
release_hash="$(awk '/^release /{print $2}' <<<"$out")"
cmp -s "$logs/release.json" ".leanblame/store/manifests/${release_hash#sha256:}" || fail "--out differs from the stored manifest"
python3 - "$logs/release.json" "$release_hash" "$(current_export)" "$basic_record" "$energy_record" <<'PY' \
  || fail "release manifest does not match docs/design/14"
import hashlib, json, sys
path, h, export, basic, energy = sys.argv[1:]
text = open(path).read()
assert "sha256:" + hashlib.sha256(text.encode()).hexdigest() == h
m = json.loads(text)
assert m["schema"] == "leanblame.release.1" and m["tag"] == "2026.10" and m["export"] == export
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
! grep -q "copying" "$logs/export.log" || fail "no module changed, yet export copied: $(cat "$logs/export.log")"
run status --json
python3 -c 'import json, sys; assert json.loads(sys.argv[1])["commit"] is None' "$out" \
  || fail "status --json: an export of uncommitted changes names a commit"
must_fail "the current export has uncommitted changes" -- "$lb" sign --signer local:alice
must_fail "release: the current export has uncommitted changes" -- "$lb" release --tag 2026.10.2
rm notes.txt
export_lib
ok "an untracked file: the export names no commit; sign and release refuse it; no module is copied again"

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
export_lib
[[ "$(current_export)" != "$before" ]] || fail "the proof edit did not change the export"
grep -q "copying 2 of 3 modules" "$logs/export.log" || fail "want Sample.Energy and Sample copied again: $(cat "$logs/export.log")"
run status
expect_line Sample.second_site "Sample.second_site valid"
ok "a proof inside a statement is not part of the hash; only its module and the one importing it are copied again"

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

echo "== withdraw"
run sign --withdraw "$basic_record" --signer local:alice --note "energy was wrong"
grep -q "^withdraw sha256:" <<<"$out" || fail "no withdraw record: $out"
withdraw_record="$(awk '/^withdraw /{print $2}' <<<"$out")"
must_fail "only its signer can withdraw it" -- "$lb" sign --withdraw "$basic_record" --signer local:bob
ok "only the signer can withdraw"
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
d = json.loads(sys.argv[1])["declarations"]["Sample.second_site"]
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
grep -q "^Sample.Point  inductive  " <<<"$out" || fail "blame by label: $out"
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
run status --json
python3 - "$out" "$(id_of Sample.second_site)" <<'PY' || fail "rename: $out"
import json, sys
d = json.loads(sys.argv[1])["declarations"]
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

rm -rf "$work" "$logs"
echo "PASS ($pass checks)"
