#!/usr/bin/env bash
# End-to-end test of the leanblame CLI on test/Sample.
#
#   cli/test/run.sh            # from anywhere; needs elan (Lean 4.35.0), git, python3
#
# Copies the sample library to a scratch directory, makes it a git repository,
# and walks through: init -> export -> sign -> status (valid) -> edit a body
# -> status (outdated, own-body) -> edit a dependency body -> status (blocked)
# -> more causes (untagged, own-text, dep-spec) -> withdraw -> status
# (withdrawn) -> blame -> validate (and its append-only check).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cli="$(cd "$here/.." && pwd)"

pass=0
fail() { echo "FAIL: $*" >&2; echo "work directory kept: $work" >&2; exit 1; }
ok() { pass=$((pass + 1)); echo "  ok: $*"; }

echo "== build leanblame"
(cd "$cli" && lake build) >/dev/null
lb="$cli/.lake/build/bin/leanblame"
(cd "$cli" && lake env lean --run test/Canon.lean) || fail "canonical printing (test/Canon.lean)"
ok "canonical printing is linear in the term as a graph"

work="$(mktemp -d "${TMPDIR:-/tmp}/leanblame-test.XXXXXX")"
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
run() { out="$("$lb" "$@" 2>>"$work/stderr.log")" || { tail -20 "$work/stderr.log" >&2; fail "leanblame $*"; }; }
# Assert that the status line of a declaration is exactly the given text.
expect_line() {
  local name="$1" want="$2" got
  got="$(grep "^$name " <<<"$out" || true)"
  [[ "$got" == "$want" ]] || fail "status line for $name: want '$want', got '$got'"
  ok "$want"
}
export_lib() { "$lb" export >/dev/null 2>"$work/export.log" || { cat "$work/export.log" >&2; fail "export"; }; }
# Edit a file in place with a sed expression.
edit() { sed -i.bak "$2" "$1" && rm "$1.bak"; }
# Run a command that must fail, and whose output (stdout and stderr) must match every pattern.
must_fail() {
  local patterns=()
  while [[ "$1" != "--" ]]; do patterns+=("$1"); shift; done
  shift
  if "$@" >"$work/fail.log" 2>&1; then fail "should have failed: $*"; fi
  for p in "${patterns[@]}"; do
    grep -q -- "$p" "$work/fail.log" || fail "$*: no '$p' in: $(cat "$work/fail.log")"
  done
}
current_export() { python3 -c 'import json; print(json.load(open(".leanblame/current"))["exportHash"])'; }

echo "== init"
run init
for f in leanblame.toml records .github/workflows/leanblame.yml; do
  [[ -e "$f" ]] || fail "init did not create $f"
done
grep -qx ".leanblame/" .gitignore || fail "init did not ignore .leanblame/"
grep -qx "/.lake/" .gitignore || fail "init dropped the existing .gitignore entries"
ok "init created leanblame.toml, records/, the CI job, .gitignore entry"
commit "sample library"

echo "== export"
export_lib
[[ "$(current_export)" =~ ^sha256:[0-9a-f]{64}$ ]] || fail "no current export"
first_export="$(current_export)"
ok "export stored $first_export"

echo "== sign"
run sign --signer local:alice --note "first review"
[[ "$(grep -c '^approve ' <<<"$out")" == 2 ]] || fail "expected one approve record per module: $out"
basic_record="$(awk '/of Sample.Basic\)$/ {print $2}' <<<"$out")"
energy_record="$(awk '/of Sample.Energy\)$/ {print $2}' <<<"$out")"
ok "two approve records, Sample.Basic is $basic_record"
run validate
ok "validate: $out"
commit "first signoff"

echo "== status: everything valid"
out="$("$lb" status 2>"$work/status.err")"
for n in Sample.Point Sample.Point.mk Sample.Point.x Sample.Point.y Sample.Point.norm \
         Sample.energy Sample.energy_even Sample.pointEnergy Sample.second_site; do
  expect_line "$n" "$n valid"
done
want="warning: untagged Sample.double of this library is used by tagged Sample.energy; tag it so it gets its own signer"
grep -qxF "$want" "$work/status.err" || fail "no untagged-dependency warning: $(cat "$work/status.err")"
[[ "$(grep -c '^warning' "$work/status.err")" == 1 ]] || fail "unexpected warnings: $(cat "$work/status.err")"
ok "status warns that tagged Sample.energy uses untagged Sample.double, and nothing else"
run status --json
python3 - "$out" <<'PY' || fail "status --json does not match docs/14"
import json, sys
s = json.loads(sys.argv[1])
assert s["schema"] == "leanblame.status.1"
assert set(s) == {"schema", "library", "commit", "export", "generated", "declarations"}
keys = {"module", "kind", "informal", "informal_source", "claim", "state", "flags", "change",
        "signers", "history", "blocked_by", "proof", "evidence", "tagged_deps", "closure_size"}
for name, d in s["declarations"].items():
    assert set(d) == keys, (name, set(d) ^ keys)
    assert d["state"] == "valid" and d["signers"] == ["local:alice"], name
    want = {"Sample.energy_even": "open", "Sample.second_site": "proven"}.get(name, "n/a")
    assert d["proof"]["status"] == want, (name, d["proof"])
    assert d["proof"]["export"] == (s["export"] if d["kind"] == "theorem" else None), name
    assert d["history"][0]["action"] == "approve" and d["history"][0]["claim"] == d["claim"], name
assert s["declarations"]["Sample.energy_even"]["tagged_deps"] == ["Sample.energy"]
assert s["declarations"]["Sample.energy_even"]["proof"]["axioms"] == ["sorryAx"]
PY
ok "status --json has the docs/14 fields; the proof field shows proven and open theorems"

echo "== edit a proof inside a statement: second_site"
edit Sample/Energy.lean 's/2, by decide/2, by omega/'
grep -q "by omega" Sample/Energy.lean || fail "test setup: proof not swapped"
commit "second_site: another proof of 2 < 3 in the statement"
before="$(current_export)"
export_lib
[[ "$(current_export)" != "$before" ]] || fail "the proof edit did not change the export"
run status
expect_line Sample.second_site "Sample.second_site valid"
run status --base "$energy_record"
expect_line Sample.second_site "Sample.second_site valid"
ok "a proof inside a statement is not part of the hash"

echo "== edit a body: pointEnergy"
edit Sample/Energy.lean 's/:= energy p.norm$/:= energy p.norm * 1/'
commit "pointEnergy: new body"
export_lib
run status
expect_line Sample.pointEnergy "Sample.pointEnergy outdated change=own-body:Sample.pointEnergy"
expect_line Sample.energy_even "Sample.energy_even valid"
# --base compares with the export and boundary list an approve record names.
run status --base "$energy_record"
expect_line Sample.pointEnergy "Sample.pointEnergy outdated change=own-body:Sample.pointEnergy"
must_fail "no such record" -- "$lb" status --base "$(current_export)"
ok "--base takes a record, not an export"

echo "== edit a dependency body: energy"
edit Sample/Basic.lean 's/@\[trusted\] def energy (n : Nat) : Nat := double n/@[trusted] def energy (n : Nat) : Nat := double n + 0/'
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
run status --base "$basic_record"
expect_line Sample.energy \
  "Sample.energy outdated change=own-text:Sample.energy;own-body:Sample.energy;untagged:Sample.double"
ok "a docstring edit keeps the export; --base RECORD compares with the record's boundary list"
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
expect_line Sample.energy "Sample.energy unsigned flags=withdrawn"
expect_line Sample.Point "Sample.Point unsigned flags=withdrawn blocked-by=Sample.Point.mk"
expect_line Sample.energy_even \
  "Sample.energy_even outdated blocked-by=Sample.energy change=dep-spec:Sample.energy"

echo "== a withdrawal cannot be excluded"
edit leanblame.toml "s|^exclude = \[\]|exclude = [\"$withdraw_record\"]|"
grep -q '^exclude = \["sha256:' leanblame.toml || fail "test setup: exclude not set"
must_fail "withdrawals cannot be excluded" -- "$lb" validate
run status
expect_line Sample.energy "Sample.energy unsigned flags=withdrawn"
git checkout -q -- leanblame.toml
ok "excluding a withdraw record fails validate and does not revive the approval"

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
"$lb" status >/dev/null 2>"$work/status.err" || fail "status with a misnamed file in records/"
grep -q "records/notes.toml is not a valid record and was ignored" "$work/status.err" \
  || fail "status did not warn about the misnamed file: $(cat "$work/status.err")"
rm records/notes.toml
ok "a misnamed file is a problem for validate and a warning for status"
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

echo "== stubs"
for args in equiv release "export --boundary blueprint-manifest.json" "export --boundary manual.toml"; do
  set +e; "$lb" $args >/dev/null 2>"$work/stub.log"; code=$?; set -e
  [[ "$code" == 2 ]] || fail "$args should exit 2, got $code"
  grep -q "not implemented" "$work/stub.log" || fail "$args: $(cat "$work/stub.log")"
  ok "$args says not implemented and exits 2"
done

rm -rf "$work"
echo "PASS ($pass checks)"
