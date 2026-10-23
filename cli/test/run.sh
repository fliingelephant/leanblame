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

work="$(mktemp -d "${TMPDIR:-/tmp}/leanblame-test.XXXXXX")"
cp -R "$here/Sample/Sample" "$here/Sample/Sample.lean" "$here/Sample/lean-toolchain" "$work/"
# Point the dependency on the attribute at this checkout.
sed "s|path = \"../..\"|path = \"$cli\"|" "$here/Sample/lakefile.toml" > "$work/lakefile.toml"
cd "$work"
git init -q
git config user.name "LeanBlame test"
git config user.email "test@example.invalid"
commit() { git add -A && git commit -qm "$1"; }

# Run a leanblame command; its stdout goes to $out.
run() { out="$("$lb" "$@")"; }
# Assert that the status line of a declaration is exactly the given text.
expect_line() {
  local name="$1" want="$2" got
  got="$(grep "^$name " <<<"$out" || true)"
  [[ "$got" == "$want" ]] || fail "status line for $name: want '$want', got '$got'"
  ok "$want"
}
export_lib() { "$lb" export >/dev/null 2>"$work/export.log" || { cat "$work/export.log" >&2; fail "export"; }; }

echo "== init"
run init
for f in leanblame.toml records/.gitkeep .github/workflows/leanblame.yml; do
  [[ -e "$f" ]] || fail "init did not create $f"
done
grep -qx ".leanblame/" .gitignore || fail "init did not ignore .leanblame/"
ok "init created leanblame.toml, records/, the CI job, .gitignore entry"
commit "sample library"

echo "== export"
export_lib
grep -q "^export sha256:[0-9a-f]\{64\}$" .leanblame/current || fail "no current export"
ok "export stored $(head -1 .leanblame/current)"

echo "== sign"
run sign --signer local:alice --note "first review"
[[ "$(grep -c '^approve ' <<<"$out")" == 2 ]] || fail "expected one approve record per module: $out"
basic_record="$(awk '/of Sample.Basic\)$/ {print $2}' <<<"$out")"
ok "two approve records, Sample.Basic is $basic_record"
run validate
ok "validate: $out"
commit "first signoff"

echo "== status: everything valid"
run status
for n in Sample.Point Sample.Point.mk Sample.Point.x Sample.Point.y Sample.Point.norm \
         Sample.energy Sample.energy_even Sample.pointEnergy; do
  expect_line "$n" "$n valid"
done
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
    assert d["proof"]["status"] == ("unchecked" if d["kind"] == "theorem" else "n/a"), name
    assert d["history"][0]["action"] == "approve" and d["history"][0]["claim"] == d["claim"], name
assert s["declarations"]["Sample.energy_even"]["tagged_deps"] == ["Sample.energy"]
PY
ok "status --json has the docs/14 fields"

echo "== edit a body: pointEnergy"
sed -i.bak 's/:= energy p.norm$/:= energy p.norm * 1/' Sample/Energy.lean && rm Sample/Energy.lean.bak
commit "pointEnergy: new body"
export_lib
run status
expect_line Sample.pointEnergy "Sample.pointEnergy outdated change=own-body:Sample.pointEnergy"
expect_line Sample.energy_even "Sample.energy_even valid"

echo "== edit a dependency body: energy"
sed -i.bak 's/@\[trusted\] def energy (n : Nat) : Nat := double n/@[trusted] def energy (n : Nat) : Nat := double n + 0/' Sample/Basic.lean
rm Sample/Basic.lean.bak
commit "energy: new body"
export_lib
run status
expect_line Sample.energy "Sample.energy outdated change=own-body:Sample.energy"
expect_line Sample.energy_even "Sample.energy_even valid blocked-by=Sample.energy"
expect_line Sample.pointEnergy \
  "Sample.pointEnergy outdated blocked-by=Sample.energy change=own-body:Sample.pointEnergy"

echo "== edit an untagged helper: double"
sed -i.bak 's/def double (n : Nat) : Nat := n + n/def double (n : Nat) : Nat := 2 * n/' Sample/Basic.lean
rm Sample/Basic.lean.bak
commit "double: new body"
export_lib
run status
expect_line Sample.energy "Sample.energy outdated change=own-body:Sample.energy;untagged:Sample.double"

echo "== edit informal text: energy's docstring"
sed -i.bak 's/two units per site\./two units of energy per site./' Sample/Basic.lean && rm Sample/Basic.lean.bak
commit "energy: new docstring"
export_lib
run status
expect_line Sample.energy \
  "Sample.energy outdated change=own-text:Sample.energy;own-body:Sample.energy;untagged:Sample.double"
expect_line Sample.energy_even \
  "Sample.energy_even outdated blocked-by=Sample.energy change=dep-spec:Sample.energy"

echo "== withdraw"
run sign --withdraw "$basic_record" --signer local:alice --note "energy was wrong"
grep -q "^withdraw sha256:" <<<"$out" || fail "no withdraw record: $out"
if "$lb" sign --withdraw "$basic_record" --signer local:bob >/dev/null 2>&1; then
  fail "bob withdrew alice's record"
fi
ok "only the signer can withdraw"
run validate
ok "validate: $out"
commit "withdraw Sample.Basic"
run status
expect_line Sample.energy "Sample.energy unsigned flags=withdrawn"
expect_line Sample.Point "Sample.Point unsigned flags=withdrawn blocked-by=Sample.Point.mk"
expect_line Sample.energy_even \
  "Sample.energy_even outdated blocked-by=Sample.energy change=dep-spec:Sample.energy"

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
if "$lb" validate --base-ref HEAD >"$work/validate.log" 2>&1; then fail "an edited record passed validate"; fi
grep -q "existing record modified" "$work/validate.log" || fail "edit not reported: $(cat "$work/validate.log")"
grep -q "file name must be the sha256" "$work/validate.log" || fail "hash mismatch not reported"
git checkout -q -- "$record_file"
git rm -q "$record_file"
if "$lb" validate --base-ref HEAD >"$work/validate.log" 2>&1; then fail "a deleted record passed validate"; fi
grep -q "existing record deleted" "$work/validate.log" || fail "deletion not reported: $(cat "$work/validate.log")"
git checkout -q HEAD -- "$record_file"
ok "validate refuses modified and deleted records"

echo "== export refuses undocumented and unsafe tagged declarations"
cat >> Sample/Basic.lean <<'EOF'

namespace Sample
@[trusted] def undocumented (n : Nat) : Nat := n
/-- Unsafe code never reaches the kernel. -/
@[trusted] unsafe def unsafeEnergy (n : Nat) : Nat := n
end Sample
EOF
if "$lb" export >/dev/null 2>"$work/export.log"; then fail "export accepted bad tags"; fi
grep -q "Sample.undocumented: tagged declarations need a docstring" "$work/export.log" \
  || fail "missing docstring not reported: $(cat "$work/export.log")"
grep -q "Sample.unsafeEnergy: \`unsafe\` declarations cannot be tagged" "$work/export.log" \
  || fail "unsafe tag not reported: $(cat "$work/export.log")"
git checkout -q -- Sample/Basic.lean
ok "export refuses a tagged declaration without docstring and an unsafe one"

echo "== stubs"
for c in equiv release; do
  set +e; "$lb" "$c" >/dev/null 2>&1; code=$?; set -e
  [[ "$code" == 2 ]] || fail "$c should exit 2, got $code"
done
ok "equiv and release exit 2"

rm -rf "$work"
echo "PASS ($pass checks)"
