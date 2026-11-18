#!/usr/bin/env bash
# Test suite for lean-js.
#
#   Test/run.sh            run all tests
#   Test/run.sh --update   regenerate the golden files in Test/expected/
#
# Requires the executable to be built (`lake build lean-js`). The Node.js
# behavioural tests are skipped (with a warning) if `node` is not installed.
set -uo pipefail
cd "$(dirname "$0")/.."

EXE=.lake/build/bin/lean-js
EXPECTED=Test/expected
UPDATE=0
[[ "${1:-}" == "--update" ]] && UPDATE=1

pass=0; fail=0
ok()  { pass=$((pass + 1)); }
bad() { fail=$((fail + 1)); echo "FAIL: $*"; }

if [[ ! -x "$EXE" ]]; then
  echo "error: $EXE not found; run 'lake build lean-js' first" >&2
  exit 2
fi

# ---------------------------------------------------------------- golden tests
golden() {  # golden <command> <file>
  local cmd=$1 file=$2
  local name; name="$(echo "${file#Test/}" | tr / _).$cmd"
  local actual; actual="$("$EXE" "$cmd" "$file" 2>&1; echo "[exit $?]")"
  if [[ $UPDATE == 1 ]]; then
    printf '%s\n' "$actual" > "$EXPECTED/$name"
    ok
  elif [[ ! -f "$EXPECTED/$name" ]]; then
    bad "$name: no golden file (run Test/run.sh --update)"
  elif diff -u "$EXPECTED/$name" <(printf '%s\n' "$actual") > /tmp/lean-js-diff.$$; then
    ok
  else
    bad "$name differs from golden output:"; cat /tmp/lean-js-diff.$$
  fi
  rm -f /tmp/lean-js-diff.$$
}

for f in Test/Fixtures/*.js Test/Core/*.js; do
  for cmd in parse ir roundtrip lean lean-expr check; do golden "$cmd" "$f"; done
done
for f in Test/Fixtures/*.lean Test/Core/*.lean; do
  for cmd in lean-roundtrip lean-ir-roundtrip js check; do golden "$cmd" "$f"; done
done

# ------------------------------------------- core fixtures use the verified path
for f in Test/Core/*.js; do
  if "$EXE" roundtrip "$f" 2>&1 >/dev/null | grep -q '^\[verified\]'; then ok
  else bad "$f: roundtrip did not use the verified translator"; fi
done
for f in Test/Core/*.lean; do
  if "$EXE" js "$f" 2>&1 >/dev/null | grep -q '^\[verified\]'; then ok
  else bad "$f: js did not use the verified translator"; fi
done

# ------------------------------------------------- behavioural tests (Node.js)
if command -v node > /dev/null; then
  tmp=$(mktemp -d)
  harness='console.log(JSON.stringify(result));'
  for f in Test/Core/*.js; do
    { cat "$f"; echo; echo "$harness"; } > "$tmp/orig.js"
    { "$EXE" roundtrip "$f" 2>/dev/null; echo "$harness"; } > "$tmp/rt.js"
    a=$(node "$tmp/orig.js" 2>&1); b=$(node "$tmp/rt.js" 2>&1)
    if [[ "$a" == "$b" ]]; then ok
    else bad "$f: original prints $a but round trip prints $b"; fi
  done
  for f in Test/Core/*.lean; do
    { "$EXE" js "$f" 2>/dev/null; echo "$harness"; } > "$tmp/out.js"
    a=$(node "$tmp/out.js" 2>&1); b=$(cat "$f.expected")
    if [[ "$a" == "$b" ]]; then ok
    else bad "$f: translated JS prints $a, expected $b"; fi
  done
  rm -rf "$tmp"
else
  echo "warning: node not found; skipping behavioural tests" >&2
fi

# ------------------------------------------------------------- axiom audit
axioms=$(lake env lean Test/Axioms.lean 2>&1)
if echo "$axioms" | grep -q "sorryAx"; then
  bad "a correctness theorem depends on sorryAx:"; echo "$axioms" | grep sorryAx
elif echo "$axioms" | grep -q "error"; then
  bad "axiom audit failed to run:"; echo "$axioms"
else
  ok
fi

echo "$pass passed, $fail failed"
[[ $fail == 0 ]]
