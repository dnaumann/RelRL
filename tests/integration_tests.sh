#!/bin/bash
# integration_tests.sh -- Integration tests for the whyrel compiler pipeline
# Runs whyrel on fixture files and example programs, checks exit codes and output.

set -euo pipefail

WHYREL="${WHYREL:-./bin/whyrel}"
FIXTURES="tests/fixtures"
EXAMPLES="examples"
PASS=0
FAIL=0
ERRORS=()

# ---- helpers ----------------------------------------------------------------

pass() {
  echo "  PASS: $1"
  PASS=$((PASS + 1))
}

fail() {
  echo "  FAIL: $1 -- $2"
  FAIL=$((FAIL + 1))
  ERRORS+=("$1: $2")
}

# Run whyrel with given flags on a file; expect success (exit 0)
expect_success() {
  local label="$1"
  local flags="$2"
  local file="$3"
  if "$WHYREL" $flags "$file" >/dev/null 2>&1; then
    pass "$label"
  else
    fail "$label" "expected success but got non-zero exit"
  fi
}

# Run whyrel with given flags on a file; expect failure (non-zero exit)
expect_failure() {
  local label="$1"
  local flags="$2"
  local file="$3"
  if "$WHYREL" $flags "$file" >/dev/null 2>&1; then
    fail "$label" "expected failure but got exit 0"
  else
    pass "$label"
  fi
}

# Run whyrel and check that stderr contains a given pattern
expect_stderr_contains() {
  local label="$1"
  local flags="$2"
  local file="$3"
  local pattern="$4"
  local stderr
  stderr=$("$WHYREL" $flags "$file" 2>&1 >/dev/null || true)
  if echo "$stderr" | grep -q "$pattern"; then
    pass "$label"
  else
    fail "$label" "expected stderr to contain '$pattern', got: $stderr"
  fi
}

# ---- fixture tests ----------------------------------------------------------

echo "=== Fixture: parse-only tests ==="

expect_success "parse valid_simple.rl"         "-parse" "$FIXTURES/valid_simple.rl"
expect_success "parse valid_bimodule.rl"       "-parse" "$FIXTURES/valid_bimodule.rl"
expect_success "parse valid_empty_interface.rl" "-parse" "$FIXTURES/valid_empty_interface.rl"
expect_failure "parse parse_error.rl"          "-parse" "$FIXTURES/parse_error.rl"

echo ""
echo "=== Fixture: type-check tests ==="

expect_success "type-check valid_simple.rl"          "-type-check" "$FIXTURES/valid_simple.rl"
expect_success "type-check valid_bimodule.rl"        "-type-check" "$FIXTURES/valid_bimodule.rl"
expect_success "type-check valid_empty_interface.rl" "-type-check" "$FIXTURES/valid_empty_interface.rl"
expect_failure "type-check type_error.rl"            "-type-check" "$FIXTURES/type_error.rl"
expect_stderr_contains \
  "type_error.rl produces type error message" \
  "-type-check" "$FIXTURES/type_error.rl" "Type error"

echo ""
echo "=== Fixture: full translation tests ==="

# Translate valid programs (write to /dev/null)
TMP=$(mktemp /tmp/whyrel_test_XXXXXX.mlw)
trap 'rm -f $TMP' EXIT

if "$WHYREL" "$FIXTURES/valid_simple.rl" -o "$TMP" 2>/dev/null; then
  if [ -s "$TMP" ]; then
    pass "translate valid_simple.rl produces non-empty output"
  else
    fail "translate valid_simple.rl produces non-empty output" "output file is empty"
  fi
else
  fail "translate valid_simple.rl" "translation failed"
fi

if "$WHYREL" "$FIXTURES/valid_bimodule.rl" -o "$TMP" 2>/dev/null; then
  pass "translate valid_bimodule.rl succeeds"
else
  fail "translate valid_bimodule.rl" "translation failed"
fi

echo ""
echo "=== Example: all_all suite ==="

for example in factorial fibonacci swap; do
  prog="$EXAMPLES/all_all/$example/prog.rl"
  if [ -f "$prog" ]; then
    expect_success "parse $example"      "-parse"      "$prog"
    expect_success "type-check $example" "-type-check" "$prog"
  fi
done

echo ""
echo "=== Example: all_exists suite ==="

for example in CCR Havoc_Test; do
  prog="$EXAMPLES/all_exists/$example/prog.rl"
  if [ -f "$prog" ]; then
    expect_success "parse $example (all_exists)"      "-parse"      "$prog"
    expect_success "type-check $example (all_exists)" "-type-check" "$prog"
  fi
done

echo ""
echo "=== Version flag ==="

if "$WHYREL" -version 2>&1 | grep -q "WhyRel"; then
  pass "version flag prints WhyRel"
else
  fail "version flag" "expected 'WhyRel' in output"
fi

echo ""
echo "=== No files: exits cleanly ==="

if "$WHYREL" >/dev/null 2>&1; then
  pass "no-file invocation exits 0"
else
  fail "no-file invocation" "expected exit 0"
fi

echo ""
echo "=== Summary ==="
echo "  Passed: $PASS"
echo "  Failed: $FAIL"
if [ ${#ERRORS[@]} -gt 0 ]; then
  echo ""
  echo "  Failures:"
  for err in "${ERRORS[@]}"; do
    echo "    - $err"
  done
fi

[ "$FAIL" -eq 0 ]
