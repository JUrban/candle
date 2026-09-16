#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-inequalities-goal.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

ocaml -noinit -noprompt \
  <"$fixture_root/inequalities_goal_effect_ocaml_oracle.ml" \
  >"$test_dir/native.log" 2>&1
rg -Fq 'INEQUALITIES_GOAL_EFFECT_OCAML_ORACLE_OK' "$test_dir/native.log"

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' \
    "$fixture_root/inequalities_goal_effect_original.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/original.log" 2>&1
)
(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' \
    "$fixture_root/inequalities_goal_effect_normalized.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/normalized.log" 2>&1
)

rg -Fq 'val candle_inequalities_goal_original_ok = true: bool' \
  "$test_dir/original.log"
rg -Fq 'val candle_inequalities_goal_effect_ok = true: bool' \
  "$test_dir/normalized.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/original.log"; then
  tail -n 50 "$test_dir/original.log" >&2
  exit 1
fi
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/normalized.log"; then
  tail -n 50 "$test_dir/normalized.log" >&2
  exit 1
fi

printf 'PASS: Flyspeck Inequalities raw/wrapped goal structure effects\n'
