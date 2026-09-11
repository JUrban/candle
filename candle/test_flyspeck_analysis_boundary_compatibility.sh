#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-analysis-boundary.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

ocaml -noinit -noprompt \
  <"$fixture_root/analysis_structure_effect_ocaml_oracle.ml" \
  >"$test_dir/ocaml.log" 2>&1
rg -Fq 'ANALYSIS_STRUCTURE_EFFECT_OCAML_ORACLE_OK' "$test_dir/ocaml.log"

run_candle() {
  local fixture=$1
  local output=$2
  (
    cd "$candle_runtime_cwd"
    timeout 60 "$candle_binary" --candle <"$fixture" >"$output" 2>&1
  )
}

run_candle "$fixture_root/analysis_theorem_phrase_original.ml" \
  "$test_dir/theorem-original.log"
run_candle "$fixture_root/analysis_unit_phrase_original.ml" \
  "$test_dir/unit-original.log"
run_candle "$fixture_root/analysis_structure_effect_normalized.ml" \
  "$test_dir/normalized.log"

rg -Fq 'Type mismatch between candle_analysis_theorem' \
  "$test_dir/theorem-original.log"
rg -Fq 'Type mismatch between unit' "$test_dir/unit-original.log"
rg -Fq 'val candle_analysis_structure_effect_ok = true: bool' \
  "$test_dir/normalized.log"

if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/normalized.log"; then
  tail -n 60 "$test_dir/normalized.log" >&2
  exit 1
fi

printf 'PASS: analysis boundary structure-effect compatibility oracles\n'
