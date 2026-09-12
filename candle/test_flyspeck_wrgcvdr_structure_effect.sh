#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-wrgcvdr-structure.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

ocaml -noinit -noprompt \
  <"$fixture_root/wrgcvdr_structure_effect_ocaml_oracle.ml" \
  >"$test_dir/native.log" 2>&1
rg -Fq 'WRGCVDR_STRUCTURE_EFFECT_OCAML_ORACLE_OK' "$test_dir/native.log"

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' \
    "$fixture_root/wrgcvdr_structure_effect_original.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/original.log" 2>&1
)
(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' \
    "$fixture_root/wrgcvdr_theorem_effect_original.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/theorem-original.log" 2>&1
)
(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' \
    "$fixture_root/wrgcvdr_theorem_effect_normalized.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/theorem-normalized.log" 2>&1
)
(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' \
    "$fixture_root/wrgcvdr_structure_effect_normalized.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/normalized.log" 2>&1
)

rg -Fq 'Type mismatch between thm and' "$test_dir/original.log"
rg -Fq 'Type mismatch between thm and' "$test_dir/theorem-original.log"
rg -Fq 'val candle_wrgcvdr_structure_effect_ok = true: bool' \
  "$test_dir/normalized.log"
rg -Fq 'val candle_wrgcvdr_theorem_effect_ok = true: bool' \
  "$test_dir/theorem-normalized.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/normalized.log"; then
  tail -n 50 "$test_dir/normalized.log" >&2
  exit 1
fi
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/theorem-normalized.log"; then
  tail -n 50 "$test_dir/theorem-normalized.log" >&2
  exit 1
fi

printf 'PASS: Flyspeck WRGCVDR structure-effect normalization\n'
