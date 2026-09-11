#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-packing-term-setify.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' \
    "$fixture_root/packing_flat_term_setify_original.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/original.log" 2>&1
)
(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' \
    "$fixture_root/packing_flat_term_setify_normalized.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/normalized.log" 2>&1
)

rg -Fq 'Type mismatch between' "$test_dir/original.log"
rg -Fq 'val candle_packing_flat_term_setify_ok = true: bool' \
  "$test_dir/normalized.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/normalized.log"; then
  tail -n 50 "$test_dir/normalized.log" >&2
  exit 1
fi

printf 'PASS: Flyspeck packing term-setify normalization\n'
