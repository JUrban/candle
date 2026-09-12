#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-marchal3-open.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

ocaml -noinit -noprompt \
  <"$fixture_root/marchal3_open_resolution_original.ml" \
  >"$test_dir/native.log" 2>&1

(
  cd "$candle_runtime_cwd"
  printf '#use "%s";;\n' \
    "$fixture_root/marchal3_open_resolution_original.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/original.log" 2>&1
)

(
  cd "$candle_runtime_cwd"
  printf '#use "%s";;\n' \
    "$fixture_root/marchal3_open_resolution_normalized.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/normalized.log" 2>&1
)

rg -Fq 'val candle_marchal3_native_open_resolution_ok : bool = true' \
  "$test_dir/native.log"
rg -Fq 'val candle_marchal3_native_open_resolution_ok = false: bool' \
  "$test_dir/original.log"
rg -Fq 'val candle_marchal3_open_resolution_ok = true: bool' \
  "$test_dir/normalized.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' \
  "$test_dir/original.log" "$test_dir/normalized.log"; then
  tail -n 80 "$test_dir/original.log" "$test_dir/normalized.log" >&2
  exit 1
fi

printf 'PASS: Flyspeck Marchal3 native open-resolution normalization\n'
