#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-ajripqn-open.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

ocaml -noinit -noprompt \
  <"$fixture_root/ajripqn_open_resolution_original.ml" \
  >"$test_dir/native.log" 2>&1

(
  cd "$candle_runtime_cwd"
  printf '#use "%s";;\n' \
    "$fixture_root/ajripqn_open_resolution_original.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/original.log" 2>&1
)
(
  cd "$candle_runtime_cwd"
  printf '#use "%s";;\n' \
    "$fixture_root/ajripqn_open_resolution_normalized.ml" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/normalized.log" 2>&1
)

rg -Fq 'val candle_ajripqn_native_resolution_ok : bool = true' \
  "$test_dir/native.log"
rg -Fq 'Type mismatch between bool and' "$test_dir/original.log"
rg -Fq 'val candle_ajripqn_open_resolution_ok = true: bool' \
  "$test_dir/normalized.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/normalized.log"; then
  tail -n 50 "$test_dir/normalized.log" >&2
  exit 1
fi

printf 'PASS: Flyspeck AJRIPQN native open-resolution normalization\n'
