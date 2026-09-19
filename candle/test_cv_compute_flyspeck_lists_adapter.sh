#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
candle_support_root=${CANDLE_SUPPORT_ROOT:-"$candle_root"}
test_dir=$(mktemp -d /tmp/candle-cv-flyspeck-lists-adapter.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    printf '%s\n' '--- Candle cv_compute Flyspeck list adapter log' >&2
    tail -n 240 "$test_dir/candle.log" >&2 2>/dev/null || true
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

(
  cd "$candle_runtime_cwd"
  printf 'Cakeml.loadPath := ["%s"; "%s"; Filename.currentDir];;\n#use "hol.ml";;\n#use "%s/candle/test_cv_compute_flyspeck_lists_adapter.ml";;\n' \
    "$candle_root" "$candle_support_root" "$candle_root" |
    timeout 1800 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

rg -Fq 'CANDLE_CV_FLYSPECK_LIST_ADAPTER_OK' "$test_dir/candle.log"
rg -Fq 'CANDLE_CV_FLYSPECK_LIST_BENCH_READY' "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed|Undefined variable:' \
  "$test_dir/candle.log"; then
  exit 1
fi

printf 'PASS: reflected list_of_faces preserves the ordinary theorem interface\n'
