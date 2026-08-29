#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  printf 'usage: %s /path/to/candle.sh /path/to/flyspeck\n' "$0" >&2
  exit 2
fi

test_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
candle_script=$(realpath -- "$1")
flyspeck_root=$(realpath -- "$2")
candle_root=$(cd -- "$(dirname -- "$candle_script")" && pwd)
log=$(mktemp /tmp/candle-flyspeck-source-digests.XXXXXX.log)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    tail -n 100 "$log" >&2 2>/dev/null || true
  fi
  find "$log" -maxdepth 0 -type f -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

(
  cd -- "$candle_root"
  timeout 1200 "$candle_script" >"$log" 2>&1 <<EOF
let candle_flyspeck_test_flyspeck_root = "$flyspeck_root";;
#use "$test_dir/test_flyspeck_source_digests.ml";;
EOF
)

rg -Fq 'CANDLE_FLYSPECK_SOURCE_DIGESTS_OK' "$log"
if rg -a -q 'Parsing failed|ERROR:|Undefined variable:' "$log"; then
  tail -n 100 "$log" >&2
  exit 1
fi
printf 'PASS: compiled Candle verifies all selected source digests and rejects corruption\n'
