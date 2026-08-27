#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  printf 'usage: %s /path/to/candle.sh /path/to/flyspeck\n' "$0" >&2
  exit 2
fi

loader_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
candle_script=$(realpath -- "$1")
flyspeck_root=$(realpath -- "$2")
log=$(mktemp /tmp/candle-flyspeck-loader-frontier.XXXXXX.log)
cleanup() {
  find "$log" -maxdepth 0 -type f -delete 2>/dev/null || true
}
trap cleanup EXIT

(
  cd -- "$(dirname -- "$candle_script")"
  timeout 180 "$candle_script" >"$log" 2>&1 <<EOF
let candle_flyspeck_root = "$flyspeck_root";;
let candle_flyspeck_build_mode = "full";;
#use "$loader_dir/flyspeck_loader.ml";;
EOF
)

rg -Fq 'ERROR: Undefined variable: Sys.file_exists' "$log"
if rg -q 'CANDLE_FLYSPECK_DIRECT_FULL_OK|build/strictbuild\.hl.*successfully loaded' "$log"; then
  tail -n 40 "$log" >&2
  exit 1
fi
printf 'EXPECTED GAP: full loader stops at missing Sys.file_exists compatibility\n'
