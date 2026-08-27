#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  printf 'usage: %s /path/to/candle.sh /path/to/flyspeck\n' "$0" >&2
  exit 2
fi

loader_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
candle_script=$(realpath -- "$1")
flyspeck_root=$(realpath -- "$2")
candle_root=$(cd -- "$(dirname -- "$candle_script")" && pwd)
log=$(mktemp /tmp/candle-flyspeck-loader-frontier.XXXXXX.log)
cleanup() {
  find "$log" -maxdepth 0 -type f -delete 2>/dev/null || true
}
trap cleanup EXIT

(
  cd -- "$(dirname -- "$candle_script")"
  timeout 300 "$candle_script" >"$log" 2>&1 <<EOF
let candle_flyspeck_root = "$flyspeck_root";;
let candle_hollight_root = "$candle_root";;
let candle_flyspeck_build_mode = "full";;
#use "$loader_dir/flyspeck_loader.ml";;
EOF
)

rg -Fq -- '- Selecting statically linked library unix.cma (module Unix)' "$log"
rg -Fq -- '- Selecting statically linked library str.cma (module Str)' "$log"
rg -Fq 'ERROR: Undefined variable: Toploop.use_file at line 7' "$log"
if rg -q 'Parsing failed at line 23|Static #load rejected|No such file: .*\.cma' "$log"; then
  tail -n 60 "$log" >&2
  exit 1
fi
if rg -q 'Undefined variable: (Sys\.(configure_manifest_environment|file_exists)|Filename\.concat|load_path)' "$log"; then
  tail -n 60 "$log" >&2
  exit 1
fi
if rg -q 'CANDLE_FLYSPECK_DIRECT_FULL_OK|build/strictbuild\.hl.*successfully loaded' "$log"; then
  tail -n 40 "$log" >&2
  exit 1
fi
printf 'EXPECTED GAP: full loader stops at strictbuild Toploop.use_file\n'
