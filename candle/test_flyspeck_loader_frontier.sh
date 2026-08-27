#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 3 ]]; then
  printf 'usage: %s /path/to/candle.sh /path/to/flyspeck /path/to/overlay\n' "$0" >&2
  exit 2
fi

loader_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
candle_script=$(realpath -- "$1")
flyspeck_root=$(realpath -- "$2")
overlay_root=$(realpath -- "$3")
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
let candle_flyspeck_overlay_root = "$overlay_root";;
let candle_flyspeck_build_mode = "full";;
#use "$loader_dir/flyspeck_loader.ml";;
EOF
)

rg -Fq -- '- Selecting statically linked library unix.cma (module Unix)' "$log"
rg -Fq -- '- Selecting statically linked library str.cma (module Str)' "$log"
rg -Fq -- '- Selecting normalized source' "$log"
rg -Fq 'val loaded_files = <ref>: (string * string) list ref' "$log"
rg -Fq 'val file_on_path = <fun>: string list -> string -> string' "$log"
rg -Fq 'val load_on_path_b = <fun>: string list -> string -> bool' "$log"
rg -Fq -- '- Selecting normalized source '"$flyspeck_root"'/text_formalization/general/parser_verbose.hl' "$log"
rg -Fq -- '- Loading '"$overlay_root"'/text_formalization/general/parser_verbose.hl' "$log"
rg -Fq -- '- Flyspeck source action complete: general/parser_verbose.hl' "$log"
rg -Fq -- '- Selecting normalized source '"$flyspeck_root"'/text_formalization/general/debug.hl' "$log"
rg -Fq -- '- Loading '"$overlay_root"'/text_formalization/general/debug.hl' "$log"
rg -Fq 'open-declarations are not supported (yet)' "$log"
rg -Fq 'Parsing failed at line 16' "$log"
if rg -q 'Parsing failed at line (23|90)|Or-patterns are not allowed in let|Undefined variable: sprintf|Expected to be at EOF|Static #load rejected|No such file: .*\.cma' "$log"; then
  tail -n 60 "$log" >&2
  exit 1
fi
if rg -q 'Undefined variable: (Sys\.(configure_manifest_environment|file_exists)|Filename\.concat|load_path|loadt|file_on_path|loaded_files|Toploop\.use_file)' "$log"; then
  tail -n 60 "$log" >&2
  exit 1
fi
if rg -q 'CANDLE_FLYSPECK_DIRECT_FULL_OK|build/strictbuild\.hl.*successfully loaded|- Flyspeck source action complete: general/debug\.hl' "$log"; then
  tail -n 40 "$log" >&2
  exit 1
fi
printf 'EXPECTED GAP: full loader stops at verified Dopen frontier\n'
