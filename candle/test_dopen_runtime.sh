#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  printf 'usage: %s /path/to/candle.sh\n' "$0" >&2
  exit 2
fi

candle_script=$(realpath -- "$1")
[[ -x $candle_script ]] || {
  printf 'Candle launcher is not executable: %s\n' "$candle_script" >&2
  exit 2
}

source_file=$(mktemp /tmp/candle-dopen-runtime.XXXXXX.ml)
log=$(mktemp /tmp/candle-dopen-runtime.XXXXXX.log)
cleanup() {
  result=$?
  if [[ $result -ne 0 && -f $log ]]; then
    tail -n 80 "$log" >&2
  fi
  find "$source_file" "$log" -maxdepth 0 -type f -delete 2>/dev/null || true
}
trap cleanup EXIT

printf '%s\n' \
  'module M = struct' \
  '  type t = C | Comb of int * int;;' \
  '  let x = 7;;' \
  'end;;' \
  'let x = 1;;' \
  'open M;;' \
  'let opened_value = x;;' \
  'let qualified_value = M.x;;' \
  'let opened_constructor_value =' \
  '  match Comb (2,3) with C -> 0 | Comb (a,b) -> a + b;;' \
  'let x = 9;;' \
  'let later_shadow = x;;' \
  'module Outer = struct' \
  '  module Inner = struct' \
  '    let nested = 11;;' \
  '  end;;' \
  'end;;' \
  'open Outer.Inner;;' \
  'let opened_nested = nested;;' \
  'let () =' \
  '  if opened_value = 7 && qualified_value = 7 &&' \
  '     opened_constructor_value = 5 && later_shadow = 9 &&' \
  '     opened_nested = 11' \
  '  then print_endline "CANDLE_DOPEN_RUNTIME_OK"' \
  '  else failwith "Dopen runtime mismatch";;' \
  >"$source_file"

(
  cd -- "$(dirname -- "$candle_script")"
  timeout 300 "$candle_script" >"$log" 2>&1 <<EOF
#use "$source_file";;
EOF
)

rg -q '^CANDLE_DOPEN_RUNTIME_OK$' "$log"
if rg -q 'open-declarations are not supported|Parsing failed|^ERROR:|^EXCEPTION:' \
     "$log"; then
  exit 1
fi
printf 'Dopen runtime smoke PASS\n'
