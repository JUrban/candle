#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  printf 'usage: %s /path/to/candle.sh\n' "$0" >&2
  exit 2
fi

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
candle_script=$(realpath -- "$1")
[[ -x $candle_script ]] || {
  printf 'Candle launcher is not executable: %s\n' "$candle_script" >&2
  exit 2
}

log=$(mktemp /tmp/candle-multiline-string.XXXXXX.log)
cleanup() {
  result=$?
  if [[ $result -ne 0 && -f $log ]]; then
    tail -n 80 "$log" >&2
  fi
  find "$log" -maxdepth 0 -type f -delete 2>/dev/null || true
}
trap cleanup EXIT

(
  cd -- "$(dirname -- "$candle_script")"
  timeout 300 "$candle_script" >"$log" 2>&1 <<EOF
#use "$script_dir/compatibility/oracles/multiline_string.ml";;
let () =
  if candle_multiline_string = "alpha" ^ "\n" ^ "beta"
  then print_endline "CANDLE_MULTILINE_STRING_OK"
  else failwith "multiline string mismatch";;
EOF
)

rg -q '^CANDLE_MULTILINE_STRING_OK$' "$log"
if rg -q 'LEXER ERROR|Parsing failed|^ERROR:|^EXCEPTION:' "$log"; then
  exit 1
fi
printf 'multiline string runtime smoke PASS\n'
