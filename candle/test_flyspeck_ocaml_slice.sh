#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle=${1:-"$candle_root/candle.sh"}
temporary=$(mktemp -d)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    printf 'Flyspeck OCaml slice gate failed with status %d; Candle tail follows:\n' \
      "$status" >&2
    tail -n 120 "$temporary/candle.log" >&2 2>/dev/null || true
  fi
  rm -rf -- "$temporary"
  exit "$status"
}
trap cleanup EXIT

(
  cd "$candle_root"
  timeout 1800 "$candle" <"$candle_root/candle/test_flyspeck_ocaml_slice.ml"
) >"$temporary/candle.log" 2>&1

rg -a -q 'CANDLE_FLYSPECK_OCAML_SLICE_OK' "$temporary/candle.log"
if rg -a -q 'EXCEPTION:|Parsing failed|ERROR:|Undefined variable:' \
  "$temporary/candle.log"; then
  tail -n 80 "$temporary/candle.log" >&2
  exit 1
fi

printf 'PASS: selected Flyspeck OCaml compatibility slice\n'
