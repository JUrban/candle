#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle.sh"}
: "${FLYSPECK_ROOT:?set FLYSPECK_ROOT to the pinned Flyspeck checkout}"
temporary=$(mktemp -d)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    for log in "$temporary"/*.log; do
      printf '%s\n' "--- $log" >&2
      tail -n 80 "$log" >&2 2>/dev/null || true
    done
  fi
  rm -rf -- "$temporary"
  exit "$status"
}
trap cleanup EXIT

python3 "$candle_root/candle/flyspeck_normalize.py" \
  --flyspeck-root "$FLYSPECK_ROOT" --check

ocaml -noinit -noprompt \
  "$candle_root/candle/flyspeck_set_make_ocaml_oracle.ml" \
  >"$temporary/ocaml.log" 2>&1
timeout 90 "$candle_binary" \
  <"$candle_root/candle/flyspeck_set_make_normalized_oracle.ml" \
  >"$temporary/candle.log" 2>&1

rg -Fq 'flyspeck-set-make-ocaml-oracle: ok' "$temporary/ocaml.log"
rg -Fq 'candle_flyspeck_set_make_normalized_oracle_ok = true' \
  "$temporary/candle.log"
! rg -q 'EXCEPTION:|Parsing failed|ERROR:|Undefined (variable|module):' \
  "$temporary/candle.log"

printf 'PASS: exact Flyspeck Serialization.Set.Make replacement\n'
