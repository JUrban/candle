#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle=${1:-"$candle_root/candle.sh"}
ocaml=${OCAML_414:-/project/repos/hol-light/_opam/bin/ocaml}
temporary=$(mktemp -d)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    printf 'Str compatibility gate failed with status %d; Candle tail follows:\n' \
      "$status" >&2
    wc -c "$temporary/oracle.log" "$temporary/candle.log" >&2 2>/dev/null || true
    tail -n 120 "$temporary/candle.log" >&2 2>/dev/null || true
  fi
  rm -rf -- "$temporary"
  exit "$status"
}
trap cleanup EXIT

"$ocaml" -noinit str.cma "$candle_root/candle/str_compat_oracle.ml" \
  >"$temporary/oracle.log" 2>&1
timeout 1800 "$candle" <"$candle_root/candle/test_str_compat.ml" \
  >"$temporary/candle.log" 2>&1

rg -o 'STR:[A-Za-z_]+=[^[:space:]]+' "$temporary/oracle.log" \
  >"$temporary/oracle.results"
rg -o 'STR:[A-Za-z_]+=[^[:space:]]+' "$temporary/candle.log" |
  rg -v '^STR:reject_grouping=' >"$temporary/candle.results"
diff -u "$temporary/oracle.results" "$temporary/candle.results"

rg -q 'STR:reject_grouping=true' "$temporary/candle.log"
rg -q 'CANDLE_STR_COMPAT_OK' "$temporary/candle.log"
if rg -q 'EXCEPTION:' "$temporary/candle.log"; then
  tail -n 80 "$temporary/candle.log" >&2
  exit 1
fi

printf 'PASS: pure Candle Str compatibility matches OCaml 4.14.1 oracle\n'
