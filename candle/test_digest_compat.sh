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
    printf 'Digest compatibility gate failed with status %d; Candle tail follows:\n' \
      "$status" >&2
    tail -n 120 "$temporary/candle.log" >&2 2>/dev/null || true
  fi
  rm -rf -- "$temporary"
  exit "$status"
}
trap cleanup EXIT

(
  cd "$candle_root"
  "$ocaml" -noinit "$candle_root/candle/digest_compat_oracle.ml"
) >"$temporary/oracle.log" 2>&1
(
  cd "$candle_root"
  timeout 1800 "$candle" <"$candle_root/candle/test_digest_compat.ml"
) >"$temporary/candle.log" 2>&1

rg -a -o 'DIGEST:[A-Za-z0-9_]+=[^[:space:]]+' "$temporary/oracle.log" \
  >"$temporary/oracle.results"
rg -a -o 'DIGEST:[A-Za-z0-9_]+=[^[:space:]]+' "$temporary/candle.log" \
  >"$temporary/candle.results"
diff -u "$temporary/oracle.results" "$temporary/candle.results"

rg -a -q 'CANDLE_DIGEST_COMPAT_OK' "$temporary/candle.log"
if rg -a -q 'EXCEPTION:|Parsing failed|ERROR:|Undefined variable:' \
  "$temporary/candle.log"; then
  tail -n 80 "$temporary/candle.log" >&2
  exit 1
fi

printf 'PASS: pure Candle Digest compatibility matches OCaml 4.14.1\n'
