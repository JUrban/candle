#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle=${1:-"$candle_root/candle.sh"}
candle_workdir=${CANDLE_WORKDIR:-$(cd -- "$(dirname -- "$candle")" && pwd)}
fixtures=$candle_root/candle/compatibility/fixtures
test_dir=$(mktemp -d /tmp/candle-lp-hashtbl.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    for log in "$test_dir"/*.log; do
      [[ -f $log ]] || continue
      printf '%s\n' "--- ${log##*/}" >&2
      tail -n 80 "$log" >&2 || true
    done
  fi
  chmod -R u+w "$test_dir" 2>/dev/null || true
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

ocaml -noinit -noprompt \
  <"$fixtures/lp_hashtbl_value_restriction_ocaml_oracle.ml" \
  >"$test_dir/ocaml.log" 2>&1
rg -Fq 'LP_HASHTBL_ANNOTATION_OCAML_ORACLE_OK' "$test_dir/ocaml.log"

(
  cd "$candle_workdir"
  timeout 300 "$candle" --candle \
    <"$fixtures/lp_hashtbl_value_restriction_raw.ml"
) >"$test_dir/candle-raw.log" 2>&1
rg -Fq 'Value restriction violated' "$test_dir/candle-raw.log"

(
  cd "$candle_workdir"
  timeout 300 "$candle" --candle \
    <"$fixtures/lp_hashtbl_value_restriction_normalized.ml"
) >"$test_dir/candle-normalized.log" 2>&1
rg -Fq \
  'val candle_lp_annotated_observation = [("beta", 17); ("alpha", 11)]' \
  "$test_dir/candle-normalized.log"
if rg -q 'EXCEPTION:|Parsing failed|ERROR:|Undefined variable:' \
     "$test_dir/candle-normalized.log"; then
  exit 1
fi

printf 'PASS: LP top-level hash-table value-restriction preflight\n'
