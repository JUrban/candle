#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle=${1:-"$candle_root/candle.sh"}
candle_workdir=${CANDLE_WORKDIR:-$(cd -- "$(dirname -- "$candle")" && pwd)}
fixtures=$candle_root/candle/compatibility/fixtures
test_dir=$(mktemp -d /tmp/candle-good-list-printer.XXXXXX)
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
  <"$fixtures/good_list_printer_value_restriction_raw.ml" \
  >"$test_dir/ocaml-raw.log" 2>&1
ocaml -noinit -noprompt \
  <"$fixtures/good_list_printer_value_restriction_normalized.ml" \
  >"$test_dir/ocaml-normalized.log" 2>&1
expected='[5; 0; 4; 3; 0; 2; 0; 1]'
rg -Fq "candle_good_list_observation : int list = $expected" \
  "$test_dir/ocaml-raw.log"
rg -Fq "candle_good_list_observation : int list = $expected" \
  "$test_dir/ocaml-normalized.log"

ocaml -noinit -noprompt \
  <"$fixtures/incr_counter_original.ml" \
  >"$test_dir/ocaml-incr-original.log" 2>&1
ocaml -noinit -noprompt \
  <"$fixtures/incr_counter_normalized.ml" \
  >"$test_dir/ocaml-incr-normalized.log" 2>&1
rg -Fq 'candle_incr_observation : int = 1' \
  "$test_dir/ocaml-incr-original.log"
rg -Fq 'candle_incr_observation : int = 1' \
  "$test_dir/ocaml-incr-normalized.log"

(
  cd "$candle_workdir"
  timeout 300 "$candle" --candle \
    <"$fixtures/good_list_printer_value_restriction_raw.ml"
) >"$test_dir/candle-raw.log" 2>&1
rg -Fq 'Value restriction violated' "$test_dir/candle-raw.log"

(
  cd "$candle_workdir"
  timeout 300 "$candle" --candle \
    <"$fixtures/good_list_printer_value_restriction_normalized.ml"
) >"$test_dir/candle-normalized.log" 2>&1
rg -Fq "val candle_good_list_observation = $expected: int list" \
  "$test_dir/candle-normalized.log"
if rg -q 'EXCEPTION:|Parsing failed|ERROR:|Undefined variable:' \
     "$test_dir/candle-normalized.log"; then
  exit 1
fi

(
  cd "$candle_workdir"
  timeout 300 "$candle" --candle \
    <"$fixtures/incr_counter_original.ml"
) >"$test_dir/candle-incr-original.log" 2>&1
rg -Fq 'Undefined variable: incr' "$test_dir/candle-incr-original.log"

(
  cd "$candle_workdir"
  timeout 300 "$candle" --candle \
    <"$fixtures/incr_counter_normalized.ml"
) >"$test_dir/candle-incr-normalized.log" 2>&1
rg -Fq 'val candle_incr_observation = 1: int' \
  "$test_dir/candle-incr-normalized.log"
if rg -q 'EXCEPTION:|Parsing failed|ERROR:|Undefined variable:' \
     "$test_dir/candle-incr-normalized.log"; then
  exit 1
fi

printf 'PASS: action-170 good-list printer and counter normalizations\n'
