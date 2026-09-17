#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
ocaml=${OCAML_414:-/project/repos/hol-light/_opam/bin/ocaml}
fixtures="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-lpproc-float-compare.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    for log in "$test_dir"/*.log; do
      [[ -f $log ]] || continue
      printf '%s\n' "--- ${log##*/}" >&2
      tail -n 100 "$log" >&2 || true
    done
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

rg -Fq 'module Float = struct' "$candle_root/candle/ocaml.ml"
rg -Fq 'let compare = Float.compare' "$candle_root/candle/ocaml.ml"

"$ocaml" -noinit -noprompt \
  <"$fixtures/lpproc_float_compare_ocaml_oracle.ml" \
  >"$test_dir/ocaml.log" 2>&1
rg -Fq 'LPPROC_FLOAT_COMPARE_OCAML_ORACLE_OK' "$test_dir/ocaml.log"

(
  cd "$candle_runtime_cwd"
  printf 'Cakeml.loadPath := ["%s"; Filename.currentDir];;\n#use "hol.ml";;\n#use "%s";;\n#use "%s";;\n' \
    "$candle_root" \
    "$fixtures/lpproc_float_compare_raw.ml" \
    "$fixtures/lpproc_float_compare_normalized.ml" |
    timeout 300 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

rg -Fq 'Type mismatch between int -> bool and Double.double ->' \
  "$test_dir/candle.log"
test "$(rg -c '^ERROR:' "$test_dir/candle.log")" -eq 1
rg -Fq 'val candle_lpproc_float_compare_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'CANDLE_LPPROC_FLOAT_COMPARE_OK' "$test_dir/candle.log"
if rg -q 'EXCEPTION:|Parsing failed|Undefined variable:' "$test_dir/candle.log"; then
  exit 1
fi

printf 'PASS: Lpproc float comparison matches OCaml 4.14.1\n'
