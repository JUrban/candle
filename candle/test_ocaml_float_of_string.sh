#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
ocaml=${OCAML_414:-/project/repos/hol-light/_opam/bin/ocaml}
fixture="$candle_root/candle/compatibility/fixtures/ocaml_float_of_string_oracle.ml"
test_dir=$(mktemp -d /tmp/candle-ocaml-float-of-string.XXXXXX)
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

rg -Fq 'let float_of_string = Float.of_string' "$candle_root/candle/ocaml.ml"

"$ocaml" -noinit -noprompt <"$fixture" >"$test_dir/ocaml.log" 2>&1
rg -Fq 'CANDLE_OCAML_FLOAT_OF_STRING_OK' "$test_dir/ocaml.log"

(
  cd "$candle_runtime_cwd"
  printf 'Cakeml.loadPath := ["%s"; Filename.currentDir];;\n#use "hol.ml";;\n#use "%s";;\n' \
    "$candle_root" "$fixture" |
    timeout 300 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1
rg -Fq 'val candle_float_of_string_ok = true: bool' "$test_dir/candle.log"
rg -Fq 'CANDLE_OCAML_FLOAT_OF_STRING_OK' "$test_dir/candle.log"
if rg -q 'EXCEPTION:|Parsing failed|ERROR:|Undefined variable:' \
     "$test_dir/candle.log"; then
  exit 1
fi

printf 'PASS: Candle float_of_string matches OCaml 4.14.1\n'
