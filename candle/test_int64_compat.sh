#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
ocaml=${OCAML_414:-/project/repos/hol-light/_opam/bin/ocaml}
fixture="$candle_root/candle/compatibility/fixtures/int64_compat.ml"
test_dir=$(mktemp -d /tmp/candle-int64-compat.XXXXXX)
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

rg -Fq 'module Int64 = struct' "$candle_root/candle/ocaml.ml"
rg -Fq 'Cake.Word64.toIntSigned' "$candle_root/candle/ocaml.ml"

"$ocaml" -noinit -noprompt <"$fixture" >"$test_dir/ocaml.log" 2>&1
rg -Fq 'CANDLE_INT64_COMPAT_OK' "$test_dir/ocaml.log"

(
  cd "$candle_runtime_cwd"
  printf 'Cakeml.loadPath := ["%s"; Filename.currentDir];;\n#use "hol.ml";;\n#use "%s";;\n' \
    "$candle_root" "$fixture" |
    timeout 300 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

rg -Fq 'val candle_int64_compat_ok = true: bool' "$test_dir/candle.log"
rg -Fq 'CANDLE_INT64_COMPAT_OK' "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed|Undefined variable:' \
  "$test_dir/candle.log"; then
  exit 1
fi

printf 'PASS: Int64 compatibility matches OCaml 4.14.1\n'
