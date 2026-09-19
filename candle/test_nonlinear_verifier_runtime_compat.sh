#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
candle_hol_root=${CANDLE_HOL_ROOT:-"$candle_root"}
ocaml=${OCAML_414:-/project/repos/hol-light/_opam/bin/ocaml}
fixture="$candle_root/candle/compatibility/fixtures/nonlinear_verifier_runtime_compat.ml"
test_dir=$(mktemp -d /tmp/candle-nonlinear-verifier-runtime.XXXXXX)
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

printf '#use "%s";;\n' "$fixture" |
  "$ocaml" -noinit -noprompt >"$test_dir/ocaml.log" 2>&1
rg -Fq 'CANDLE_NONLINEAR_VERIFIER_RUNTIME_COMPAT_OK' "$test_dir/ocaml.log"

(
  cd "$candle_runtime_cwd"
  printf '#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n' \
    "$candle_hol_root/candle/build/insulate.ml" \
    "$candle_root/candle/nums.ml" \
    "$candle_root/candle/pretty.ml" \
    "$candle_root/candle/ocaml.ml" \
    "$fixture" |
    timeout 600 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

rg -Fq 'val candle_nonlinear_verifier_runtime_compat_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'CANDLE_NONLINEAR_VERIFIER_RUNTIME_COMPAT_OK' "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed|Undefined variable:' \
  "$test_dir/candle.log"; then
  exit 1
fi

printf 'PASS: nonlinear verifier runtime compatibility matches OCaml 4.14.1\n'
