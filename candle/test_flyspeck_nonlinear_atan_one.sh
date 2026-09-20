#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
candle_base_support=${CANDLE_BASE_SUPPORT:-"$candle_root"}
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-nonlinear-atan-one.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

ocaml -noinit -noprompt \
  <"$fixture_root/nonlinear_atan_one_ocaml_oracle.ml" \
  >"$test_dir/ocaml.log" 2>&1
rg -Fq 'NONLINEAR_ATAN_ONE_OCAML_ORACLE_OK' "$test_dir/ocaml.log"

printf 'Cakeml.loadPath := ["%s"; "%s"; Filename.currentDir];;\n#use "hol.ml";;\n#use "%s";;\n#use "%s";;\n' \
  "$candle_root" "$candle_base_support" \
  "$fixture_root/nonlinear_atan_one_original.ml" \
  "$fixture_root/nonlinear_atan_one_normalized.ml" |
  (
    cd "$candle_runtime_cwd"
    timeout 600 "$candle_binary" --candle
  ) >"$test_dir/candle.log" 2>&1
rg -Fq 'Undefined variable: atan' "$test_dir/candle.log"
rg -Fq 'NONLINEAR_ATAN_ONE_CANDLE_OK' "$test_dir/candle.log"
if rg -q 'EXCEPTION:|Parsing failed' "$test_dir/candle.log"; then
  tail -n 60 "$test_dir/candle.log" >&2
  exit 1
fi

printf 'PASS: nonlinear atan-one normalization oracle\n'
