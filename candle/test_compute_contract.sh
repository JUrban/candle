#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
candle_support_root=${CANDLE_SUPPORT_ROOT:-"$candle_root"}
test_dir=$(mktemp -d /tmp/candle-compute-contract.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    printf '%s\n' '--- Candle compute contract log' >&2
    tail -n 160 "$test_dir/candle.log" >&2 2>/dev/null || true
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

(
  cd "$candle_runtime_cwd"
  printf 'Cakeml.loadPath := ["%s"; "%s"; Filename.currentDir];;\n#use "hol.ml";;\n#use "%s/candle/test_compute_contract.ml";;\n' \
    "$candle_root" "$candle_support_root" "$candle_root" |
    timeout 1800 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

for marker in \
  init_theorem_count \
  arithmetic \
  div_mod_pair \
  numeric_if \
  pair_if_uses_else_branch \
  nested_pair_equality \
  user_equation_theorem_handoff \
  swapped_contract_rejected \
  short_contract_rejected; do
  rg -Fq "CANDLE_COMPUTE_OK:$marker" "$test_dir/candle.log"
done
rg -Fq 'CANDLE_COMPUTE_CONTRACT_OK' "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed|Undefined variable:' \
  "$test_dir/candle.log"; then
  exit 1
fi

printf 'PASS: Candle compute wrapper matches the complete kernel contract\n'
