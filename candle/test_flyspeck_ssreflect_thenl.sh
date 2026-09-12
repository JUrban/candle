#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-ssreflect-thenl.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

# The compatibility replacement is the local analogue of the linked
# instantiation propagation in the current HOL Light tactic engine.
rg -Fq 'let compose_justs n just1 just2 insts2 i ths =' \
  "$candle_root/tactics.ml"
rg -Fq 'let combined_goals = (map (inst_goal insts2) gls1)@gls2 in' \
  "$candle_root/tactics.ml"
rg -Fq 'compose_justs (length gls1) just1 just2 insts2' \
  "$candle_root/tactics.ml"

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' \
    "$fixture_root/ssreflect_thenl_original.ml" |
    timeout 300 "$candle_binary" --candle >"$test_dir/original.log" 2>&1
)
(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' \
    "$fixture_root/ssreflect_thenl_normalized.ml" |
    timeout 300 "$candle_binary" --candle >"$test_dir/normalized.log" 2>&1
)

rg -Fq 'Type mismatch between ((string * thm) list * term) list ->' \
  "$test_dir/original.log"
rg -Fq 'val candle_ssreflect_thenl_ok = true: bool' \
  "$test_dir/normalized.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/normalized.log"; then
  tail -n 50 "$test_dir/normalized.log" >&2
  exit 1
fi

printf 'PASS: Flyspeck ssreflect current-instantiation tactic normalization\n'
