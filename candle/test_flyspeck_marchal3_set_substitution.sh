#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture="$candle_root/candle/compatibility/fixtures/marchal3_set_substitution.ml"
test_dir=$(mktemp -d /tmp/candle-flyspeck-marchal3-set.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' "$fixture" |
    timeout 300 "$candle_binary" --candle >"$test_dir/candle.log" 2>&1
)

rg -Fq 'MARCHAL3_SET_SUBSTITUTION_OK' "$test_dir/candle.log"
for theorem in xy xz xt yz yt zt; do
  rg -Fq "val candle_marchal3_${theorem} = |-" "$test_dir/candle.log"
done
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/candle.log"; then
  tail -n 80 "$test_dir/candle.log" >&2
  exit 1
fi

printf 'PASS: Flyspeck Marchal3 deterministic set substitution\n'
