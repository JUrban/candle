#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
flyspeck_root=${FLYSPECK_ROOT:-${1:-}}
if [[ -z "$flyspeck_root" || ! -d "$flyspeck_root" ]]; then
  echo "usage: FLYSPECK_ROOT=/exact/source/root $0" >&2
  exit 1
fi
flyspeck_root=$(realpath -- "$flyspeck_root")
fixture="$candle_root/candle/compatibility/fixtures/print_types_atom_order_normalized.ml"
test_dir=$(mktemp -d /tmp/candle-flyspeck-print-types.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT
overlay="$test_dir/overlay"
cd "$candle_root"

python3 candle/flyspeck_normalize.py \
  --flyspeck-root "$flyspeck_root" --write "$overlay" \
  >"$test_dir/normalization.log"
print_types="$overlay/text_formalization/general/print_types.hl"
printf '#use "hol.ml";;\n#use "%s";;\n#use "%s";;\n' \
    "$print_types" "$fixture" |
  timeout 300 "$candle_binary" --candle \
    >"$test_dir/candle.log" 2>&1

rg -Fq -- "- Finished loading $print_types" "$test_dir/candle.log"
rg -Fq 'val Print_types.print_term_types' "$test_dir/candle.log"
rg -Fq 'val flyspeck_print_types_duplicate_distinct_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'val flyspeck_print_types_order_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'val flyspeck_print_types_numeric_comparison_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'val flyspeck_print_types_concat_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'val flyspeck_print_types_atom_order_oracle_ok = true: bool' \
  "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/candle.log"; then
  tail -n 50 "$test_dir/candle.log" >&2
  exit 1
fi

printf 'PASS: exact Flyspeck Print_types normalization\n'
