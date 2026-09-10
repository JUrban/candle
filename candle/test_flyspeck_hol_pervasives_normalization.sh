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
original="$flyspeck_root/text_formalization/general/hol_pervasives.hl"
fixture="$candle_root/candle/compatibility/fixtures/hol_pervasives_compatibility_normalized.ml"
test_dir=$(mktemp -d /tmp/candle-flyspeck-hol-pervasives.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT
overlay="$test_dir/overlay"
cd "$candle_root"

python3 candle/flyspeck_normalize.py \
  --flyspeck-root "$flyspeck_root" --write "$overlay" \
  >"$test_dir/normalization.log"
normalized="$overlay/text_formalization/general/hol_pervasives.hl"

printf '#use "hol.ml";;\n#use "%s";;\n' "$original" |
  timeout 300 "$candle_binary" --candle \
    >"$test_dir/candle-original.log" 2>&1
printf '#use "hol.ml";;\n#use "%s";;\n#use "%s";;\n' \
    "$normalized" "$fixture" |
  timeout 300 "$candle_binary" --candle \
    >"$test_dir/candle-normalized.log" 2>&1

rg -Fq 'Undefined variable: loadt' "$test_dir/candle-original.log"
if rg -Fq 'val Hol_pervasives.needs' "$test_dir/candle-original.log"; then
  echo 'Candle unexpectedly accepted original Hol_pervasives.needs' >&2
  exit 1
fi
rg -Fq -- "- Finished loading $normalized" "$test_dir/candle-normalized.log"
rg -Fq 'val Hol_pervasives.needs = <fun>: string -> unit' \
  "$test_dir/candle-normalized.log"
rg -Fq 'val flyspeck_hol_pervasives_needs_fail_closed = true: bool' \
  "$test_dir/candle-normalized.log"
rg -Fq 'val flyspeck_hol_pervasives_string_order_ok = true: bool' \
  "$test_dir/candle-normalized.log"
rg -Fq 'val flyspeck_hol_pervasives_compatibility_oracle_ok = true: bool' \
  "$test_dir/candle-normalized.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/candle-normalized.log"; then
  tail -n 60 "$test_dir/candle-normalized.log" >&2
  exit 1
fi

printf 'PASS: exact Flyspeck Hol_pervasives compatibility normalization\n'
