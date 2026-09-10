#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
fixture_root="$candle_root/candle/compatibility/fixtures"
original="$fixture_root/parser_tuple_constructor_original.ml"
normalized="$fixture_root/parser_tuple_constructor_normalized.ml"
test_dir=$(mktemp -d /tmp/candle-flyspeck-parser-tuple.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT
cd "$candle_root"

ocaml -noinit -noprompt <"$original" >"$test_dir/ocaml-original.log" 2>&1
ocaml -noinit -noprompt <"$normalized" >"$test_dir/ocaml-normalized.log" 2>&1
timeout 60 "$candle_binary" --candle <"$original" \
  >"$test_dir/candle-original.log" 2>&1
timeout 60 "$candle_binary" --candle <"$normalized" \
  >"$test_dir/candle-normalized.log" 2>&1

rg -Fq \
  'Type mismatch between string -> string and string * flyspeck_parser_mini_pretype' \
  "$test_dir/candle-original.log"
rg -Fq 'val flyspeck_parser_tuple_constructor_oracle_ok : bool = true' \
  "$test_dir/ocaml-original.log"
rg -Fq 'val flyspeck_parser_tuple_constructor_oracle_ok : bool = true' \
  "$test_dir/ocaml-normalized.log"
rg -Fq 'val flyspeck_parser_tuple_constructor_oracle_ok = true: bool' \
  "$test_dir/candle-normalized.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/candle-normalized.log"; then
  tail -n 50 "$test_dir/candle-normalized.log" >&2
  exit 1
fi
if rg -Fq 'val flyspeck_parser_tuple_constructor_oracle_ok = true: bool' \
  "$test_dir/candle-original.log"; then
  echo 'Candle unexpectedly accepted original tuple-constructor oracle' >&2
  exit 1
fi

printf 'PASS: exact parser tuple-constructor normalization\n'
