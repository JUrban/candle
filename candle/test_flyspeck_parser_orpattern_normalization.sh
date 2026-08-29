#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle.sh"}
fixture_root="$candle_root/candle/compatibility/fixtures"
original="$fixture_root/parser_let_orpattern_original.ml"
normalized="$fixture_root/parser_let_orpattern_normalized.ml"
test_dir=$(mktemp -d /tmp/candle-flyspeck-parser-orpattern.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

printf 'let print = print_string;;\n#use "%s";;\n' "$original" |
  ocaml -noinit -noprompt >"$test_dir/ocaml-original.log" 2>&1
printf 'let print = print_string;;\n#use "%s";;\n' "$normalized" |
  ocaml -noinit -noprompt >"$test_dir/ocaml-normalized.log" 2>&1
(
  cd "$candle_root"
  timeout 60 "$candle_binary" <"$normalized" \
    >"$test_dir/candle-normalized.log" 2>&1
)

for log in \
  "$test_dir/ocaml-original.log" \
  "$test_dir/ocaml-normalized.log" \
  "$test_dir/candle-normalized.log"
do
  rg -Fq 'FLYSPECK_PARSER_ORPATTERN_ORACLE_OK' "$log"
done
if rg -q 'EXCEPTION:|Parsing failed' "$test_dir/candle-normalized.log"; then
  tail -n 50 "$test_dir/candle-normalized.log" >&2
  exit 1
fi

printf 'PASS: exact parser let-or-pattern normalization\n'
