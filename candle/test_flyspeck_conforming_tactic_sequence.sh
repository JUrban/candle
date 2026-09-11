#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture_root="$candle_root/candle/compatibility/fixtures"
original="$fixture_root/conforming_tactic_sequence_original.ml"
normalized="$fixture_root/conforming_tactic_sequence_normalized.ml"
test_dir=$(mktemp -d /tmp/candle-flyspeck-conforming-sequence.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

pa_j_name=$("$candle_runtime_cwd/pa_j/chooser.sh")
cp "$candle_runtime_cwd/pa_j/$pa_j_name" "$test_dir/pa_j.ml"
(
  cd "$test_dir"
  ocamlc -safe-string -c \
    -pp 'camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo' \
    -I "$(camlp5 -where)" \
    -I "$(ocamlfind query camlp-streams)" \
    pa_j.ml
)
camlp5o -I "$test_dir" "$test_dir/pa_j.cmo" pr_o.cmo "$original" \
  >"$test_dir/native-original.ml"
camlp5o -I "$test_dir" "$test_dir/pa_j.cmo" pr_o.cmo "$normalized" \
  >"$test_dir/native-normalized.ml"
cmp "$test_dir/native-original.ml" "$test_dir/native-normalized.ml"

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' "$original" |
  timeout 300 "$candle_binary" --candle \
    >"$test_dir/original.log" 2>&1
)
(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' "$normalized" |
  timeout 300 "$candle_binary" --candle \
    >"$test_dir/normalized.log" 2>&1
)

rg -Fq 'Type mismatch between' "$test_dir/original.log"
rg -Fq 'val candle_conforming_tactic_sequence = <fun>:' \
  "$test_dir/normalized.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/normalized.log"; then
  tail -n 50 "$test_dir/normalized.log" >&2
  exit 1
fi

printf 'PASS: Flyspeck Conforming tactic-sequence normalization\n'
