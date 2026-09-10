#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
fixture_root="$candle_root/candle/compatibility/fixtures"
original="$fixture_root/jrh_lexer_toggle_original.ml"
normalized="$fixture_root/jrh_lexer_toggle_normalized.ml"
registration="$fixture_root/debug_quotation_registration_normalized.ml"
term_setify="$fixture_root/debug_term_setify_normalized.ml"
test_dir=$(mktemp -d /tmp/candle-flyspeck-debug-compatibility.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT
cd "$candle_root"

pa_j_name=$("$candle_root/pa_j/chooser.sh")
pa_j_source="$candle_root/pa_j/$pa_j_name"
if [[ ! -f "$pa_j_source" ]]; then
  echo "selected pa_j source does not exist: $pa_j_source" >&2
  exit 1
fi
cp "$pa_j_source" "$test_dir/pa_j.ml"
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
camlp5o pr_o.cmo "$normalized" >"$test_dir/native-normalized.ml"
cmp "$test_dir/native-original.ml" "$test_dir/native-normalized.ml"
rg -Fq 'let _ = false' "$test_dir/native-original.ml"
rg -Fq 'let _ = true' "$test_dir/native-original.ml"

printf '#use "hol.ml";;\n#use "%s";;\n' "$original" |
  timeout 300 "$candle_binary" --candle \
    >"$test_dir/candle-original.log" 2>&1
printf '#use "hol.ml";;\n#use "%s";;\n#use "%s";;\n' \
    "$normalized" "$term_setify" |
  timeout 300 "$candle_binary" --candle \
    >"$test_dir/candle-normalized.log" 2>&1
timeout 60 "$candle_binary" --candle <"$registration" \
  >"$test_dir/candle-registration.log" 2>&1

rg -Fq 'Undefined variable: unset_jrh_lexer' \
  "$test_dir/candle-original.log"
rg -Fq 'FLYSPECK_JRH_TOGGLE_ORACLE_OK' \
  "$test_dir/candle-normalized.log"
rg -Fq 'val flyspeck_jrh_toggle_oracle = true: bool' \
  "$test_dir/candle-normalized.log"
rg -Fq 'val flyspeck_debug_setify_duplicate_ok = true: bool' \
  "$test_dir/candle-normalized.log"
rg -Fq 'val flyspeck_debug_setify_distinct_ok = true: bool' \
  "$test_dir/candle-normalized.log"
rg -Fq 'val flyspeck_debug_setify_oracle_ok = true: bool' \
  "$test_dir/candle-normalized.log"
rg -Fq 'val flyspeck_debug_verbose_registration_ok = true: bool' \
  "$test_dir/candle-registration.log"
rg -Fq 'val flyspeck_debug_restore_registration_ok = true: bool' \
  "$test_dir/candle-registration.log"
rg -Fq 'val flyspeck_debug_registration_oracle_ok = true: bool' \
  "$test_dir/candle-registration.log"
for log in "$test_dir/candle-normalized.log" "$test_dir/candle-registration.log"
do
  if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$log"; then
    tail -n 50 "$log" >&2
    exit 1
  fi
done
if rg -Fq 'FLYSPECK_JRH_TOGGLE_ORACLE_OK' "$test_dir/candle-original.log"; then
  echo 'Candle unexpectedly accepted original JRH lexer toggle fixture' >&2
  exit 1
fi

printf 'PASS: exact Flyspeck Debug compatibility normalization\n'
