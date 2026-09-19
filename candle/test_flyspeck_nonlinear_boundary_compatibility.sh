#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-nonlinear-boundary.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

ocaml -noinit -noprompt \
  <"$fixture_root/nonlinear_boundary_compatibility_ocaml_oracle.ml" \
  >"$test_dir/ocaml.log" 2>&1
rg -Fq 'NONLINEAR_BOUNDARY_COMPATIBILITY_OCAML_ORACLE_OK' \
  "$test_dir/ocaml.log"

run_candle() {
  local fixture=$1
  local output=$2
  (
    cd "$candle_runtime_cwd"
    timeout 60 "$candle_binary" --candle <"$fixture" >"$output" 2>&1
  )
}

run_candle "$fixture_root/nonlinear_nth_alias_original.ml" \
  "$test_dir/nth-original.log"
run_candle "$fixture_root/nonlinear_nth_alias_normalized.ml" \
  "$test_dir/nth-normalized.log"
run_candle "$fixture_root/nonlinear_string_order_original.ml" \
  "$test_dir/string-order-original.log"
run_candle "$fixture_root/nonlinear_string_order_normalized.ml" \
  "$test_dir/string-order-normalized.log"
run_candle "$fixture_root/nonlinear_structure_effect_original.ml" \
  "$test_dir/structure-effect-original.log"
run_candle "$fixture_root/nonlinear_structure_effect_normalized.ml" \
  "$test_dir/structure-effect-normalized.log"
run_candle "$fixture_root/nonlinear_ineqdoc_value_restriction_original.ml" \
  "$test_dir/ineqdoc-original.log"
run_candle "$fixture_root/nonlinear_ineqdoc_value_restriction_normalized.ml" \
  "$test_dir/ineqdoc-normalized.log"
run_candle "$fixture_root/nonlinear_dart_classes_value_restriction_original.ml" \
  "$test_dir/dart-classes-original.log"
run_candle "$fixture_root/nonlinear_dart_classes_value_restriction_normalized.ml" \
  "$test_dir/dart-classes-normalized.log"
run_candle "$fixture_root/nonlinear_autogen_value_restriction_original.ml" \
  "$test_dir/autogen-original.log"
run_candle "$fixture_root/nonlinear_autogen_value_restriction_normalized.ml" \
  "$test_dir/autogen-normalized.log"
run_candle "$fixture_root/nonlinear_optimize_preprocess_tuple_original.ml" \
  "$test_dir/optimize-preprocess-tuple-original.log"
run_candle "$fixture_root/nonlinear_optimize_preprocess_tuple_normalized.ml" \
  "$test_dir/optimize-preprocess-tuple-normalized.log"
run_candle "$fixture_root/nonlinear_merge_qualified_record_original.ml" \
  "$test_dir/merge-qualified-record-original.log"
run_candle "$fixture_root/nonlinear_merge_qualified_record_normalized.ml" \
  "$test_dir/merge-qualified-record-normalized.log"
run_candle "$fixture_root/parse_ineq_runtime_compatibility_normalized.ml" \
  "$test_dir/parse-ineq-runtime-normalized.log"
run_candle "$fixture_root/nonlinear_boundary_compatibility_normalized.ml" \
  "$test_dir/boundary-normalized.log"
(
  cd "$candle_runtime_cwd"
  timeout 300 "$candle_binary" --candle \
    <"$fixture_root/nonlinear_merge_ineq_setify_normalized.ml" \
    >"$test_dir/merge-ineq-setify-normalized.log" 2>&1
)

rg -Fq \
  'Type mismatch between string list -> string * string and (string * string * string * string) list' \
  "$test_dir/nth-original.log"
rg -Fq 'val candle_nonlinear_nth_alias_ok = true: bool' \
  "$test_dir/nth-normalized.log"
rg -Fq 'Type mismatch between int list -> int list and string list' \
  "$test_dir/string-order-original.log"
rg -Fq 'val candle_nonlinear_string_order_ok = true: bool' \
  "$test_dir/string-order-normalized.log"
rg -Fq 'val candle_nonlinear_structure_effect_original_ok = true: bool' \
  "$test_dir/structure-effect-original.log"
rg -Fq 'val candle_nonlinear_structure_effect_ok = true: bool' \
  "$test_dir/structure-effect-normalized.log"
rg -Fq 'Value restriction violated' "$test_dir/ineqdoc-original.log"
rg -Fq 'val candle_nonlinear_ineqdoc_value_ok = true: bool' \
  "$test_dir/ineqdoc-normalized.log"
rg -Fq 'Value restriction violated' "$test_dir/dart-classes-original.log"
rg -Fq 'val candle_nonlinear_dart_classes_value_ok = true: bool' \
  "$test_dir/dart-classes-normalized.log"
rg -Fq 'Value restriction violated' "$test_dir/autogen-original.log"
rg -Fq 'val candle_nonlinear_autogen_value_ok = true: bool' \
  "$test_dir/autogen-normalized.log"
rg -Fq \
  'Type mismatch between string -> string and string * int list * int' \
  "$test_dir/optimize-preprocess-tuple-original.log"
rg -Fq 'val candle_optimize_preprocess_tuple_ok = true: bool' \
  "$test_dir/optimize-preprocess-tuple-normalized.log"
rg -Fq \
  'Undefined variable: Candle_merge_qualified_source.TSKAJXY_DERIVED.ineq' \
  "$test_dir/merge-qualified-record-original.log"
rg -Fq 'val candle_merge_qualified_record_ok = true: bool' \
  "$test_dir/merge-qualified-record-normalized.log"
rg -Fq 'val candle_parse_ineq_runtime_compatibility_ok = true: bool' \
  "$test_dir/parse-ineq-runtime-normalized.log"
rg -Fq 'val candle_nonlinear_boundary_compatibility_ok = true: bool' \
  "$test_dir/boundary-normalized.log"
rg -Fq 'val candle_merge_ineq_setify_ok = true: bool' \
  "$test_dir/merge-ineq-setify-normalized.log"

for output in nth-normalized.log string-order-normalized.log \
              structure-effect-original.log structure-effect-normalized.log \
              ineqdoc-normalized.log \
              dart-classes-normalized.log autogen-normalized.log \
              optimize-preprocess-tuple-normalized.log \
              merge-qualified-record-normalized.log \
              parse-ineq-runtime-normalized.log \
              boundary-normalized.log merge-ineq-setify-normalized.log; do
  if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$test_dir/$output"; then
    tail -n 60 "$test_dir/$output" >&2
    exit 1
  fi
done

printf 'PASS: nonlinear boundary compatibility oracles\n'
