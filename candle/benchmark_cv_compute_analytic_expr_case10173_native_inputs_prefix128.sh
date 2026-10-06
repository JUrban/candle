#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/v497-direct-case10173-compute-support-checkpoint-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-case10173-native-inputs-prefix128-v1-16g-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
fragment="$repo_root/candle/benchmark_cv_compute_analytic_expr_case10173_native_inputs_prefix128.ml"
marker='CANDLE_CV_CASE10173_NATIVE_INPUTS_PREFIX128_OK'

CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "$fragment"

rg 'CANDLE_CV_NL_NATIVE_PROGRAM[[:space:]]+10173[[:space:]]' \
  "$output_dir/candle.log" |
  sed $'s/^.*CANDLE_CV_NL_NATIVE_PROGRAM\t10173\t//' \
  >"$output_dir/case10173-program.cval"

rg 'CANDLE_CV_NL_NATIVE_JOB[[:space:]]+10173[[:space:]]' \
  "$output_dir/candle.log" |
  sed $'s/^.*CANDLE_CV_NL_NATIVE_JOB\t10173\t//' \
  >"$output_dir/case10173-native-jobs-prefix128.tsv"

[[ $(wc -l <"$output_dir/case10173-program.cval") -eq 1 ]]
awk -F '\t' '
  function valid_q(q) {
    return q ~ /^-?[0-9]+(\/[1-9][0-9]*)?$/
  }
  function valid_vector(vector, expected, values, count, i) {
    count = split(vector, values, ",")
    if (count != expected) return 0
    for (i = 1; i <= count; i++) if (!valid_q(values[i])) return 0
    return 1
  }
  function valid_intervals(vector, expected, values, endpoints, count, i) {
    count = split(vector, values, ",")
    if (count != expected) return 0
    for (i = 1; i <= count; i++) {
      if (split(values[i], endpoints, ":") != 2 ||
          !valid_q(endpoints[1]) || !valid_q(endpoints[2])) return 0
    }
    return 1
  }
  BEGIN { expected_index = 0 }
  {
    if (NF != 5 || $1 != expected_index ||
        !valid_intervals($2, 7) || !valid_intervals($3, 7) ||
        !valid_vector($4, 6) || !valid_vector($5, 6)) exit 1
    expected_index++
  }
  END { if (expected_index != 128) exit 1 }
' "$output_dir/case10173-native-jobs-prefix128.tsv"

sha256sum "$output_dir/case10173-program.cval" \
  "$output_dir/case10173-native-jobs-prefix128.tsv" \
  >"$output_dir/native-inputs.sha256"
sha256sum -c "$output_dir/result-files.sha256"
printf '%s\n' \
  'CANDLE_CV_CASE10173_NATIVE_INPUTS_PREFIX128_DRIVER_OK DEVELOPMENT_NON_RELEASE'
