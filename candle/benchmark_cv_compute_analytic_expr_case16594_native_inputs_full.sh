#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-case16594-complete-full-precomputed-capture-checkpoint-v2-16g-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-case16594-native-inputs-full-v1-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
fragment="$repo_root/candle/benchmark_cv_compute_analytic_expr_case16594_native_inputs_full.ml"
marker='CANDLE_CV_CASE16594_NATIVE_INPUTS_FULL_OK'
historical_root=${CANDLE_HISTORICAL_RUNNER_ROOT:-/project/worktrees/candle-historical-runner-c1dd}

[[ -d "$historical_root" ]]

CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  CANDLE_FRAGMENT_INPUT_RELOCATION_FROM=/project/worktrees/candle-cv-compute-equation-slicing-v1 \
  CANDLE_FRAGMENT_INPUT_RELOCATION_TO="$historical_root" \
  "$runner" "$output_dir" "$marker" "$fragment"

rg 'CANDLE_CV_NL_NATIVE_PROGRAM[[:space:]]+16594[[:space:]]' \
  "$output_dir/candle.log" |
  sed $'s/^.*CANDLE_CV_NL_NATIVE_PROGRAM\t16594\t//' \
  >"$output_dir/case16594-program.cval"

rg 'CANDLE_CV_NL_NATIVE_JOB[[:space:]]+16594[[:space:]]' \
  "$output_dir/candle.log" |
  sed $'s/^.*CANDLE_CV_NL_NATIVE_JOB\t16594\t//' \
  >"$output_dir/case16594-native-jobs-full.tsv"

[[ $(wc -l <"$output_dir/case16594-program.cval") -eq 1 ]]
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
        !valid_intervals($2, 10) || !valid_intervals($3, 10) ||
        !valid_vector($4, 6) || !valid_vector($5, 6)) exit 1
    expected_index++
  }
  END { if (expected_index != 875) exit 1 }
' "$output_dir/case16594-native-jobs-full.tsv"

sha256sum "$output_dir/case16594-program.cval" \
  "$output_dir/case16594-native-jobs-full.tsv" \
  >"$output_dir/native-inputs.sha256"
sha256sum -c "$output_dir/result-files.sha256"
printf '%s\n' \
  'CANDLE_CV_CASE16594_NATIVE_INPUTS_FULL_DRIVER_OK DEVELOPMENT_NON_RELEASE'
