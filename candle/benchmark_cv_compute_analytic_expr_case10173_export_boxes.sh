#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/v497-direct-case10173-compute-support-checkpoint-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-case10173-export-boxes-v2-16g-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
fragment="$repo_root/candle/benchmark_cv_compute_analytic_expr_case10173_export_boxes.ml"
marker='CANDLE_CV_CASE10173_BOX_EXPORT_OK'

CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "$fragment"

rg 'CANDLE_CV_NL_BOX[[:space:]]+10173[[:space:]]' \
  "$output_dir/candle.log" |
  sed $'s/^.*CANDLE_CV_NL_BOX\t10173\t//' >"$output_dir/case10173-boxes.tsv"

awk -F '\t' '
  function valid_vector(vector, values, count, i) {
    count = split(vector, values, ",")
    if (count != 6) return 0
    for (i = 1; i <= count; i++)
      if (values[i] !~ /^-?[0-9]+(\/[1-9][0-9]*)?$/) return 0
    return 1
  }
  BEGIN { expected = 0 }
  {
    if (NF != 3 || $1 != expected ||
        !valid_vector($2) || !valid_vector($3)) exit 1
    expected++
  }
  END { if (expected != 4173) exit 1 }
' "$output_dir/case10173-boxes.tsv"

sha256sum "$output_dir/case10173-boxes.tsv" \
  >"$output_dir/case10173-boxes.sha256"
printf '%s\n' \
  'CANDLE_CV_CASE10173_BOX_EXPORT_DRIVER_OK boxes=4173 dimensions=6 DEVELOPMENT_NON_RELEASE'
