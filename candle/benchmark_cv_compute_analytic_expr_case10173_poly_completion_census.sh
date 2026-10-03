#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-case10173-complete-capture-checkpoint-v1-16g-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-case10173-poly-completion-census-v1-16g-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
fragment="$repo_root/candle/benchmark_cv_compute_analytic_expr_case10173_poly_completion_census.ml"
marker='CANDLE_CV_CASE10173_POLY_COMPLETION_CENSUS_OK'

CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "$fragment"

printf '%s\n' 'CANDLE_CV_CASE10173_POLY_COMPLETION_CENSUS_DRIVER_OK'
