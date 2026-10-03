#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-case10173-complete-proof-support-v1-16g-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-fixed-outer-lazy-complete-v1-16g-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
marker='CANDLE_CV_FIXED_OUTER_LAZY_COMPLETE_OK DEVELOPMENT_NON_RELEASE'

CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" \
  "$repo_root/candle/cv_compute_analytic_expr_fixed_scale_lazy_completion_compute.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_fixed_scale_lazy_completion_sound.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_lazy.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_lazy_sound.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_lazy_variable_raw.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_lazy_complete.ml"

printf '%s\n' 'CANDLE_CV_FIXED_OUTER_LAZY_COMPLETE_DRIVER_OK'
