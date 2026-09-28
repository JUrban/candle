#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-action296-box-plan-support-checkpoint-v1}
output_dir=${1:-/project/flyspeck-candle-runs/cv-fixed-outer-invariant-v1-run-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
marker=CANDLE_CV_FIXED_OUTER_INVARIANT_OK

fragments=(
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_invariant.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_item_invariant.ml"
  "$repo_root/candle/test_cv_compute_analytic_expr_taylor_model_program_fixed_outer_invariant.ml"
)

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "${fragments[@]}"

sha256sum -c "$output_dir/result-files.sha256"
printf '%s\n' 'CANDLE_CV_FIXED_OUTER_INVARIANT_DRIVER_OK'
