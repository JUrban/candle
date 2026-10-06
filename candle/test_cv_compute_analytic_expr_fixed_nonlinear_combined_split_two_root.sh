#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 ]]; then
  printf 'usage: %s [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/v570-fifteen-sibling-lineage-fourth-batch-forest-plan-checkpoint-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/v598-fixed-nonlinear-combined-split-two-root-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
marker=CANDLE_CV_FIXED_NONLINEAR_COMBINED_SPLIT_TWO_ROOT_OK

fragments=(
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_combine_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_stack_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_combined_split_prove.ml"
  "$repo_root/candle/test_cv_compute_analytic_expr_fixed_nonlinear_combined_split_two_root.ml"
)

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "${fragments[@]}"
