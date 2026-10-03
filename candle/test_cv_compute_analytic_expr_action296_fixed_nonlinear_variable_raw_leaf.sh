#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 ]]; then
  printf 'usage: %s [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-action296-fixed-nonlinear-fixture-support-v1-16g-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-action296-fixed-nonlinear-variable-raw-leaf-v1-16g-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
marker=CANDLE_CV_ACTION296_FIXED_NONLINEAR_VARIABLE_RAW_LEAF_OK

fragments=(
  "$repo_root/candle/cv_compute_analytic_expr_stable_batch_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_representation_support.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove.ml"
  "$repo_root/candle/test_cv_compute_analytic_expr_action296_fixed_nonlinear_variable_raw_leaf.ml"
)

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "${fragments[@]}"
