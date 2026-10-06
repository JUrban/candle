#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 ]]; then
  printf 'usage: %s [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/v580a-fifteen-sibling-lineage-fourth-batch-chunked-function1-groups-through080-checkpoint-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/v600-fourth-group83-bounded-component-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
marker=CANDLE_CV_FOURTH_GROUP83_BOUNDED_COMPONENT_OK

fragments=(
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_combine_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_stack_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_combined_split_prove.ml"
  "$repo_root/candle/cv_compute_flyspeck_nonlinear_term_order_compat.ml"
  "$repo_root/candle/cv_compute_analytic_expr_disjunctive_component_bounded_prove.ml"
  "$repo_root/candle/test_cv_compute_analytic_expr_disjunctive_fourth_group83_bounded_component.ml"
)

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "${fragments[@]}"
