#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-action296-taylor-certified-checkpoint-v1}
output_dir=${1:-/project/flyspeck-candle-runs/cv-action296-tree-verdict-point-plan-v1-run-001}

fragments=(
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_certified_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_point_certificate_prepare.ml"
  "$repo_root/candle/cv_compute_analytic_expr_box_certificate_prepare.ml"
  "$repo_root/candle/cv_compute_analytic_expr_certificate_variant_prepare.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_batch.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_batch_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_tree.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_tree_prove.ml"
  "$repo_root/candle/test_cv_compute_analytic_expr_action296_tree_verdict.ml"
)

exec env CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_root/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" CANDLE_CV_ACTION296_TREE_VERDICT_OK "${fragments[@]}"
