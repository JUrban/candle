#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
output_dir=${1:-/project/flyspeck-candle-runs/cv-polynomial-expression-dim-jet-semantics-v1-run-001}
base_dir=/project/flyspeck-candle-runs/cv-flyspeck-universal-sound-checkpoint-v1

exec "$base_dir/restart-with-fragments.sh" \
  "$output_dir" \
  CANDLE_CV_DIM_JET_SEMANTICS_OK \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet.ml" \
  "$repo_dir/candle/cv_compute_linear_combination.ml" \
  "$repo_dir/candle/cv_compute_linear_combination_normalize.ml" \
  "$repo_dir/candle/cv_compute_exact_rational_normalize.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_compute.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_representation.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_semantics.ml" \
  "$repo_dir/candle/test_cv_compute_polynomial_expr_dim_jet_semantics.ml"
