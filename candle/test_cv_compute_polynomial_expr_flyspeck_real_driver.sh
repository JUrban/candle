#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
output_dir=${1:-/project/flyspeck-candle-runs/cv-polynomial-expression-flyspeck-real-driver-v1-run-001}

exec "$repo_dir/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" \
  CANDLE_CV_REAL_FLYSPECK_DRIVER_OK \
  "$repo_dir/candle/compute.ml" \
  "$repo_dir/candle/cv_compute_linear_combination_core.ml" \
  "$repo_dir/candle/cv_compute_linear_combination_sound.ml" \
  "$repo_dir/candle/cv_compute_linear_combination_realize.ml" \
  "$repo_dir/candle/cv_compute_exact_rational_core.ml" \
  "$repo_dir/candle/cv_compute_exact_interval_core.ml" \
  "$repo_dir/candle/cv_compute_exact_rational_order_core.ml" \
  "$repo_dir/candle/cv_compute_exact_interval_mul_core.ml" \
  "$repo_dir/candle/cv_compute_exact_interval_square_core.ml" \
  "$repo_dir/candle/cv_compute_exact_interval_program.ml" \
  "$repo_dir/candle/cv_compute_exact_interval_reify.ml" \
  "$repo_dir/candle/cv_compute_whole_box_taylor.ml" \
  "$repo_dir/candle/cv_compute_whole_box_jet.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_jet.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_derivatives.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet.ml" \
  "$repo_dir/candle/cv_compute_linear_combination.ml" \
  "$repo_dir/candle/cv_compute_linear_combination_normalize.ml" \
  "$repo_dir/candle/cv_compute_exact_rational_normalize.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_reify.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_calculus.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_calculus.ml" \
  "$repo_dir/candle/cv_compute_whole_box_dim_taylor.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_diff.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_flyspeck_dim_bridge.ml" \
  "$repo_dir/candle/cv_compute_whole_box_dim_taylor_sound.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_check.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_flyspeck_dim_sound.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_flyspeck_reify.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_flyspeck_fixture.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_compute.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_representation.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_first_jet_compute.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_first_jet_representation.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_semantics.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_check.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_sound.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_prove.ml" \
  "$repo_dir/candle/cv_compute_flyspeck_nonlinear_driver.ml" \
  "$repo_dir/candle/test_cv_compute_polynomial_expr_flyspeck_real_driver.ml"
