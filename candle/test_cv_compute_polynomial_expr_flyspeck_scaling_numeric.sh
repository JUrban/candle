#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
output_dir=${1:-/project/flyspeck-candle-runs/cv-polynomial-expression-flyspeck-scaling-numeric-v1-run-001}
base_dir=/project/flyspeck-candle-runs/cv-flyspeck-universal-sound-checkpoint-v1

exec "$base_dir/restart-with-fragments.sh" \
  "$output_dir" \
  CANDLE_CV_POLYNOMIAL_EXPR_FLYSPECK_SCALING_NUMERIC_OK \
  "$repo_dir/candle/cv_compute_exact_interval_reify.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_reify.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_flyspeck_reify.ml" \
  "$repo_dir/candle/cv_compute_polynomial_expr_flyspeck_fixture.ml" \
  "$repo_dir/candle/test_cv_compute_polynomial_expr_flyspeck_scaling_numeric.ml"
