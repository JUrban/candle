#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
output_dir=${1:-/project/flyspeck-candle-runs/cv-polynomial-expression-flyspeck-dim-bridge-v1-run-001}
base_dir=/project/flyspeck-candle-runs/cv-flyspeck-taylor-bridge-checkpoint-v3

exec "$base_dir/restart-with-fragments.sh" \
  "$output_dir" \
  CANDLE_CV_POLYNOMIAL_EXPR_FLYSPECK_DIM_BRIDGE_OK \
  "$repo_dir/candle/cv_compute_polynomial_expr_flyspeck_dim_bridge.ml" \
  "$repo_dir/candle/test_cv_compute_polynomial_expr_flyspeck_dim_bridge.ml"
