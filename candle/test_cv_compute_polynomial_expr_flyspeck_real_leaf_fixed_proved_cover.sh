#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
output_dir=${1:-/project/flyspeck-candle-runs/cv-real-flyspeck-fixed-proved-cover-v1-run-001}
base_dir=/project/flyspeck-candle-runs/cv-fixed-scale-sound-checkpoint-v1

exec env \
  CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_dir/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" \
  CANDLE_CV_REAL_FLYSPECK_FIXED_PROVED_COVER_OK \
  "$repo_dir/candle/cv_compute_analytic_expr_fixed_scale_complete_sound.ml" \
  "$repo_dir/candle/cv_compute_analytic_expr_fixed_scale_invariant.ml" \
  "$repo_dir/candle/cv_compute_analytic_expr_fixed_scale_accept.ml" \
  "$repo_dir/candle/test_cv_compute_polynomial_expr_flyspeck_real_leaf_jet_batch.ml" \
  "$repo_dir/candle/test_cv_compute_polynomial_expr_flyspeck_real_leaf_fixed_proved_batch.ml" \
  "$repo_dir/candle/test_cv_compute_polynomial_expr_flyspeck_real_leaf_jet_certificate.ml" \
  "$repo_dir/candle/test_cv_compute_polynomial_expr_flyspeck_real_leaf_fixed_proved_cover.ml"
