#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_MATAN_TIGHT_CHECKER_BASE_DIR:-/project/flyspeck-candle-runs/nl-matan-genuine-root-tight-checker-checkpoint-v1-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/nl-matan-genuine-root-dual-check-checkpoint-v1-dev-001}

cd "$repo_root"
candle/build_cv_fragment_checkpoint.sh \
  "$base_dir" "$output_dir" \
  CANDLE_CV_MATAN_GENUINE_ROOT_DUAL_CHECK_CHECKPOINT_READY \
  candle/cv_compute_analytic_expr_fixed_scale_taylor_handoff_compute.ml \
  candle/cv_compute_analytic_expr_certificate_erasure.ml \
  candle/cv_compute_analytic_expr_fixed_scale_taylor_handoff_sound.ml \
  candle/test_cv_compute_analytic_expr_matan_genuine_root_center_prepare.ml \
  candle/test_cv_compute_analytic_expr_matan_genuine_root_dual_check_prepare.ml
