#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-reflected-support-checkpoint-v1}
output_dir=${1:-/project/flyspeck-candle-runs/cv-analytic-poly-inv-v1-run-001}

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_dir/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" CANDLE_CV_ANALYTIC_POLY_INV_OK \
  "$repo_dir/candle/cv_compute_exact_rational_inv.ml" \
  "$repo_dir/candle/cv_compute_exact_interval_inv_core.ml" \
  "$repo_dir/candle/cv_compute_analytic_dim_jet_inv.ml" \
  "$repo_dir/candle/cv_compute_analytic_poly_inv.ml" \
  "$repo_dir/candle/test_cv_compute_analytic_poly_inv.ml"

printf 'CANDLE_CV_ANALYTIC_POLY_INV_WRAPPER_OK output=%s\n' "$output_dir"
