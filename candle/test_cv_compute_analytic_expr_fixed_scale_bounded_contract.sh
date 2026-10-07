#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-action296-taylor-certified-checkpoint-v1}
output_dir=${1:-/project/flyspeck-candle-runs/cv-fixed-scale-bounded-contract-v1-run-001}
runner="$repo_root/candle/restart_real_functions_with_fragments_strict.sh"
marker=CANDLE_CV_FS_BOUNDED_CONTRACT_TEST_OK

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" \
  "$repo_root/candle/cv_compute_analytic_expr_fixed_scale_compute.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_fixed_scale_bounded_contract.ml" \
  "$repo_root/candle/test_cv_compute_analytic_expr_fixed_scale_bounded_contract.ml"
