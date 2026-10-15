#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_MATAN_DUAL_CHECK_BASE_DIR:-/project/flyspeck-candle-runs/nl-matan-genuine-root-dual-check-checkpoint-v1-dev-002}
output_dir=${1:-/project/flyspeck-candle-runs/nl-matan-genuine-root-dual-check-original-prove-v1-dev-001}

cd "$repo_root"
env \
  CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  candle/restart_real_functions_with_fragments.sh \
    "$output_dir" \
    CANDLE_CV_MATAN_GENUINE_ROOT_DUAL_CHECK_ORIGINAL_OK \
    candle/test_cv_compute_analytic_expr_matan_genuine_root_dual_check_original_prove.ml
