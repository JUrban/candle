#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_MATAN_TIGHT_CHECKER_BASE_DIR:-/project/flyspeck-candle-runs/nl-matan-genuine-root-tight-checker-checkpoint-v1-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/nl-matan-genuine-root-fixed-handoff-v1-dev-017}

cd "$repo_root"
env \
  CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  candle/restart_real_functions_with_fragments.sh \
    "$output_dir" \
    CANDLE_CV_MATAN_GENUINE_ROOT_FIXED_HANDOFF_OK \
    candle/cv_compute_analytic_expr_fixed_scale_taylor_handoff_compute.ml \
    candle/test_cv_compute_analytic_expr_matan_genuine_root_fixed_handoff.ml
