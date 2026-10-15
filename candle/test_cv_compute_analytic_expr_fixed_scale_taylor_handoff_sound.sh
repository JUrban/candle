#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_MATAN_TIGHT_CHECKER_BASE_DIR:-/project/flyspeck-candle-runs/nl-matan-genuine-root-tight-checker-checkpoint-v1-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/nl-matan-fixed-handoff-scalar-sound-v1-dev-001}

cd "$repo_root"
env \
  CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  candle/restart_real_functions_with_fragments.sh \
    "$output_dir" \
    CANDLE_CV_MATAN_FS_HANDOFF_SCALAR_SOUND_OK \
    candle/cv_compute_analytic_expr_fixed_scale_taylor_handoff_compute.ml \
    candle/cv_compute_analytic_expr_fixed_scale_taylor_handoff_sound.ml \
    candle/test_cv_compute_analytic_expr_fixed_scale_taylor_handoff_sound.ml
