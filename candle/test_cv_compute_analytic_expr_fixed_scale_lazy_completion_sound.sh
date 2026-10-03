#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-case10173-complete-capture-checkpoint-v1-16g-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-fixed-scale-lazy-completion-sound-v1-16g-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
marker='CANDLE_CV_FIXED_SCALE_LAZY_COMPLETION_SOUND_OK DEVELOPMENT_NON_RELEASE'

CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" \
  "$repo_root/candle/cv_compute_analytic_expr_fixed_scale_lazy_completion_compute.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_fixed_scale_lazy_completion_sound.ml"

printf '%s\n' 'CANDLE_CV_FIXED_SCALE_LAZY_COMPLETION_SOUND_DRIVER_OK'
