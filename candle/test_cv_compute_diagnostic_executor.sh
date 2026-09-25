#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-action296-taylor-certified-checkpoint-v1}
output_dir=${1:-/project/flyspeck-candle-runs/cv-diagnostic-executor-v1-run-001}

exec env CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_root/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" \
  CANDLE_CV_DIAGNOSTIC_EXECUTOR_OK \
  "$repo_root/candle/cv_compute_diagnostic_executor.ml" \
  "$repo_root/candle/test_cv_compute_diagnostic_executor.ml"
