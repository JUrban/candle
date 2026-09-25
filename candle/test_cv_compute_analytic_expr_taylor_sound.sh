#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-bridge-checkpoint-v1}
output_dir=${1:-"/project/flyspeck-candle-runs/cv-analytic-taylor-$(date -u +%Y%m%dT%H%M%SZ)"}

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_root/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" CANDLE_CV_ANALYTIC_TAYLOR_OK \
  "$repo_root/candle/cv_compute_analytic_expr_domain.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_flyspeck_bridge.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_sound.ml" \
  "$repo_root/candle/test_cv_compute_analytic_expr_taylor_sound.ml"

grep -q 'CANDLE_CV_ANALYTIC_TAYLOR_OK' "$output_dir/candle.log"
printf 'CANDLE_CV_ANALYTIC_TAYLOR_WRAPPER_OK output=%s\n' "$output_dir"
