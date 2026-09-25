#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-checker-checkpoint-v1}
output_dir=${1:-"/project/flyspeck-candle-runs/cv-analytic-flyspeck-real-leaf-$(date -u +%Y%m%dT%H%M%SZ)"}
test_fragment="$repo_root/candle/test_cv_compute_analytic_expr_flyspeck_real_leaf.ml"

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_root/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" CANDLE_CV_ANALYTIC_REAL_FLYSPECK_OK \
  "$test_fragment"

grep -q 'CANDLE_CV_ANALYTIC_REAL_FLYSPECK_OK' "$output_dir/candle.log"
printf 'CANDLE_CV_ANALYTIC_REAL_FLYSPECK_WRAPPER_OK output=%s\n' \
  "$output_dir"
