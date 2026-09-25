#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-driver-checkpoint-v3}
output_dir=${1:-/project/flyspeck-candle-runs/cv-exact-interval-atn-series-v1-run-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=0 \
  /usr/bin/time -v -o /tmp/candle-atn-series-resource-$$.txt \
  "$runner" "$output_dir" CANDLE_CV_EXACT_INTERVAL_ATN_SERIES_OK \
  "$repo_root/candle/cv_compute_exact_interval_atn_series.ml" \
  "$repo_root/candle/test_cv_compute_exact_interval_atn_series.ml"

mv /tmp/candle-atn-series-resource-$$.txt "$output_dir/resource-usage.txt"
printf 'CANDLE_CV_EXACT_INTERVAL_ATN_SERIES_WRAPPER_OK output=%s\n' \
  "$output_dir"
