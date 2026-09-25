#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-checker-checkpoint-v1}
output_dir=${1:-"/project/flyspeck-candle-runs/cv-analytic-jet-check-$(date -u +%Y%m%dT%H%M%SZ)"}
implementation="$repo_root/candle/cv_compute_analytic_expr_jet_check.ml"
test_fragment="$repo_root/candle/test_cv_compute_analytic_expr_jet_check.ml"
fragments=("$test_fragment")
if [[ ! -f "$base_dir/input-files.sha256" ]] ||
   ! grep -Fq "  $implementation" "$base_dir/input-files.sha256"; then
  fragments=("$implementation" "$test_fragment")
fi

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_root/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" CANDLE_CV_ANALYTIC_JET_CHECK_OK \
  "${fragments[@]}"

grep -q 'CANDLE_CV_ANALYTIC_JET_CHECK_OK' "$output_dir/candle.log"
printf 'CANDLE_CV_ANALYTIC_JET_CHECK_WRAPPER_OK output=%s\n' "$output_dir"
