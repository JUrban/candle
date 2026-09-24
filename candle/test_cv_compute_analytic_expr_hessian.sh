#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-program-checkpoint-v1}
output_dir=${1:-"/project/flyspeck-candle-runs/cv-analytic-expr-hessian-$(date -u +%Y%m%dT%H%M%SZ)"}

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_root/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" CANDLE_CV_ANALYTIC_EXPR_HESSIAN_OK \
  "$repo_root/candle/cv_compute_analytic_expr_calculus.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_partials.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_hessian.ml" \
  "$repo_root/candle/test_cv_compute_analytic_expr_hessian.ml"

grep -q 'CANDLE_CV_ANALYTIC_EXPR_HESSIAN_OK' "$output_dir/candle.log"
printf 'CANDLE_CV_ANALYTIC_EXPR_HESSIAN_WRAPPER_OK output=%s\n' "$output_dir"
