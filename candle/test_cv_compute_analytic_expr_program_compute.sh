#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-expr-checkpoint-v2}
output_dir=${1:-/project/flyspeck-candle-runs/cv-analytic-expr-program-compute-v1-run-001}

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_dir/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" CANDLE_CV_ANALYTIC_EXPR_PROGRAM_COMPUTE_OK \
  "$repo_dir/candle/cv_compute_analytic_expr_program.ml" \
  "$repo_dir/candle/cv_compute_analytic_expr_program_compute.ml" \
  "$repo_dir/candle/test_cv_compute_analytic_expr_program_compute.ml"

printf 'CANDLE_CV_ANALYTIC_EXPR_PROGRAM_COMPUTE_WRAPPER_OK output=%s\n' \
  "$output_dir"
