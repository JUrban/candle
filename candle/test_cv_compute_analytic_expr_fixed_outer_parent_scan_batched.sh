#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
CANDLE_FIXED_OUTER_PARENT_SCAN_FILE="$repo_root/candle/benchmark_cv_compute_analytic_expr_fixed_outer_parent_scan_batched.ml" \
CANDLE_FIXED_OUTER_PARENT_SCAN_STOP_KEY=fixed-outer-parent-scan/parents/all-batches \
  exec "$repo_root/candle/test_cv_compute_analytic_expr_fixed_outer_parent_scan.sh" "$@"
