#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
CANDLE_FIXED_OUTER_GROUPED_POLICY_MARKER=CANDLE_CV_ACTION296_FIXED_OUTER_GROUPED_DISCOVERY_OK \
CANDLE_FIXED_OUTER_GROUPED_POLICY_TEST_FILE="$repo_root/candle/test_cv_compute_analytic_expr_action296_fixed_outer_grouped_policy_discovery.ml" \
  exec "$repo_root/candle/test_cv_compute_analytic_expr_action296_fixed_outer_grouped_policy_proof.sh" "$@"
