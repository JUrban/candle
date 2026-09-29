#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
CANDLE_CASE10173_FIXED_OUTER_PROOF_READY_MARKER=CANDLE_CV_CASE10173_FIXED_OUTER_ADAPTIVE_PROOF_CHECKPOINT_READY \
CANDLE_CASE10173_FIXED_OUTER_PROOF_FRAGMENT="$repo_root/candle/test_cv_compute_analytic_expr_action296_fixed_outer_grouped_policy_discovery.ml" \
  exec "$repo_root/candle/build_cv_case10173_fixed_outer_proof_checkpoint.sh" "$@"
