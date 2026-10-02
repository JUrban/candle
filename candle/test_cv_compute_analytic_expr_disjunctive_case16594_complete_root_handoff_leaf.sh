#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-case16594-complete-proof-support-v4-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-case16594-complete-root-handoff-leaf-v1-dev-001}
marker='CANDLE_CV_CASE16594_COMPLETE_ROOT_HANDOFF_LEAF_OK DEVELOPMENT_NON_RELEASE'

CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_root/candle/restart_real_functions_with_fragments.sh" \
    "$output_dir" "$marker" \
    "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove.ml" \
    "$repo_root/candle/test_cv_compute_analytic_expr_disjunctive_case16594_complete_root_handoff_leaf.ml"
