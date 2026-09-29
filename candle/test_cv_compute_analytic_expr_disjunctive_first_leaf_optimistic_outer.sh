#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
flyspeck_root=${CANDLE_DISJUNCTIVE_FLYSPECK_DIR:-/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6}
base_dir=${CANDLE_DISJUNCTIVE_OPTIMISTIC_BASE_DIR:-/project/flyspeck-candle-runs/cv-disjunctive-fixed-outer-support-checkpoint-v3}
output_dir=${1:-/project/flyspeck-candle-runs/cv-disjunctive-first-leaf-optimistic-outer-v1-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
fragment="$repo_root/candle/test_cv_compute_analytic_expr_disjunctive_first_leaf_optimistic_outer.ml"
marker=CANDLE_CV_DISJUNCTIVE_OPTIMISTIC_OK

python3 "$repo_root/candle/flyspeck_nonlinear_disjunctive_target.py" \
  --flyspeck-root "$flyspeck_root" --check

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "$fragment"

sha256sum -c "$output_dir/result-files.sha256"
rg -F 'CANDLE_CV_DISJUNCTIVE_OPTIMISTIC_RESULT' "$output_dir/candle.log"
printf '%s\n' CANDLE_CV_DISJUNCTIVE_OPTIMISTIC_DRIVER_OK
