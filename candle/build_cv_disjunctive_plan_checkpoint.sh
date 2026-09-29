#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 ]]; then
  printf 'usage: %s [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_DISJUNCTIVE_PLAN_BASE_DIR:-/project/flyspeck-candle-runs/cv-disjunctive-post-adaptive-base-v1}
run_dir=${1:-/project/flyspeck-candle-runs/cv-disjunctive-plan-support-checkpoint-v1}
ready_marker=CANDLE_CV_DISJUNCTIVE_PLAN_CHECKPOINT_READY
leaf_fixture="$repo_root/candle/cv_compute_analytic_expr_disjunctive_leaf_grouping_fixture.ml"

exec "$repo_root/candle/build_cv_fragment_checkpoint.sh" \
  "$base_dir" "$run_dir" "$ready_marker" "$leaf_fixture"
