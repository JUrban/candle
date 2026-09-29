#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 ]]; then
  printf 'usage: %s [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
flyspeck_root=${CANDLE_DISJUNCTIVE_FLYSPECK_DIR:-/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6}
base_dir=${CANDLE_DISJUNCTIVE_FAMILY_BASE_DIR:-/project/flyspeck-candle-runs/cv-disjunctive-fixed-outer-support-checkpoint-v3}
run_dir=${1:-/project/flyspeck-candle-runs/cv-disjunctive-family-support-checkpoint-v1}
ready_marker=CANDLE_CV_DISJUNCTIVE_FAMILY_SUPPORT_CHECKPOINT_READY

python3 "$repo_root/candle/flyspeck_nonlinear_disjunctive_target.py" \
  --flyspeck-root "$flyspeck_root" --check

exec "$repo_root/candle/build_cv_fragment_checkpoint.sh" \
  "$base_dir" "$run_dir" "$ready_marker" \
  "$repo_root/candle/cv_compute_analytic_expr_disjunctive_fixed_outer_prove.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_disjunctive_family_prove.ml"
