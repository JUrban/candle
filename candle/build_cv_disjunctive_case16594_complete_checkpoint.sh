#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 2 ]]; then
  printf 'usage: %s [BASE_DIR] [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${1:-/project/flyspeck-candle-runs/cv-disjunctive-case16594-family-832-through-859-checkpoint-v1-dev-001}
run_dir=${2:-/project/flyspeck-candle-runs/cv-disjunctive-case16594-complete-v1-dev-001}
ready_marker=CANDLE_CV_DISJUNCTIVE_CASE16594_COMPLETE_CHECKPOINT_READY

exec "$repo_root/candle/build_cv_fragment_checkpoint.sh" \
  "$base_dir" "$run_dir" "$ready_marker" \
  "$repo_root/candle/cv_compute_analytic_expr_disjunctive_case16594_complete.ml"
