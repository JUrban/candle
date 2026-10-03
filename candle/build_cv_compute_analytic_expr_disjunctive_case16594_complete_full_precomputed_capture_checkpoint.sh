#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-case16594-complete-lean-compute-support-minimal-v2-16g-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-case16594-complete-full-precomputed-capture-checkpoint-v2-16g-dev-001}
builder="$repo_root/candle/build_cv_fragment_checkpoint.sh"
marker='CANDLE_CV_CASE16594_COMPLETE_FULL_CAPTURE_CHECKPOINT_READY_V2 DEVELOPMENT_NON_RELEASE'

"$builder" "$base_dir" "$output_dir" "$marker" \
  "$repo_root/candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_full_precomputed_capture.ml"
