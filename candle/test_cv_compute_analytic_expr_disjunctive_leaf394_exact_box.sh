#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_DISJUNCTIVE_EXACT_BOX_BASE_DIR:-/project/flyspeck-candle-runs/cv-disjunctive-fixed-outer-support-checkpoint-v3}
output_dir=${1:-/project/flyspeck-candle-runs/cv-disjunctive-leaf394-exact-box-v1-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
prover="$repo_root/candle/cv_compute_analytic_expr_disjunctive_fixed_outer_prove.ml"
test_fragment="$repo_root/candle/test_cv_compute_analytic_expr_disjunctive_leaf394_exact_box.ml"
marker=CANDLE_CV_DISJUNCTIVE_LEAF394_EXACT_BOX_OK

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "$prover" "$test_fragment"

sha256sum -c "$output_dir/result-files.sha256"
rg -F 'CANDLE_CV_DISJUNCTIVE_LEAF394_EXACT_BOX_RESULT' \
  "$output_dir/candle.log"
printf '%s\n' CANDLE_CV_DISJUNCTIVE_LEAF394_EXACT_BOX_DRIVER_OK
