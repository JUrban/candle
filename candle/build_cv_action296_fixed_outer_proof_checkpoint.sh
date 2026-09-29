#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 ]]; then
  printf 'usage: %s [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_ACTION296_FIXED_OUTER_PROOF_BASE_DIR:-/project/flyspeck-candle-runs/cv-action296-box-plan-support-checkpoint-v1-schedule-copy-001}
run_dir=${1:-/project/flyspeck-candle-runs/cv-action296-fixed-outer-proof-support-checkpoint-v1}
ready_marker=CANDLE_CV_ACTION296_FIXED_OUTER_PROOF_CHECKPOINT_READY

fragments=(
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_invariant.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_item_invariant.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_program_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_compile_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_certified_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove.ml"
)

exec "$repo_dir/candle/build_cv_fragment_checkpoint.sh" \
  "$base_dir" "$run_dir" "$ready_marker" "${fragments[@]}"
