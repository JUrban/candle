#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 ]]; then
  printf 'usage: %s [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_DISJUNCTIVE_FIXED_OUTER_BASE_DIR:-/project/flyspeck-candle-runs/cv-disjunctive-plan-support-checkpoint-v1}
run_dir=${1:-/project/flyspeck-candle-runs/cv-disjunctive-fixed-outer-support-checkpoint-v2}
ready_marker=CANDLE_CV_DISJUNCTIVE_FIXED_OUTER_CHECKPOINT_READY

fragments=(
  # The disjunctive plan refreshes the analytic prepared-record type after
  # extending the reifier.  Refresh its two OCaml-level consumers as one
  # coherent layer before loading the fixed-outer proof adapter.
  "$repo_root/candle/cv_compute_analytic_expr_box_certificate_prepare.ml"
  "$repo_root/candle/cv_compute_analytic_expr_certificate_variant_prepare.ml"
  "$repo_root/candle/cv_compute_analytic_expr_stable_batch_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_invariant.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_item_invariant.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_program_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_compile_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_certified_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove.ml"
)

exec "$repo_root/candle/build_cv_fragment_checkpoint.sh" \
  "$base_dir" "$run_dir" "$ready_marker" "${fragments[@]}"
