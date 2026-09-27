#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FIXED_SOUND_CHECKPOINT_DIR:-/project/flyspeck-candle-runs/cv-fixed-scale-sound-checkpoint-v1}
output_dir=${1:-/project/flyspeck-candle-runs/cv-fixed-algebraic-sound-v1-run-001}
runner="$repo_root/candle/restart_real_functions_with_fragments_strict.sh"
marker=CANDLE_CV_FIXED_ALGEBRAIC_SOUND_OK

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" \
  "$repo_root/candle/cv_compute_analytic_expr_fixed_scale_complete_sound.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_fixed_scale_invariant.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_sound.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_compute.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compute.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_sound.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_item_sound.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_invariant.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_program_sound.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound.ml" \
  "$repo_root/candle/test_cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_sound.ml"
