#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/v499-direct-fixed-nonlinear-compute-checkpoint-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-case10173-canonical-mul-prefix128-v1-16g-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
support="$repo_root/candle/cv_compute_analytic_expr_fixed_scale_canonical_mul_compute.ml"
baseline="$repo_root/candle/benchmark_cv_compute_analytic_expr_case10173_bound_tightness_prefix128.ml"
fragment="$repo_root/candle/benchmark_cv_compute_analytic_expr_case10173_canonical_mul_prefix128.ml"
marker='CANDLE_CV_CASE10173_CANONICAL_MUL_PREFIX128_OK'

CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "$support" "$baseline" "$fragment" &
runner_pid=$!

baseline_begin=
baseline_end=
candidate_begin=
candidate_end=
while kill -0 "$runner_pid" 2>/dev/null; do
  if [[ -f "$output_dir/candle.log" ]]; then
    if [[ -z "$baseline_begin" ]] &&
       rg -Fq 'lane=case10173-bound-tightness-prefix128 phase=kernel-compute-begin' \
         "$output_dir/candle.log"; then
      baseline_begin=$(date -u +%s.%N)
    fi
    if [[ -z "$baseline_end" ]] &&
       rg -Fq 'lane=case10173-bound-tightness-prefix128 phase=kernel-compute-end' \
         "$output_dir/candle.log"; then
      baseline_end=$(date -u +%s.%N)
    fi
    if [[ -z "$candidate_begin" ]] &&
       rg -Fq 'lane=case10173-canonical-mul-prefix128 phase=kernel-compute-begin' \
         "$output_dir/candle.log"; then
      candidate_begin=$(date -u +%s.%N)
    fi
    if [[ -z "$candidate_end" ]] &&
       rg -Fq 'lane=case10173-canonical-mul-prefix128 phase=kernel-compute-end' \
         "$output_dir/candle.log"; then
      candidate_end=$(date -u +%s.%N)
    fi
  fi
  sleep 0.02
done
wait "$runner_pid"

[[ -n "$baseline_begin" && -n "$baseline_end" ]]
[[ -n "$candidate_begin" && -n "$candidate_end" ]]
awk -v baseline_begin="$baseline_begin" -v baseline_end="$baseline_end" \
    -v candidate_begin="$candidate_begin" -v candidate_end="$candidate_end" '
  BEGIN {
    baseline = baseline_end - baseline_begin
    candidate = candidate_end - candidate_begin
    printf "lane\tseconds\n"
    printf "baseline\t%.9f\n", baseline
    printf "canonical-mul\t%.9f\n", candidate
    printf "speedup\t%.9f\n", baseline / candidate
  }
' >"$output_dir/phase-times.tsv"

sha256sum -c "$output_dir/result-files.sha256"
sha256sum "$output_dir/phase-times.tsv" >"$output_dir/benchmark-files.sha256"
printf '%s\n' \
  'CANDLE_CV_CASE10173_CANONICAL_MUL_PREFIX128_DRIVER_OK DEVELOPMENT_NON_RELEASE'
