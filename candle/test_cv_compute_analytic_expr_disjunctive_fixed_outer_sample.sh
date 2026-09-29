#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
flyspeck_root=${CANDLE_DISJUNCTIVE_FLYSPECK_DIR:-/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6}
base_dir=${CANDLE_DISJUNCTIVE_SAMPLE_BASE_DIR:-/project/flyspeck-candle-runs/cv-disjunctive-fixed-outer-support-checkpoint-v3}
output_dir=${1:-/project/flyspeck-candle-runs/cv-disjunctive-fixed-outer-sample-v1-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
prover="$repo_root/candle/cv_compute_analytic_expr_disjunctive_fixed_outer_prove.ml"
test_fragment="$repo_root/candle/test_cv_compute_analytic_expr_disjunctive_fixed_outer_sample.ml"
marker=CANDLE_CV_DISJUNCTIVE_SAMPLE_OK

python3 "$repo_root/candle/flyspeck_nonlinear_disjunctive_target.py" \
  --flyspeck-root "$flyspeck_root" --check

started_ns=$(date -u +%s%N)
started_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)
CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "$prover" "$test_fragment" &
runner_pid=$!

timing_file="$output_dir/leaf-timing.receipt"
seen=0
while kill -0 "$runner_pid" 2>/dev/null; do
  if [[ -f "$output_dir/candle.log" ]]; then
    count=$(rg -c '^CANDLE_CV_DISJUNCTIVE_SAMPLE_LEAF_RESULT ' \
      "$output_dir/candle.log" || true)
    while [[ "$seen" -lt "$count" ]]; do
      seen=$((seen + 1))
      line=$(rg '^CANDLE_CV_DISJUNCTIVE_SAMPLE_LEAF_RESULT ' \
        "$output_dir/candle.log" | sed -n "${seen}p")
      printf 'observed_ns=%s observed_utc=%s %s\n' \
        "$(date -u +%s%N)" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$line" \
        >>"$timing_file"
    done
  fi
  sleep 0.2
done

set +e
wait "$runner_pid"
runner_status=$?
set -e
completed_ns=$(date -u +%s%N)
completed_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'started_ns=%s started_utc=%s completed_ns=%s completed_utc=%s\n' \
  "$started_ns" "$started_utc" "$completed_ns" "$completed_utc" \
  >>"$timing_file"
if [[ "$runner_status" -ne 0 ]]; then exit "$runner_status"; fi

sha256sum -c "$output_dir/result-files.sha256"
rg -F 'CANDLE_CV_DISJUNCTIVE_SAMPLE_' "$output_dir/candle.log" \
  | rg 'RESULT|OK'
printf '%s\n' CANDLE_CV_DISJUNCTIVE_SAMPLE_DRIVER_OK
