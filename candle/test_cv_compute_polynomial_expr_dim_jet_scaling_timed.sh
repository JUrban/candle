#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
output_dir=${1:-/project/flyspeck-candle-runs/cv-polynomial-expression-dim-jet-scaling-timed-v1-run-001}
runner="$repo_dir/candle/test_cv_compute_polynomial_expr_dim_jet_scaling.sh"
telemetry_tmp=$(mktemp)
resource_tmp=$(mktemp)

cleanup() {
  rm -f "$telemetry_tmp" "$resource_tmp"
}
trap cleanup EXIT

printf 'timestamp_utc\tevent\n' >"$telemetry_tmp"
printf '%s\trun-start\n' "$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)" >>"$telemetry_tmp"

/usr/bin/time -v -o "$resource_tmp" "$runner" "$output_dir" &
runner_pid=$!

(
  while [[ ! -f "$output_dir/candle.log" ]] && kill -0 "$runner_pid" 2>/dev/null; do
    sleep 0.02
  done
  if [[ -f "$output_dir/candle.log" ]]; then
    tail --pid="$runner_pid" -n +1 -F "$output_dir/candle.log" 2>/dev/null |
      stdbuf -oL tr '\r' '\n' |
      stdbuf -oL grep --line-buffered -E \
        'CANDLE_DIM_JET_(SCALE phase=|SCALE_PREP|SCALE_RESULT|CHUNKED_PREP|CHUNKED_RESULT)|CANDLE_DIM_FIRST_JET_PROFILE|CANDLE_CV_POLYNOMIAL_EXPR_DIM_JET_SCALING_OK' |
      while IFS= read -r event; do
        printf '%s\t%s\n' "$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)" "$event"
      done
  fi
) >>"$telemetry_tmp" &
monitor_pid=$!

set +e
wait "$runner_pid"
runner_status=$?
wait "$monitor_pid"
monitor_status=$?
set -e

printf '%s\trun-end status=%d monitor_status=%d\n' \
  "$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)" "$runner_status" "$monitor_status" \
  >>"$telemetry_tmp"

if [[ -d "$output_dir" ]]; then
  cp "$telemetry_tmp" "$output_dir/external-phase-timing.tsv"
  cp "$resource_tmp" "$output_dir/resource-usage.txt"
fi

if [[ "$runner_status" -ne 0 ]]; then
  exit "$runner_status"
fi
if [[ "$monitor_status" -ne 0 ]]; then
  exit "$monitor_status"
fi

printf 'CANDLE_DIM_JET_EXTERNAL_TIMING_OK output=%s\n' "$output_dir"
