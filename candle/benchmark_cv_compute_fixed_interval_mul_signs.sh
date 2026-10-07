#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/v493-direct-reflected-fixed-core-checkpoint-dev-001}
validation_worktree=${CANDLE_FRAGMENT_VALIDATION_WORKTREE:-/project/worktrees/candle-cv-compute-equation-slicing-v1}
output_dir=${1:-/project/flyspeck-candle-runs/cv-fixed-interval-mul-sign-run-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
fragment="$repo_root/candle/benchmark_cv_compute_fixed_interval_mul_signs.ml"
marker=CANDLE_CV_FS_INTERVAL_MUL_SIGN_OK
event_pattern='CANDLE_CERT_PROFILE lane=fixed-interval-mul-sign'

[[ -d "$validation_worktree" ]]
[[ ! -e "$output_dir" ]]

telemetry_tmp=$(mktemp)
resource_tmp=$(mktemp)

cleanup() {
  rm -f "$telemetry_tmp" "$resource_tmp"
}
trap cleanup EXIT

printf 'timestamp_utc\tevent\n' >"$telemetry_tmp"
printf '%s\trun-start\n' "$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)" \
  >>"$telemetry_tmp"

(
  cd "$validation_worktree"
  CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
    /usr/bin/time -v -o "$resource_tmp" \
    "$runner" "$output_dir" "$marker" "$fragment"
) &
runner_pid=$!

(
  while [[ ! -f "$output_dir/candle.log" ]] &&
        kill -0 "$runner_pid" 2>/dev/null; do
    sleep 0.02
  done
  if [[ -f "$output_dir/candle.log" ]]; then
    tail --pid="$runner_pid" -n +1 -F "$output_dir/candle.log" 2>/dev/null |
      stdbuf -oL tr '\r' '\n' |
      stdbuf -oL grep --line-buffered -F "$event_pattern" |
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
  "$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)" \
  "$runner_status" "$monitor_status" >>"$telemetry_tmp"

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

printf '%s\n' \
  'CANDLE_CV_FS_INTERVAL_MUL_SIGN_EXTERNAL_TIMING_OK DEVELOPMENT_NON_RELEASE'
