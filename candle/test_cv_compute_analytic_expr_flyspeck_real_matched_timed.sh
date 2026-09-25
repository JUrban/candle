#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-driver-checkpoint-v1}
output_dir=${1:-/project/flyspeck-candle-runs/cv-analytic-flyspeck-real-matched-timed-v1-run-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
first_program="$repo_root/candle/cv_compute_analytic_expr_first_jet_program_compute.ml"
first_check="$repo_root/candle/cv_compute_analytic_expr_first_center_check.ml"
prover="$repo_root/candle/cv_compute_analytic_expr_jet_prove.ml"
driver="$repo_root/candle/cv_compute_flyspeck_nonlinear_driver.ml"
test_fragment="$repo_root/candle/test_cv_compute_analytic_expr_flyspeck_real_matched.ml"
fragments=()
checkpoint_has_exact_file() {
  [[ -f "$base_dir/input-files.sha256" ]] &&
    sha256sum "$1" | grep -Fqx -f - "$base_dir/input-files.sha256"
}
for fragment in "$first_program" "$first_check" "$prover" "$driver"; do
  if ! checkpoint_has_exact_file "$fragment"; then
    fragments+=("$fragment")
  fi
done
fragments+=("$test_fragment")
telemetry_tmp=$(mktemp)
resource_tmp=$(mktemp)

cleanup() {
  rm -f "$telemetry_tmp" "$resource_tmp"
}
trap cleanup EXIT

printf 'timestamp_utc\tevent\n' >"$telemetry_tmp"
printf '%s\trun-start\n' "$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)" \
  >>"$telemetry_tmp"

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  /usr/bin/time -v -o "$resource_tmp" \
  "$runner" "$output_dir" CANDLE_CV_ANALYTIC_MATCHED_OK \
  "${fragments[@]}" &
runner_pid=$!

(
  while [[ ! -f "$output_dir/candle.log" ]] && \
        kill -0 "$runner_pid" 2>/dev/null; do
    sleep 0.02
  done
  if [[ -f "$output_dir/candle.log" ]]; then
    tail --pid="$runner_pid" -n +1 -F "$output_dir/candle.log" 2>/dev/null |
      stdbuf -oL tr '\r' '\n' |
      stdbuf -oL grep --line-buffered -E \
        'CANDLE_CV_ANALYTIC_MATCHED_(BEGIN|END|RESULT|OK)' |
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

printf 'CANDLE_CV_ANALYTIC_MATCHED_EXTERNAL_TIMING_OK output=%s\n' \
  "$output_dir"
