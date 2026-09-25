#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-action296-taylor-certified-checkpoint-v1}
mode=${1:-certified}
output_dir=${2:-/project/flyspeck-candle-runs/cv-action296-taylor-batch-${mode}-v1-run-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"

case "$mode" in
  certified)
    marker=CANDLE_CV_ACTION296_CERTIFIED_BATCH_OK
    event_pattern='CANDLE_CV_ACTION296_CERTIFIED_BATCH_(STAGE|CELL|LEAF|RETRY|RESULT|OK)'
    fragments=(
      "$repo_root/candle/cv_compute_analytic_expr_taylor_model_certified_prove.ml"
      "$repo_root/candle/cv_compute_analytic_expr_box_certificate_prepare.ml"
      "$repo_root/candle/cv_compute_analytic_expr_certificate_variant_prepare.ml"
      "$repo_root/candle/test_cv_compute_analytic_expr_action296_certified_taylor_batch.ml"
    )
    ;;
  legacy)
    marker=CANDLE_CV_ACTION296_LEGACY_BATCH_OK
    event_pattern='CANDLE_CV_ACTION296_LEGACY_BATCH_(LEAF|RESULT|OK)'
    fragments=(
      "$repo_root/candle/test_cv_compute_analytic_expr_action296_legacy_batch.ml"
    )
    ;;
  *)
    printf 'unknown action296 Taylor batch mode: %s\n' "$mode" >&2
    exit 2
    ;;
esac

telemetry_tmp=$(mktemp)
resource_tmp=$(mktemp)

cleanup() {
  rm -f "$telemetry_tmp" "$resource_tmp"
}
trap cleanup EXIT

printf 'timestamp_utc\tevent\n' >"$telemetry_tmp"
printf '%s\trun-start mode=%s\n' \
  "$(date -u +%Y-%m-%dT%H:%M:%S.%NZ)" "$mode" >>"$telemetry_tmp"

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  /usr/bin/time -v -o "$resource_tmp" \
  "$runner" "$output_dir" "$marker" "${fragments[@]}" &
runner_pid=$!

(
  while [[ ! -f "$output_dir/candle.log" ]] &&
        kill -0 "$runner_pid" 2>/dev/null; do
    sleep 0.02
  done
  if [[ -f "$output_dir/candle.log" ]]; then
    tail --pid="$runner_pid" -n +1 -F "$output_dir/candle.log" 2>/dev/null |
      stdbuf -oL tr '\r' '\n' |
      stdbuf -oL grep --line-buffered -E "$event_pattern" |
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

printf 'CANDLE_CV_ACTION296_TAYLOR_BATCH_EXTERNAL_TIMING_OK mode=%s output=%s\n' \
  "$mode" "$output_dir"
