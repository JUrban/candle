#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-action296-taylor-certified-checkpoint-v1}
output_dir=${1:-/project/flyspeck-candle-runs/cv-action296-fixed-scale-reflected-v1-run-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
profiler="$repo_root/candle/compatibility/certificate_phase_profile.py"
marker=CANDLE_CV_ACTION296_FIXED_SCALE_REFLECTED_OK
fragments=(
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_certified_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_point_certificate_prepare.ml"
  "$repo_root/candle/cv_compute_analytic_expr_box_certificate_prepare.ml"
  "$repo_root/candle/cv_compute_analytic_expr_certificate_variant_prepare.ml"
  "$repo_root/candle/cv_compute_analytic_expr_fixed_scale_compute.ml"
  "$repo_root/candle/benchmark_cv_compute_analytic_expr_action296_fixed_scale_reflected.ml"
)

is_descendant() {
  local candidate=$1 ancestor=$2 parent
  while [[ "$candidate" =~ ^[0-9]+$ ]] && (( candidate > 1 )); do
    if (( candidate == ancestor )); then return 0; fi
    parent=$(ps -o ppid= -p "$candidate" 2>/dev/null | tr -d ' ')
    [[ "$parent" =~ ^[0-9]+$ ]] || return 1
    candidate=$parent
  done
  return 1
}

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "${fragments[@]}" &
runner_pid=$!

profiled_pid=
for _ in $(seq 1 1200); do
  while read -r candidate; do
    if is_descendant "$candidate" "$runner_pid"; then
      profiled_pid=$candidate
      break
    fi
  done < <(ps -eo pid=,args= | awk '$0 ~ /\[DMTCP:cake\]/ {print $1}')
  if [[ -n "$profiled_pid" ]]; then break; fi
  if ! kill -0 "$runner_pid" 2>/dev/null; then break; fi
  sleep 0.1
done

if [[ -z "$profiled_pid" ]]; then
  wait "$runner_pid"
  printf '%s\n' 'restored action-296 reflected fixed process was not found' >&2
  exit 1
fi
printf '%s\n' "$profiled_pid" >"$output_dir/profiled.pid"
python3 "$profiler" --pid "$profiled_pid" --log "$output_dir/candle.log" \
  --output "$output_dir/phase-profile.json" --poll-seconds 0.01 \
  --stop-key action296-fs-reflected/batch/profiled-run \
  --wait-for-log-seconds 1200 >"$output_dir/profile-observer.log" 2>&1 &
profile_pid=$!

set +e
wait "$runner_pid"
runner_status=$?
wait "$profile_pid"
profile_status=$?
set -e

(( runner_status == 0 )) || exit "$runner_status"
(( profile_status == 0 )) || {
  sed -n '1,240p' "$output_dir/profile-observer.log" >&2
  exit "$profile_status"
}
printf '%s\n' 'CANDLE_CV_ACTION296_FIXED_SCALE_REFLECTED_DRIVER_OK'
