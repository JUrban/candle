#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 ]]; then
  printf 'usage: %s [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-case10173-fixed-nonlinear-complete-proof-support-v127-16g-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-case10173-fixed-nonlinear-complete-capture-v1-16g-dev-001}
builder="$repo_root/candle/build_cv_fragment_checkpoint.sh"
profiler="$repo_root/candle/compatibility/certificate_phase_profile.py"
fragment="$repo_root/candle/benchmark_cv_compute_analytic_expr_case10173_fixed_nonlinear_complete_capture.ml"
capture_marker='CANDLE_CV_CASE10173_FIXED_NONLINEAR_COMPLETE_CAPTURE_OK DEVELOPMENT_NON_RELEASE roots=3305 numerical_cells=4173 token_items=8345 active_roots=1 remaining_jobs=0 assumptions=0 axiom_growth=0'
ready_marker='CANDLE_CV_CASE10173_FIXED_NONLINEAR_COMPLETE_CAPTURE_CHECKPOINT_READY_V1'

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

"$builder" "$base_dir" "$output_dir" "$ready_marker" "$fragment" &
builder_pid=$!

profiled_pid=
for _ in $(seq 1 1200); do
  while read -r candidate; do
    if is_descendant "$candidate" "$builder_pid"; then
      profiled_pid=$candidate
      break
    fi
  done < <(ps -eo pid=,args= | awk '$0 ~ /\[DMTCP:cake\]/ {print $1}')
  if [[ -n "$profiled_pid" ]]; then break; fi
  if ! kill -0 "$builder_pid" 2>/dev/null; then break; fi
  sleep 0.1
done

if [[ -z "$profiled_pid" ]]; then
  wait "$builder_pid"
  printf '%s\n' 'restored case-10173 fixed nonlinear process was not found' >&2
  exit 1
fi
printf '%s\n' "$profiled_pid" >"$output_dir/profiled.pid"
python3 "$profiler" --pid "$profiled_pid" --log "$output_dir/base.log" \
  --output "$output_dir/phase-profile.json" --poll-seconds 0.1 \
  --stop-text "$capture_marker" --wait-for-log-seconds 43200 \
  >"$output_dir/profile-observer.log" 2>&1 &
profile_pid=$!

set +e
wait "$builder_pid"
builder_status=$?
wait "$profile_pid"
profile_status=$?
set -e

(( builder_status == 0 )) || exit "$builder_status"
(( profile_status == 0 )) || {
  sed -n '1,240p' "$output_dir/profile-observer.log" >&2
  exit "$profile_status"
}
sha256sum "$output_dir/phase-profile.json" >"$output_dir/phase-profile.sha256"
sha256sum -c "$output_dir/checkpoint.sha256"
sha256sum -c "$output_dir/base-log.sha256"
printf '%s\n' 'CANDLE_CV_CASE10173_FIXED_NONLINEAR_COMPLETE_CAPTURE_DRIVER_OK'
