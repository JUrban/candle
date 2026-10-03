#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-case16594-raw-plan-profile-v1-16g-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-case16594-fixed-mul-square-discriminator-v1-16g-dev-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
profiler="$repo_root/candle/compatibility/certificate_phase_profile.py"
fragment="$repo_root/candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_fixed_mul_square_discriminator.ml"
marker='CANDLE_CV_CASE16594_FIXED_MUL_SQUARE_OK DEVELOPMENT_NON_RELEASE'

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

CANDLE_FRAGMENT_BASE_DIR="$base_dir" \
  CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$runner" "$output_dir" "$marker" "$fragment" &
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
  printf '%s\n' 'restored fixed mul/square discriminator was not found' >&2
  exit 1
fi
printf '%s\n' "$profiled_pid" >"$output_dir/profiled.pid"
python3 "$profiler" --pid "$profiled_pid" --log "$output_dir/candle.log" \
  --output "$output_dir/phase-profile.json" --poll-seconds 0.1 \
  --stop-text "$marker" --wait-for-log-seconds 1800 \
  >"$output_dir/profile-observer.log" 2>&1 &
profile_pid=$!

set +e
wait "$runner_pid"
runner_status=$?
if (( runner_status != 0 )); then kill "$profile_pid" 2>/dev/null; fi
wait "$profile_pid"
profile_status=$?
set -e

(( runner_status == 0 )) || exit "$runner_status"
(( profile_status == 0 )) || {
  sed -n '1,240p' "$output_dir/profile-observer.log" >&2
  exit "$profile_status"
}
sha256sum "$output_dir/phase-profile.json" >"$output_dir/phase-profile.sha256"
printf '%s\n' 'CANDLE_CV_CASE16594_FIXED_MUL_SQUARE_DRIVER_OK'
