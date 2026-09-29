#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
  printf 'usage: %s CONFIG_ML OUTPUT_DIR [BASE_DIR]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
config=$1
output_dir=$2
base_dir=${3:-/project/flyspeck-candle-runs/cv-case10173-fixed-outer-support-checkpoint-v1-directbuild-001}
runner="$repo_root/candle/restart_real_functions_with_fragments_strict.sh"
profiler="$repo_root/candle/compatibility/certificate_phase_profile.py"
stable_data="$repo_root/candle/cv_compute_analytic_expr_stable_program_data.ml"
flags="$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_flags.ml"
scanner="$repo_root/candle/benchmark_cv_compute_analytic_expr_fixed_outer_parent_scan.ml"
marker=CANDLE_CV_FIXED_OUTER_PARENT_SCAN_OK

[[ -f "$config" ]]
fragments=("$stable_data" "$flags" "$config" "$scanner")

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
  printf '%s\n' 'restored fixed-outer parent scan process was not found' >&2
  exit 1
fi
printf '%s\n' "$profiled_pid" >"$output_dir/profiled.pid"
python3 "$profiler" --pid "$profiled_pid" --log "$output_dir/candle.log" \
  --output "$output_dir/phase-profile.json" --poll-seconds 0.05 \
  --stop-key fixed-outer-parent-scan/parents/kernel-compute \
  --wait-for-log-seconds 43200 >"$output_dir/profile-observer.log" 2>&1 &
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
sha256sum -c "$output_dir/result-files.sha256"
sha256sum "$output_dir/phase-profile.json" \
  "$output_dir/profile-observer.log" >"$output_dir/profile-files.sha256"
printf '%s\n' 'CANDLE_CV_FIXED_OUTER_PARENT_SCAN_DRIVER_OK'
