#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 3 || $# -gt 4 ]]; then
  printf 'usage: %s POLICY_ML SCHEDULE_ML OUTPUT_DIR [BASE_DIR]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
policy=$1
schedule=$2
output_dir=$3
base_dir=${4:-/project/flyspeck-candle-runs/cv-case10173-fixed-outer-support-checkpoint-v1}
builder="$repo_root/candle/build_cv_fragment_checkpoint.sh"
profiler="$repo_root/candle/compatibility/certificate_phase_profile.py"
ready_marker=${CANDLE_CASE10173_FIXED_OUTER_PROOF_READY_MARKER:-CANDLE_CV_CASE10173_FIXED_OUTER_PROOF_CHECKPOINT_READY}
proof_fragment=${CANDLE_CASE10173_FIXED_OUTER_PROOF_FRAGMENT:-"$repo_root/candle/test_cv_compute_analytic_expr_action296_fixed_outer_grouped_policy_proof.ml"}
fragments=(
  "$policy"
  "$schedule"
  "$proof_fragment"
)

for fragment in "${fragments[@]}"; do [[ -f "$fragment" ]]; done

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

"$builder" "$base_dir" "$output_dir" "$ready_marker" \
  "${fragments[@]}" &
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
  printf '%s\n' 'case10173 fixed-outer proof process was not found' >&2
  exit 1
fi
printf '%s\n' "$profiled_pid" >"$output_dir/profiled.pid"
python3 "$profiler" --pid "$profiled_pid" --log "$output_dir/base.log" \
  --output "$output_dir/phase-profile.json" --poll-seconds 0.05 \
  --stop-key action296-fixed-outer-grouped-forest-proof/forest/bounded-forest \
  --wait-for-log-seconds 43200 >"$output_dir/profile-observer.log" 2>&1 &
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
sha256sum -c "$output_dir/checkpoint.sha256"
sha256sum -c "$output_dir/base-log.sha256"
sha256sum "$output_dir/phase-profile.json" \
  "$output_dir/profile-observer.log" >"$output_dir/profile-files.sha256"
printf '%s\n' 'CANDLE_CV_CASE10173_FIXED_OUTER_PROOF_CHECKPOINT_DRIVER_OK'
