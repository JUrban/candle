#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-case10173-complete-capture-checkpoint-v1-16g-dev-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-case10173-complete-proof-support-v1-16g-dev-001}
builder="$repo_root/candle/build_cv_fragment_checkpoint.sh"
profiler="$repo_root/candle/compatibility/certificate_phase_profile.py"
ready_marker='CANDLE_CV_CASE10173_COMPLETE_PROOF_SUPPORT_READY_V1'
fragments=(
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_batch.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_tree.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_tree_compact.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_tree_compact_correct.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_tree_compact_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove.ml"
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

"$builder" "$base_dir" "$output_dir" "$ready_marker" "${fragments[@]}" &
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
  printf '%s\n' 'restored case-10173 proof-support process was not found' >&2
  exit 1
fi
printf '%s\n' "$profiled_pid" >"$output_dir/profiled.pid"
python3 "$profiler" --pid "$profiled_pid" --log "$output_dir/base.log" \
  --output "$output_dir/phase-profile.json" --poll-seconds 0.2 \
  --stop-text "$ready_marker" --wait-for-log-seconds 43200 \
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
printf '%s\n' 'CANDLE_CV_CASE10173_COMPLETE_PROOF_SUPPORT_DRIVER_OK'
