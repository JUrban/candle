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
base_dir=${4:-/project/flyspeck-candle-runs/cv-action296-box-plan-support-checkpoint-v1-schedule-copy-001}
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"
profiler="$repo_root/candle/compatibility/certificate_phase_profile.py"
marker=${CANDLE_FIXED_OUTER_GROUPED_POLICY_MARKER:-CANDLE_CV_ACTION296_FIXED_OUTER_GROUPED_POLICY_OK}
test_fragment=${CANDLE_FIXED_OUTER_GROUPED_POLICY_TEST_FILE:-"$repo_root/candle/test_cv_compute_analytic_expr_action296_fixed_outer_grouped_policy_proof.ml"}

fragments=(
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_invariant.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_item_invariant.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_program_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_compile_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_certified_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_sound.ml"
  "$repo_root/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_box_certificate_prepare.ml"
  "$repo_root/candle/cv_compute_analytic_expr_action296_adaptive_forest_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_action296_bounded_grouped_forest_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_action296_stable_grouped_forest_prove.ml"
  "$repo_root/candle/cv_compute_analytic_expr_action296_fixed_outer_grouped_forest_prove.ml"
  "$policy"
  "$schedule"
  "$test_fragment"
)

for fragment in "${fragments[@]}"; do
  [[ -f "$fragment" ]]
done

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
  printf '%s\n' 'restored fixed-outer grouped proof process was not found' >&2
  exit 1
fi
printf '%s\n' "$profiled_pid" >"$output_dir/profiled.pid"
python3 "$profiler" --pid "$profiled_pid" --log "$output_dir/candle.log" \
  --output "$output_dir/phase-profile.json" --poll-seconds 0.05 \
  --stop-key action296-fixed-outer-grouped-forest-proof/forest/bounded-forest \
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
printf '%s\n' 'CANDLE_CV_ACTION296_FIXED_OUTER_GROUPED_POLICY_DRIVER_OK'
