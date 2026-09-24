#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
base_dir=/project/flyspeck-candle-runs/cv-nonlinear-real-functions-checkpoint-v1
run_dir=${1:-/project/flyspeck-candle-runs/cv-nonlinear-reflected-driver-checkpoint-v1}
ready_marker=CANDLE_NL_REFLECTED_DRIVER_CHECKPOINT_READY
fragments=(
  "$repo_dir/candle/compute.ml"
  "$repo_dir/candle/cv_compute_linear_combination_core.ml"
  "$repo_dir/candle/cv_compute_linear_combination_sound.ml"
  "$repo_dir/candle/cv_compute_linear_combination_realize.ml"
  "$repo_dir/candle/cv_compute_exact_rational_core.ml"
  "$repo_dir/candle/cv_compute_exact_interval_core.ml"
  "$repo_dir/candle/cv_compute_exact_rational_order_core.ml"
  "$repo_dir/candle/cv_compute_exact_interval_mul_core.ml"
  "$repo_dir/candle/cv_compute_exact_interval_square_core.ml"
  "$repo_dir/candle/cv_compute_exact_interval_program.ml"
  "$repo_dir/candle/cv_compute_exact_interval_reify.ml"
  "$repo_dir/candle/cv_compute_whole_box_taylor.ml"
  "$repo_dir/candle/cv_compute_whole_box_jet.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_jet.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_derivatives.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet.ml"
  "$repo_dir/candle/cv_compute_linear_combination.ml"
  "$repo_dir/candle/cv_compute_linear_combination_normalize.ml"
  "$repo_dir/candle/cv_compute_exact_rational_normalize.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_reify.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_calculus.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_calculus.ml"
  "$repo_dir/candle/cv_compute_whole_box_dim_taylor.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_diff.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_flyspeck_dim_bridge.ml"
  "$repo_dir/candle/cv_compute_whole_box_dim_taylor_sound.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_check.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_flyspeck_dim_sound.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_flyspeck_reify.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_flyspeck_fixture.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_compute.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_representation.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_first_jet_compute.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_first_jet_representation.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_semantics.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_check.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_sound.ml"
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_prove.ml"
  "$repo_dir/candle/cv_compute_flyspeck_nonlinear_driver.ml"
)

[[ -f "$base_dir/CHECKPOINT-READY" ]]
[[ ! -f "$base_dir/CHECKPOINT-FAILED" ]]
[[ ! -e "$run_dir" ]]
for fragment in "${fragments[@]}"; do [[ -f "$fragment" ]]; done
mapfile -t source_checkpoints < <(
  find "$base_dir/checkpoint" -maxdepth 1 -type f -name 'ckpt_*.dmtcp' -print
)
[[ ${#source_checkpoints[@]} -eq 1 ]]
sha256sum -c "$base_dir/checkpoint.sha256"
sha256sum -c "$base_dir/base-log.sha256"
sha256sum -c "$base_dir/input-files.sha256"

mkdir -p "$run_dir/checkpoint" "$run_dir/dmtcp-tmp"
skip_needs=
for fragment in "${fragments[@]}"; do
  skip_needs+="candle/$(basename "$fragment")"$'\n'
done
{
  printf 'print_endline "CANDLE_NL_REFLECTED_DRIVER_BUILD_INPUT_ACK";;\n'
  printf 'load_path := ["/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6/formal_ineqs"; "%s"] @ !load_path;;\n' "$repo_dir"
  for fragment in "${fragments[@]}"; do
    fragment_sha256=$(sha256sum "$fragment" | awk '{print $1}')
    printf 'print_endline "CANDLE_RESTORE_FRAGMENT_BEGIN sha256=%s file=%s";;\n' \
      "$fragment_sha256" "$(basename "$fragment")"
    awk -v skip_needs="$skip_needs" '
      BEGIN {
        count = split(skip_needs, paths, "\n")
        for (i = 1; i <= count; i++) if (paths[i] != "") skip[paths[i]] = 1
      }
      {
        candidate = $0
        if (candidate ~ /^needs "[^"]+";;$/) {
          sub(/^needs "/, "", candidate)
          sub(/";;$/, "", candidate)
          if (candidate in skip) next
        }
        print
      }
    ' "$fragment"
    printf 'print_endline "CANDLE_RESTORE_FRAGMENT_END sha256=%s file=%s";;\n' \
      "$fragment_sha256" "$(basename "$fragment")"
  done
  printf 'print_endline "%s";;\n' "$ready_marker"
} >"$run_dir/setup.ml"
sha256sum "${fragments[@]}" >"$run_dir/fragments.sha256"

mkfifo "$run_dir/input.fifo" "$run_dir/output.fifo"
tail -f /dev/null >"$run_dir/input.fifo" &
keeper_pid=$!
tee "$run_dir/base.log" <"$run_dir/output.fifo" >/dev/null &
reader_pid=$!
runtime_pid=
cleanup() {
  kill "$keeper_pid" "$reader_pid" 2>/dev/null || true
  if [[ -n "$runtime_pid" ]]; then kill "$runtime_pid" 2>/dev/null || true; fi
}
trap cleanup EXIT

env -i PATH=/project/bin:/usr/local/bin:/usr/bin:/bin LC_ALL=C \
  DMTCP_TMPDIR="$run_dir/dmtcp-tmp" \
  timeout 21600 dmtcp_restart --new-coordinator --coord-port 0 \
    --port-file "$run_dir/coord.port" --ckptdir "$run_dir/checkpoint" \
    "${source_checkpoints[0]}" \
    <"$run_dir/input.fifo" >"$run_dir/output.fifo" 2>&1 &
runtime_pid=$!
printf '%s\n' "$runtime_pid" >"$run_dir/runtime.pid"
for _ in $(seq 1 300); do
  [[ -s "$run_dir/coord.port" ]] && break
  kill -0 "$runtime_pid" 2>/dev/null || break
  sleep 0.1
done
[[ -s "$run_dir/coord.port" ]]
sed -n '1,$p' "$run_dir/setup.ml" >"$run_dir/input.fifo"

fail() {
  printf '%s\n' "$1" | tee "$run_dir/CHECKPOINT-FAILED" >&2
  if [[ -s "$run_dir/coord.port" ]]; then
    dmtcp_command --port "$(<"$run_dir/coord.port")" -k \
      >>"$run_dir/dmtcp-checkpoint.log" 2>&1 || true
  fi
  exit 1
}

while true; do
  if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$run_dir/base.log"; then
    fail 'runtime reported a source error before reflected-driver readiness'
  fi
  ready_count=$(rg -Foc "$ready_marker" "$run_dir/base.log" || true)
  [[ "$ready_count" -le 1 ]] || fail 'reflected readiness marker repeated'
  if [[ "$ready_count" -eq 1 ]]; then
    port=$(<"$run_dir/coord.port")
    dmtcp_command --port "$port" -bc >"$run_dir/dmtcp-checkpoint.log" 2>&1
    checkpoint=
    stable_size=
    stable_samples=0
    for _ in $(seq 1 600); do
      mapfile -t checkpoints < <(
        find "$run_dir/checkpoint" -maxdepth 1 -type f -name 'ckpt_*.dmtcp' -print
      )
      mapfile -t temporary < <(
        find "$run_dir/checkpoint" -maxdepth 1 -name '*.temp' -print
      )
      if [[ ${#checkpoints[@]} -eq 1 && ${#temporary[@]} -eq 0 ]]; then
        current_size=$(stat -c '%s' "${checkpoints[0]}")
        if [[ "$current_size" -gt 0 && "$current_size" == "$stable_size" ]]; then
          stable_samples=$((stable_samples + 1))
        else
          stable_size=$current_size
          stable_samples=0
        fi
        if [[ "$stable_samples" -ge 2 ]]; then checkpoint=${checkpoints[0]}; break; fi
      fi
      sleep 1
    done
    [[ -n "$checkpoint" ]] || fail 'reflected checkpoint did not stabilize'
    sha256sum "$checkpoint" >"$run_dir/checkpoint.sha256"
    sha256sum "$run_dir/base.log" >"$run_dir/base-log.sha256"
    sha256sum "$base_dir/checkpoint.sha256" "${fragments[@]}" \
      "$run_dir/setup.ml" "$repo_dir/candle/build_reflected_real_checkpoint.sh" \
      "$repo_dir/candle/restart_reflected_real_checkpoint.sh" \
      >"$run_dir/input-files.sha256"
    touch "$run_dir/CHECKPOINT-READY"
    dmtcp_command --port "$port" -k >>"$run_dir/dmtcp-checkpoint.log" 2>&1 || true
    set +e
    wait "$runtime_pid"
    set -e
    runtime_pid=
    wait "$reader_pid"
    reader_pid=
    kill "$keeper_pid" 2>/dev/null || true
    keeper_pid=
    printf '%s\n' CANDLE_NL_REFLECTED_DRIVER_CHECKPOINT_OK
    exit 0
  fi
  kill -0 "$runtime_pid" 2>/dev/null ||
    fail 'runtime exited before reflected-driver readiness'
  sleep 1
done
