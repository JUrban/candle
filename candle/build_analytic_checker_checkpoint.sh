#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
base_dir=${CANDLE_ANALYTIC_CHECKER_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-taylor-checkpoint-v1}
run_dir=${1:-/project/flyspeck-candle-runs/cv-nonlinear-analytic-checker-checkpoint-v1}
input_ack=CANDLE_NL_ANALYTIC_CHECKER_BUILD_INPUT_ACK
ready_marker=CANDLE_NL_ANALYTIC_CHECKER_CHECKPOINT_READY
fragments=(
  "$repo_dir/candle/cv_compute_analytic_expr_jet_check.ml"
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

exec 9>"$base_dir/restart.lock"
flock 9

mkdir -p "$run_dir/checkpoint" "$run_dir/dmtcp-tmp"
{
  printf 'print_endline "%s";;\n' "$input_ack"
  printf 'load_path := ["/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6/formal_ineqs"; "%s"] @ !load_path;;\n' "$repo_dir"
  for fragment in "${fragments[@]}"; do
    fragment_sha256=$(sha256sum "$fragment" | awk '{print $1}')
    printf 'print_endline "CANDLE_RESTORE_FRAGMENT_BEGIN sha256=%s file=%s";;\n' \
      "$fragment_sha256" "$(basename "$fragment")"
    awk '
      {
        candidate = $0
        if (candidate ~ /^needs "[^"]+";;$/) next
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
    fail 'runtime reported a source error before analytic-checker readiness'
  fi
  ack_count=$(rg -Foc "$input_ack" "$run_dir/base.log" || true)
  ready_count=$(rg -Foc "$ready_marker" "$run_dir/base.log" || true)
  [[ "$ack_count" -le 1 ]] || fail 'analytic-checker input acknowledgement repeated'
  [[ "$ready_count" -le 1 ]] || fail 'analytic-checker readiness marker repeated'
  if [[ "$ready_count" -eq 1 ]]; then
    [[ "$ack_count" -eq 1 ]] || fail 'fresh analytic-checker input was not acknowledged'
    ack_line=$(rg -Fn -m1 "$input_ack" "$run_dir/base.log" | cut -d: -f1)
    ready_line=$(rg -Fn -m1 "$ready_marker" "$run_dir/base.log" | cut -d: -f1)
    [[ "$ready_line" -gt "$ack_line" ]] ||
      fail 'analytic-checker readiness did not follow fresh-input acknowledgement'
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
    [[ -n "$checkpoint" ]] || fail 'analytic-checker checkpoint did not stabilize'
    sha256sum "$checkpoint" >"$run_dir/checkpoint.sha256"
    sha256sum "$run_dir/base.log" >"$run_dir/base-log.sha256"
    sha256sum "$base_dir/checkpoint.sha256" "${fragments[@]}" \
      "$run_dir/setup.ml" "$repo_dir/candle/build_analytic_checker_checkpoint.sh" \
      "$repo_dir/candle/restart_real_functions_with_fragments.sh" \
      >"$run_dir/input-files.sha256"
    printf 'input_ack=%s\nready_marker=%s\nack_line=%s\nready_line=%s\ncheckpoint_sha256=%s\ncreated_utc=%s\n' \
      "$input_ack" "$ready_marker" "$ack_line" "$ready_line" \
      "$(sha256sum "$checkpoint" | awk '{print $1}')" \
      "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >"$run_dir/checkpoint-seal.receipt"
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
    printf '%s\n' CANDLE_NL_ANALYTIC_CHECKER_CHECKPOINT_OK
    exit 0
  fi
  kill -0 "$runtime_pid" 2>/dev/null ||
    fail 'runtime exited before analytic-checker readiness'
  sleep 1
done
