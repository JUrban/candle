#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 4 ]]; then
  printf 'usage: %s BASE_DIR RUN_DIR READY_MARKER SETUP_FILE...\n' "$0" >&2
  exit 2
fi

base_dir=$1
run_dir=$2
ready_marker=$3
shift 3
setup_files=("$@")
script_path=$(realpath "$0")

[[ -f "$base_dir/CHECKPOINT-READY" ]]
[[ ! -f "$base_dir/CHECKPOINT-FAILED" ]]
for setup_file in "${setup_files[@]}"; do [[ -f "$setup_file" ]]; done
[[ ! -e "$run_dir" ]]
mapfile -t source_checkpoints < <(
  find "$base_dir/checkpoint" -maxdepth 1 -type f -name 'ckpt_*.dmtcp' -print
)
[[ ${#source_checkpoints[@]} -eq 1 ]]
sha256sum -c "$base_dir/checkpoint.sha256"
sha256sum -c "$base_dir/base-log.sha256"
sha256sum -c "$base_dir/input-files.sha256"

setup_set_sha256=$(
  sha256sum "${setup_files[@]}" | sha256sum | awk '{print $1}'
)
input_nonce=$(
  printf '%s\n%s\n%s\n' "$run_dir" "$ready_marker" "$setup_set_sha256" |
    sha256sum | awk '{print $1}'
)
input_ack="CANDLE_CV_SETUP_CHECKPOINT_INPUT_ACK_${input_nonce:0:16}"

exec 9>"$base_dir/restart.lock"
flock 9

mkdir -p "$run_dir/checkpoint" "$run_dir/dmtcp-tmp"
{
  printf 'print_endline "%s";;\n' "$input_ack"
  for setup_file in "${setup_files[@]}"; do
    setup_sha256=$(sha256sum "$setup_file" | awk '{print $1}')
    printf 'print_endline "CANDLE_CV_SETUP_REPLAY_BEGIN sha256=%s file=%s";;\n' \
      "$setup_sha256" "$(basename "$(dirname "$setup_file")")/$(basename "$setup_file")"
    sed -n '1,$p' "$setup_file"
    printf 'print_endline "CANDLE_CV_SETUP_REPLAY_END sha256=%s file=%s";;\n' \
      "$setup_sha256" "$(basename "$(dirname "$setup_file")")/$(basename "$setup_file")"
  done
} >"$run_dir/stdin.ml"
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
  timeout 43200 dmtcp_restart --new-coordinator --coord-port 0 \
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
sed -n '1,$p' "$run_dir/stdin.ml" >"$run_dir/input.fifo"

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
    fail 'runtime reported a source error before setup readiness'
  fi
  ack_count=$(rg -Foc "$input_ack" "$run_dir/base.log" || true)
  ready_count=$(rg -Foc "$ready_marker" "$run_dir/base.log" || true)
  [[ "$ack_count" -le 1 ]] || fail 'setup acknowledgement repeated'
  [[ "$ready_count" -le 1 ]] || fail 'setup readiness repeated'
  if [[ "$ready_count" -eq 1 ]]; then
    [[ "$ack_count" -eq 1 ]] || fail 'fresh setup input was not acknowledged'
    ack_line=$(rg -Fn -m1 "$input_ack" "$run_dir/base.log" | cut -d: -f1)
    ready_line=$(rg -Fn -m1 "$ready_marker" "$run_dir/base.log" | cut -d: -f1)
    [[ "$ready_line" -gt "$ack_line" ]] ||
      fail 'setup readiness did not follow fresh-input acknowledgement'
    port=$(<"$run_dir/coord.port")
    dmtcp_command --port "$port" -bc >"$run_dir/dmtcp-checkpoint.log" 2>&1
    checkpoint=
    stable_size=
    stable_samples=0
    for _ in $(seq 1 900); do
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
        if [[ "$stable_samples" -ge 2 ]]; then
          checkpoint=${checkpoints[0]}
          break
        fi
      elif [[ ${#checkpoints[@]} -gt 1 ]]; then
        fail 'more than one completed setup checkpoint was produced'
      fi
      sleep 1
    done
    [[ -n "$checkpoint" ]] || fail 'setup checkpoint did not stabilize'
    if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$run_dir/base.log"; then
      fail 'runtime reported a source error while checkpointing setup state'
    fi
    sha256sum "$checkpoint" >"$run_dir/checkpoint.sha256"
    sha256sum "$run_dir/base.log" >"$run_dir/base-log.sha256"
    sha256sum "${source_checkpoints[0]}" "${setup_files[@]}" "$script_path" \
      "$run_dir/stdin.ml" >"$run_dir/input-files.sha256"
    {
      printf 'receipt_kind=cv-setup-checkpoint\n'
      printf 'release_evidence=false\n'
      printf 'input_ack=%s\n' "$input_ack"
      printf 'ready_marker=%s\n' "$ready_marker"
      printf 'ack_line=%s\n' "$ack_line"
      printf 'ready_line=%s\n' "$ready_line"
      printf 'setup_count=%s\n' "${#setup_files[@]}"
      printf 'setup_set_sha256=%s\n' "$setup_set_sha256"
      printf 'checkpoint_sha256=%s\n' "$(awk '{print $1}' "$run_dir/checkpoint.sha256")"
      printf 'created_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    } >"$run_dir/checkpoint-seal.receipt"
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
    printf '%s\n' CANDLE_CV_SETUP_CHECKPOINT_OK
    exit 0
  fi
  kill -0 "$runtime_pid" 2>/dev/null ||
    fail 'runtime exited before setup readiness'
  sleep 1
done
