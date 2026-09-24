#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 3 ]]; then
  printf 'usage: %s OUTPUT_DIR CONTINUATION EXPECTED_MARKER\n' "$0" >&2
  exit 2
fi

base_dir=/project/flyspeck-candle-runs/cv-nonlinear-reflected-driver-checkpoint-v1
output_dir=$1
continuation=$2
expected_marker=$3

[[ -f "$base_dir/CHECKPOINT-READY" ]]
[[ ! -f "$base_dir/CHECKPOINT-FAILED" ]]
[[ -f "$continuation" ]]
[[ ! -e "$output_dir" ]]
mapfile -t checkpoints < <(
  find "$base_dir/checkpoint" -maxdepth 1 -type f -name 'ckpt_*.dmtcp' -print
)
[[ ${#checkpoints[@]} -eq 1 ]]
sha256sum -c "$base_dir/checkpoint.sha256"
sha256sum -c "$base_dir/base-log.sha256"
sha256sum -c "$base_dir/input-files.sha256"

continuation_sha256=$(sha256sum "$continuation" | awk '{print $1}')
input_nonce=$(printf '%s\n%s\n' "$output_dir" "$continuation_sha256" |
  sha256sum | awk '{print $1}')
input_ack="CANDLE_RESTORE_INPUT_ACK nonce=$input_nonce"
mkdir -p "$output_dir/dmtcp-tmp" "$output_dir/checkpoint"
{
  printf 'print_endline "%s";;\n' "$input_ack"
  awk '
    /^load_path :=/ { skipping = 1; next }
    skipping && /!load_path;;$/ { skipping = 0; next }
    /^needs "candle\/cv_compute_flyspeck_nonlinear_driver.ml";;$/ { next }
    { print }
  ' "$continuation"
} >"$output_dir/stdin.ml"

restart_pid=
cleanup() {
  if [[ -n "$restart_pid" ]]; then kill "$restart_pid" 2>/dev/null || true; fi
}
trap cleanup EXIT
env -i PATH=/project/bin:/usr/local/bin:/usr/bin:/bin LC_ALL=C \
  DMTCP_TMPDIR="$output_dir/dmtcp-tmp" \
  timeout 43200 dmtcp_restart --new-coordinator --coord-port 0 \
    --port-file "$output_dir/coord.port" --ckptdir "$output_dir/checkpoint" \
    "${checkpoints[0]}" \
    <"$output_dir/stdin.ml" >"$output_dir/candle.log" 2>&1 &
restart_pid=$!

first_error_seen=0
while kill -0 "$restart_pid" 2>/dev/null; do
  if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$output_dir/candle.log"; then
    first_error_seen=1
    kill "$restart_pid" 2>/dev/null || true
    break
  fi
  sleep 0.2
done
set +e
wait "$restart_pid"
restart_status=$?
set -e
restart_pid=
if [[ "$first_error_seen" -eq 1 ]]; then
  first_error_line=$(rg -n -m1 'ERROR:|EXCEPTION:|Parsing failed' \
    "$output_dir/candle.log" | cut -d: -f1)
  printf 'restored proof input reported its first source error at line %s\n' \
    "$first_error_line" >&2
  head -n "$first_error_line" "$output_dir/candle.log" | tail -300 >&2
  exit 1
fi
[[ "$restart_status" -eq 0 ]]
ack_line=$(rg -Fn -m1 "$input_ack" "$output_dir/candle.log" | cut -d: -f1)
marker_line=$(rg -Fn -m1 "$expected_marker" "$output_dir/candle.log" | cut -d: -f1)
[[ "$marker_line" -gt "$ack_line" ]]
printf 'nonce=%s\ncontinuation_sha256=%s\nack_line=%s\nmarker_line=%s\ncompleted_utc=%s\n' \
  "$input_nonce" "$continuation_sha256" "$ack_line" "$marker_line" \
  "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >"$output_dir/input-ack.receipt"
sha256sum "$continuation" "$output_dir/stdin.ml" "$output_dir/candle.log" \
  >"$output_dir/result-files.sha256"
printf '%s\n' CANDLE_NL_REFLECTED_DRIVER_RESTART_OK
