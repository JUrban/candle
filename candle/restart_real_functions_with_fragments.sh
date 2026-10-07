#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 3 ]]; then
  printf 'usage: %s OUTPUT_DIR EXPECTED_MARKER FRAGMENT...\n' "$0" >&2
  exit 2
fi

base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-real-functions-checkpoint-v1}
input_relocation_from=${CANDLE_FRAGMENT_INPUT_RELOCATION_FROM:-}
input_relocation_to=${CANDLE_FRAGMENT_INPUT_RELOCATION_TO:-}
extra_load_path=${CANDLE_FRAGMENT_EXTRA_LOAD_PATH:-}
output_dir=$1
expected_marker=$2
shift 2
fragments=("$@")

if [[ -n "$input_relocation_from" || -n "$input_relocation_to" ]]; then
  [[ -n "$input_relocation_from" && -n "$input_relocation_to" ]]
  [[ "$input_relocation_from" = /* && "$input_relocation_to" = /* ]]
  [[ -d "$input_relocation_to" ]]
fi
if [[ -n "$extra_load_path" ]]; then
  [[ "$extra_load_path" = /* ]]
  [[ "$extra_load_path" =~ ^/[A-Za-z0-9._/-]+$ ]]
  [[ -d "$extra_load_path" ]]
fi

[[ -f "$base_dir/CHECKPOINT-READY" ]]
[[ ! -f "$base_dir/CHECKPOINT-FAILED" ]]
[[ ! -e "$output_dir" ]]
for fragment in "${fragments[@]}"; do
  [[ -f "$fragment" ]]
done

fragment_set_sha256=$(
  sha256sum "${fragments[@]}" | sha256sum | awk '{print $1}'
)
input_nonce=$(
  printf '%s\n%s\n%s\n' "$output_dir" "$expected_marker" \
    "$fragment_set_sha256" | sha256sum | awk '{print $1}'
)
input_ack="CANDLE_RESTORE_INPUT_ACK nonce=$input_nonce"

exec 9>"$base_dir/restart.lock"
flock 9

mkdir -p "$output_dir/dmtcp-tmp" "$output_dir/checkpoint"
mapfile -t checkpoints < <(
  find "$base_dir/checkpoint" -maxdepth 1 -type f -name 'ckpt_*.dmtcp' -print
)
[[ ${#checkpoints[@]} -eq 1 ]]
sha256sum -c "$base_dir/checkpoint.sha256"
sha256sum -c "$base_dir/base-log.sha256"
: >"$output_dir/input-files.resolved.tsv"
while read -r expected path; do
  overlaid=0
  for fragment in "${fragments[@]}"; do
    if [[ "$path" == "$fragment" ]]; then overlaid=1; break; fi
  done
  if [[ "$overlaid" -eq 0 ]]; then
    resolved_path=$path
    if [[ -n "$input_relocation_from" &&
          "$path" == "$input_relocation_from"/* ]]; then
      relocated_path="$input_relocation_to/${path#"$input_relocation_from"/}"
      if [[ -f "$relocated_path" ]]; then resolved_path=$relocated_path; fi
    fi
    printf '%s  %s\n' "$expected" "$resolved_path" | sha256sum -c -
    printf '%s\t%s\t%s\n' "$expected" "$path" "$resolved_path" \
      >>"$output_dir/input-files.resolved.tsv"
  fi
done <"$base_dir/input-files.sha256"

skip_needs=$'candle/cv_compute_polynomial_expr_dim_jet_prove.ml\n'
skip_all_needs=${CANDLE_FRAGMENT_SKIP_ALL_NEEDS:-0}
[[ "$skip_all_needs" == 0 || "$skip_all_needs" == 1 ]]
for fragment in "${fragments[@]}"; do
  if [[ $(basename "$(dirname "$fragment")") == candle ]]; then
    skip_needs+="candle/$(basename "$fragment")"$'\n'
  fi
done

{
  printf 'print_endline "%s";;\n' "$input_ack"
  printf 'load_path := ["/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6/formal_ineqs"; "/project/worktrees/candle-cv-nonlinear-whole-box-v1"] @ !load_path;;\n'
  if [[ -n "$extra_load_path" ]]; then
    printf 'load_path := "%s" :: !load_path;;\n' "$extra_load_path"
  fi
  for fragment in "${fragments[@]}"; do
    fragment_sha256=$(sha256sum "$fragment" | awk '{print $1}')
    printf 'print_endline "CANDLE_RESTORE_FRAGMENT_BEGIN sha256=%s file=%s";;\n' \
      "$fragment_sha256" "$(basename "$fragment")"
    awk -v skip_needs="$skip_needs" -v skip_all_needs="$skip_all_needs" '
      BEGIN {
        count = split(skip_needs, paths, "\n")
        for (i = 1; i <= count; i++) if (paths[i] != "") skip[paths[i]] = 1
      }
      {
        sub(/\r$/, "")
        candidate = $0
        if (candidate ~ /^needs "[^"]+";;$/) {
          sub(/^needs "/, "", candidate)
          sub(/";;$/, "", candidate)
          if (skip_all_needs == 1 || candidate in skip) next
        }
        print
      }
    ' "$fragment"
    printf 'print_endline "CANDLE_RESTORE_FRAGMENT_END sha256=%s file=%s";;\n' \
      "$fragment_sha256" "$(basename "$fragment")"
  done
} >"$output_dir/stdin.ml"

sha256sum "${fragments[@]}" >"$output_dir/fragments.sha256"
printf 'nonce=%s\nfragment_set_sha256=%s\nstarted_utc=%s\n' \
  "$input_nonce" "$fragment_set_sha256" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  >"$output_dir/input-ack.started"

restart_pid=
cleanup() {
  if [[ -n "$restart_pid" ]]; then kill "$restart_pid" 2>/dev/null || true; fi
}
trap cleanup EXIT

env -i PATH=/project/bin:/usr/local/bin:/usr/bin:/bin LC_ALL=C \
  DMTCP_TMPDIR="$output_dir/dmtcp-tmp" \
  timeout 43200 dmtcp_restart --new-coordinator --coord-port 0 \
    --port-file "$output_dir/coord.port" \
    --ckptdir "$output_dir/checkpoint" "${checkpoints[0]}" \
    <"$output_dir/stdin.ml" >"$output_dir/candle.log" 2>&1 &
restart_pid=$!

ack_seen=0
for _ in $(seq 1 600); do
  if [[ -f "$output_dir/candle.log" ]] &&
     rg -Fq "$input_ack" "$output_dir/candle.log"; then
    ack_seen=1
    break
  fi
  if ! kill -0 "$restart_pid" 2>/dev/null; then break; fi
  sleep 0.2
done
if [[ "$ack_seen" -ne 1 ]]; then
  printf 'restored process did not acknowledge fresh input within 120 seconds\n' >&2
  tail -200 "$output_dir/candle.log" >&2 || true
  exit 1
fi

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
  first_error_line=$(
    rg -n -m1 'ERROR:|EXCEPTION:|Parsing failed' "$output_dir/candle.log" |
      cut -d: -f1
  )
  printf 'restored proof input reported its first source error at line %s\n' \
    "$first_error_line" >&2
  head -n "$first_error_line" "$output_dir/candle.log" | tail -300 >&2
  exit 1
fi
if [[ "$restart_status" -ne 0 ]]; then
  printf 'DMTCP restart failed with status %s\n' "$restart_status" >&2
  exit "$restart_status"
fi

ack_count=$(rg -Foc "$input_ack" "$output_dir/candle.log")
[[ "$ack_count" -eq 1 ]]
ack_line=$(rg -Fn -m1 "$input_ack" "$output_dir/candle.log" | cut -d: -f1)
if ! rg -Fq "$expected_marker" "$output_dir/candle.log"; then
  printf 'expected post-restore marker was not emitted: %s\n' \
    "$expected_marker" >&2
  tail -800 "$output_dir/candle.log" >&2
  exit 1
fi
marker_line=$(rg -Fn -m1 "$expected_marker" "$output_dir/candle.log" | cut -d: -f1)
[[ "$marker_line" -gt "$ack_line" ]]
printf 'nonce=%s\nfragment_set_sha256=%s\nack_line=%s\nmarker_line=%s\ncompleted_utc=%s\n' \
  "$input_nonce" "$fragment_set_sha256" "$ack_line" "$marker_line" \
  "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >"$output_dir/input-ack.receipt"
sha256sum "$output_dir/fragments.sha256" "$output_dir/stdin.ml" \
  "$output_dir/input-files.resolved.tsv" "$output_dir/candle.log" \
  >"$output_dir/result-files.sha256"
printf '%s\n' 'CANDLE_REAL_FUNCTIONS_FRAGMENT_RESTART_OK'
