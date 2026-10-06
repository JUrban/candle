#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
candle_support_root=${CANDLE_SUPPORT_ROOT:-"$candle_root"}
test_dir=$(mktemp -d /tmp/candle-cv-tame-graph-data.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    printf '%s\n' '--- Candle reflected tame-graph data log' >&2
    tail -n 200 "$test_dir/candle.log" >&2 2>/dev/null || true
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

(
  cd "$candle_runtime_cwd"
  printf 'Cakeml.loadPath := ["%s"; "%s"; Filename.currentDir];;\n#use "hol.ml";;\n#use "%s/candle/test_cv_compute_tame_graph_data.ml";;\n' \
    "$candle_root" "$candle_support_root" "$candle_root" |
    timeout 1800 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

for marker in \
  valid_graph valid_map empty_graph nonzero_graph_tail empty_face pair_vertex \
  vertex_out_of_range duplicate_face_vertex nonzero_map_tail \
  malformed_map_entry map_source_out_of_range duplicate_map_source \
  duplicate_map_target; do
  rg -Fq "CANDLE_CV_TAME_GRAPH_DATA_CASE_OK:$marker" "$test_dir/candle.log"
done
rg -Fq 'CANDLE_CV_TAME_GRAPH_DATA_TEST_OK' "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed|Undefined variable:' \
  "$test_dir/candle.log"; then
  exit 1
fi

printf 'PASS: reflected tame-graph data boundary\n'
