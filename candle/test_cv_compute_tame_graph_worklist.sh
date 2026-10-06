#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
test_dir=$(mktemp -d /tmp/candle-tame-graph-worklist.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ -n ${CANDLE_TEST_LOG:-} && -f "$test_dir/candle.log" ]]; then
    cp "$test_dir/candle.log" "$CANDLE_TEST_LOG"
  fi
  if [[ $status != 0 ]]; then
    tail -n 320 "$test_dir/candle.log" >&2 2>/dev/null || true
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\nload_path := "%s" :: !load_path;;\nneeds "candle/test_cv_compute_tame_graph_worklist.ml";;\n' \
    "$candle_root" |
    timeout 1800 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

marker='CANDLE_CV_TAME_GRAPH_WORKLIST_TEST_OK fuel0_preserves_frontier=true fuel1_visited=1 fuel1_stage0_children=2 fuel1_retained=1 fuel1_final_pruned=1 fuel1_maximum_frontier=1 exact_state=true axiom_growth=0 DEVELOPMENT_NON_RELEASE'
rg -Fq "$marker" "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed|Undefined variable:' \
  "$test_dir/candle.log"; then
  exit 1
fi

rg -F "$marker" "$test_dir/candle.log"
printf 'PASS: deterministic reflected AFP worklist state\n'
