#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
test_dir=$(mktemp -d /tmp/candle-tame-graph-transition.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ -n ${CANDLE_TEST_LOG:-} && -f "$test_dir/candle.log" ]]; then
    cp "$test_dir/candle.log" "$CANDLE_TEST_LOG"
  fi
  if [[ $status != 0 ]]; then
    tail -n 300 "$test_dir/candle.log" >&2 2>/dev/null || true
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\nload_path := "%s" :: !load_path;;\nneeds "candle/test_cv_compute_tame_graph_transition.ml";;\n' \
    "$candle_root" |
    timeout 1800 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

marker='CANDLE_CV_TAME_GRAPH_TRANSITION_TEST_OK enum33=2 enum43=3 next_tame0_children=2 next_tame_children=1 final_pruned=1 complete_graph_identities=isabelle_exact axiom_growth=0 DEVELOPMENT_NON_RELEASE'
rg -Fq "$marker" "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed|Undefined variable:' \
  "$test_dir/candle.log"; then
  exit 1
fi

rg -F "$marker" "$test_dir/candle.log"
printf 'PASS: exact AFP runtime enumerator and composed next_tame transition\n'
