#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
test_dir=$(mktemp -d /tmp/candle-tame-graph-successor-p0.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    printf '%s\n' '--- Candle tame p=0 successor log' >&2
    tail -n 200 "$test_dir/candle.log" >&2 2>/dev/null || true
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\nload_path := "%s" :: !load_path;;\nneeds "candle/test_cv_compute_tame_graph_successor_p0.ml";;\n' \
    "$candle_root" |
    timeout 1800 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

rg -Fq \
  'CANDLE_CV_TAME_P0_SUCCESSOR_TEST_OK enum=2 duplicate_pruned=0 retained=2 graph_identities=isabelle_exact child_vertex_counts=4,3 child_final_flags=0,1 axiom_growth=0 DEVELOPMENT_NON_RELEASE' \
  "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed|Undefined variable:' \
  "$test_dir/candle.log"; then
  exit 1
fi

if [[ -n ${CANDLE_TEST_LOG:-} ]]; then
  cp "$test_dir/candle.log" "$CANDLE_TEST_LOG"
fi
rg 'CANDLE_CV_TAME_P0_SUCCESSOR_(TIMING|TEST_OK)' "$test_dir/candle.log"
printf 'PASS: tame enumerator exact p=0 first successor batch\n'
