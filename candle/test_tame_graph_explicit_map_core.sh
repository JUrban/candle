#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
test_dir=$(mktemp -d /tmp/candle-tame-graph-explicit-map-core.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    printf '%s\n' '--- Candle tame explicit-map core log' >&2
    tail -n 200 "$test_dir/candle.log" >&2 2>/dev/null || true
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\nload_path := "%s" :: !load_path;;\nneeds "candle/test_tame_graph_explicit_map_core.ml";;\n' \
    "$candle_root" |
    timeout 1800 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

rg -Fq \
  'CANDLE_TAME_GRAPH_EXPLICIT_MAP_CORE_TEST_OK assumptions=0 axiom_growth=0 DEVELOPMENT_NON_RELEASE' \
  "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed|Undefined variable:' \
  "$test_dir/candle.log"; then
  exit 1
fi

printf 'PASS: tame explicit-map core\n'
