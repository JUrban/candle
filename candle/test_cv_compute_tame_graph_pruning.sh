#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
test_dir=$(mktemp -d /tmp/candle-tame-graph-pruning.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    tail -n 200 "$test_dir/candle.log" >&2 2>/dev/null || true
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\nload_path := "%s" :: !load_path;;\nneeds "candle/test_cv_compute_tame_graph_pruning.ml";;\n' \
    "$candle_root" |
    timeout 1800 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

marker='CANDLE_CV_TAME_GRAPH_PRUNING_TEST_OK seed_retained=true degree7_retained=true degree8_rejected=true exceptional_degree7_rejected=true vertex16_rejected=true filter_order=exact axiom_growth=0 DEVELOPMENT_NON_RELEASE'
rg -Fq "$marker" "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed|Undefined variable:' \
  "$test_dir/candle.log"; then
  exit 1
fi

if [[ -n ${CANDLE_TEST_LOG:-} ]]; then
  cp "$test_dir/candle.log" "$CANDLE_TEST_LOG"
fi
rg -F "$marker" "$test_dir/candle.log"
printf 'PASS: exact AFP notame reflected predicate\n'
