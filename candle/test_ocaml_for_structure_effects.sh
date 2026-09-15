#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture="$candle_root/candle/compatibility/fixtures/ocaml_for_structure_effects.ml"
test_dir=$(mktemp -d /tmp/candle-ocaml-for-structure-effects.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

ocaml -noinit -noprompt <"$fixture" >"$test_dir/ocaml.log" 2>&1
rg -Fq 'CANDLE_OCAML_FOR_STRUCTURE_EFFECTS_OK' "$test_dir/ocaml.log"

(
  cd "$candle_runtime_cwd"
  timeout 300 "$candle_binary" --candle <"$fixture" \
    >"$test_dir/candle.log" 2>&1
)
rg -Fq 'CANDLE_OCAML_FOR_STRUCTURE_EFFECTS_OK' "$test_dir/candle.log"
rg -Fq 'val candle_ocaml_for_structure_effects_ok = true: bool' \
  "$test_dir/candle.log"
if rg -q 'Parsing failed|^ERROR:|^EXCEPTION:' "$test_dir/candle.log"; then
  tail -n 100 "$test_dir/candle.log" >&2
  exit 1
fi

printf 'PASS: OCaml for loops and discarded structure effects\n'
