#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture="$candle_root/candle/compatibility/fixtures/ocaml_for_structure_effects.ml"
nested_bare_fixture="$candle_root/candle/compatibility/fixtures/ocaml_for_nested_structure_effect_deferred.ml"
nested_wrapped_fixture="$candle_root/candle/compatibility/fixtures/ocaml_for_nested_structure_effect_wrapped_control.ml"
test_dir=$(mktemp -d /tmp/candle-ocaml-for-structure-effects.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

ocaml -noinit -noprompt <"$fixture" >"$test_dir/ocaml.log" 2>&1
rg -Fq 'val candle_ocaml_for_structure_effects_ok : bool = true' \
  "$test_dir/ocaml.log"

ocaml -noinit -noprompt <"$nested_bare_fixture" \
  >"$test_dir/ocaml-nested-bare.log" 2>&1
rg -Fq 'val candle_for_nested_structure_effect_expected : bool = true' \
  "$test_dir/ocaml-nested-bare.log"
ocaml -noinit -noprompt <"$nested_wrapped_fixture" \
  >"$test_dir/ocaml-nested-wrapped.log" 2>&1
rg -Fq 'val candle_for_nested_structure_effect_wrapped_expected : bool = true' \
  "$test_dir/ocaml-nested-wrapped.log"

(
  cd "$candle_runtime_cwd"
  timeout 300 "$candle_binary" --candle <"$fixture" \
    >"$test_dir/candle.log" 2>&1
)
rg -Fq 'val candle_ocaml_for_structure_effects_ok = true: bool' \
  "$test_dir/candle.log"
if rg -q 'Parsing failed|^ERROR:|^EXCEPTION:' "$test_dir/candle.log"; then
  tail -n 100 "$test_dir/candle.log" >&2
  exit 1
fi

# A nested-module `;;` is a module-item separator, not a top-level REPL phrase
# boundary.  The bare expression and explicit discarded-result binding must
# therefore preserve the same preceding structure bindings and final value.
(
  cd "$candle_runtime_cwd"
  timeout 300 "$candle_binary" --candle <"$nested_bare_fixture" \
    >"$test_dir/candle-nested-bare.log" 2>&1
)
rg -Fq 'val candle_for_nested_structure_effect_expected = true: bool' \
  "$test_dir/candle-nested-bare.log"
if rg -q 'Parsing failed|^ERROR:|^EXCEPTION:' \
    "$test_dir/candle-nested-bare.log"; then
  tail -n 100 "$test_dir/candle-nested-bare.log" >&2
  exit 1
fi

(
  cd "$candle_runtime_cwd"
  timeout 300 "$candle_binary" --candle <"$nested_wrapped_fixture" \
    >"$test_dir/candle-nested-wrapped.log" 2>&1
)
rg -Fq 'val candle_for_nested_structure_effect_wrapped_expected = true: bool' \
  "$test_dir/candle-nested-wrapped.log"
if rg -q 'Parsing failed|^ERROR:|^EXCEPTION:' \
    "$test_dir/candle-nested-wrapped.log"; then
  tail -n 100 "$test_dir/candle-nested-wrapped.log" >&2
  exit 1
fi

printf 'PASS: OCaml for loops and bare/wrapped nested-module effects\n'
