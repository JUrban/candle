#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
flyspeck_root=${FLYSPECK_ROOT:-/project/worktrees/flyspeck-v13-source}
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-misc-functions.XXXXXX)
cleanup() {
  chmod -R u+w "$test_dir" 2>/dev/null || true
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

python3 "$candle_root/candle/flyspeck_normalize.py" \
  --flyspeck-root "$flyspeck_root" --write "$test_dir/overlay"

normalized="$test_dir/overlay/formal_ineqs/misc/misc_functions.hl"
test -f "$normalized"
rg -Fq 'Misc_functions.error_fmt formatting is unavailable' "$normalized"
rg -Fq 'for i = 1 to n - 1 do' "$normalized"
if rg -Fq 'sprintf str fmt' "$normalized" ||
   rg -Fq 'let rec repeat i =' "$normalized"; then
  echo 'misc_functions normalization contract drifted' >&2
  exit 1
fi

ocaml -noinit -noprompt \
  <"$fixture_root/misc_functions_test_loop_ocaml_oracle.ml" \
  >"$test_dir/ocaml.log" 2>&1
rg -Fq 'MISC_FUNCTIONS_TEST_LOOP_OCAML_ORACLE_OK' "$test_dir/ocaml.log"

printf 'PASS: misc_functions formatting normalization and native loop oracle\n'
