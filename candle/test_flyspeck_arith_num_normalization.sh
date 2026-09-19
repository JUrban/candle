#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
flyspeck_root=${FLYSPECK_ROOT:-/project/worktrees/flyspeck-v13-source}
fixture="$candle_root/candle/compatibility/fixtures/arith_num_hashtbl_annotation_ocaml_oracle.ml"
test_dir=$(mktemp -d /tmp/candle-flyspeck-arith-num.XXXXXX)
cleanup() {
  chmod -R u+w "$test_dir" 2>/dev/null || true
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

python3 "$candle_root/candle/flyspeck_normalize.py" \
  --flyspeck-root "$flyspeck_root" --write "$test_dir/overlay"

normalized="$test_dir/overlay/formal_ineqs/arith/arith_num.hl"
test -f "$normalized"
rg -Fxq 'let def_table : (string, thm) Hashtbl.t = Hashtbl.create maximum;;' \
  "$normalized"
rg -Fxq 'let def_basic_table : (string, thm) Hashtbl.t = Hashtbl.create maximum;;' \
  "$normalized"
if [[ $(rg -c '^let [A-Za-z0-9_]+ : .+ Hashtbl\.t = Hashtbl\.create' \
          "$normalized") -ne 21 ]]; then
  echo 'normalized arith_num does not contain exactly 21 annotated tables' >&2
  exit 1
fi
if rg -q '^let [A-Za-z0-9_]+ = Hashtbl\.create' "$normalized"; then
  echo 'normalized arith_num retained an unannotated theorem table' >&2
  exit 1
fi
if [[ $(rg -c '^for i = ' "$normalized") -ne 24 ]]; then
  echo 'normalized arith_num does not retain exactly 24 outer for loops' >&2
  exit 1
fi
if rg -q '^let _ = for i = ' "$normalized"; then
  echo 'normalized arith_num retained an obsolete per-file loop binding' >&2
  exit 1
fi

ocaml -noinit -noprompt <"$fixture" >"$test_dir/ocaml.log" 2>&1
rg -Fq 'ARITH_NUM_HASHTBL_ANNOTATION_OCAML_ORACLE_OK' "$test_dir/ocaml.log"

printf 'PASS: arith_num value restriction and central loop lowering contract\n'
