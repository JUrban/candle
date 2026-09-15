#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
flyspeck_root=${FLYSPECK_ROOT:-/project/worktrees/flyspeck-v13-source}
fixture="$candle_root/candle/compatibility/fixtures/arith_cache_hashtbl_annotation_ocaml_oracle.ml"
test_dir=$(mktemp -d /tmp/candle-flyspeck-arith-cache.XXXXXX)
cleanup() {
  chmod -R u+w "$test_dir" 2>/dev/null || true
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

python3 "$candle_root/candle/flyspeck_normalize.py" \
  --flyspeck-root "$flyspeck_root" --write "$test_dir/overlay"

normalized="$test_dir/overlay/formal_ineqs/arith/arith_cache.hl"
test -f "$normalized"
rg -Fq 'let le_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size and' \
  "$normalized"
rg -Fq 'sub_le_table : (string, thm * thm) Hashtbl.t = Hashtbl.create cache_size and' \
  "$normalized"
if [[ $(rg -c 'Hashtbl\.t = Hashtbl\.create cache_size' "$normalized") -ne 6 ]]; then
  echo 'normalized arith_cache does not contain exactly six annotated tables' >&2
  exit 1
fi
if rg -q '^[[:space:]]*(let )?[a-z_]+ = Hashtbl\.create cache_size' "$normalized"; then
  echo 'normalized arith_cache retained an unannotated theorem table' >&2
  exit 1
fi
if rg -Fq 'let clear = Hashtbl.clear' "$normalized"; then
  echo 'normalized arith_cache retained the monomorphized clear alias' >&2
  exit 1
fi
if [[ $(rg -c '^[[:space:]]*Hashtbl\.clear (le|add|sub|sub_le|mul|div)_table' \
          "$normalized") -ne 6 ]]; then
  echo 'normalized arith_cache does not contain the six direct clear calls' >&2
  exit 1
fi
if rg -q 'sprintf' "$normalized"; then
  echo 'normalized arith_cache retained unsupported sprintf formatting' >&2
  exit 1
fi
if [[ $(rg -o 'string_of_int' "$normalized" | wc -l) -ne 19 ]]; then
  echo 'normalized arith_cache does not preserve all 19 integer fields' >&2
  exit 1
fi
if rg -Fq 'let len = Hashtbl.length' "$normalized" ||
   [[ $(rg -o 'Hashtbl\.length (le|add|sub|sub_le|mul|div)_table' \
            "$normalized" | wc -l) -ne 6 ]]; then
  echo 'normalized arith_cache did not inline all six typed length calls' >&2
  exit 1
fi

ocaml -noinit -noprompt <"$fixture" >"$test_dir/ocaml.log" 2>&1
rg -Fq 'ARITH_CACHE_HASHTBL_ANNOTATION_OCAML_ORACLE_OK' "$test_dir/ocaml.log"

printf 'PASS: arith_cache theorem-table value-restriction normalization\n'
