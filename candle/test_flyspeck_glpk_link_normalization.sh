#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
flyspeck_root=${FLYSPECK_ROOT:-/project/worktrees/flyspeck-v13-source}
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture="$candle_root/candle/compatibility/fixtures/glpk_fail_closed_sprintf_ocaml_oracle.ml"
test_dir=$(mktemp -d /tmp/candle-flyspeck-glpk-link.XXXXXX)
cleanup() {
  if [[ ${CANDLE_KEEP_TEST_OUTPUT:-0} = 1 ]]; then
    echo "preserved focused compatibility output: $test_dir" >&2
    return
  fi
  chmod -R u+w "$test_dir" 2>/dev/null || true
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

python3 "$candle_root/candle/flyspeck_normalize.py" \
  --flyspeck-root "$flyspeck_root" --write "$test_dir/overlay"

normalized="$test_dir/overlay/formal_lp/glpk/glpk_link.ml"
test -f "$normalized"
test "$(sha256sum -- "$normalized" | cut -d' ' -f1)" = \
  "6ffd1be47aa9039f41758794869d77484fe7ee85d4e304a9b944af3d3e3a2d45"
if rg -Fq 'Printf.sprintf' "$normalized"; then
  echo 'normalized glpk_link retained unsupported Printf.sprintf' >&2
  exit 1
fi
rg -Fq 'let sprintf _ =' "$normalized"
rg -Fq 'non-verification GLPK formatter is disabled' "$normalized"
if [[ $(rg -o 'sprintf' "$normalized" | wc -l) -ne 10 ]]; then
  echo 'normalized glpk_link changed a deferred formatter call site' >&2
  exit 1
fi
rg -Fq 'let convert_to_list3  =' "$normalized"
rg -Fq 'let convert_to_list = (fun (h,_,ls) -> (h,ls)) o convert_to_list3;;' \
  "$normalized"
rg -Fq \
  'wheremod [[0;1;2];[3;4;5];[7;8;9]] [8;9;7];;  (* 2 *)' \
  "$normalized"
rg -Fq 'let (ic,oc) = Unix.open_process(com) in' "$normalized"
rg -Fq 'let find_all f l = filter f l' "$candle_root/candle/ocaml.ml"
rg -Fq 'let flatten xss = concat xss' "$candle_root/candle/ocaml.ml"

ocaml -noinit -noprompt <"$fixture" >"$test_dir/ocaml.log" 2>&1
rg -Fq 'val candle_glpk_fail_closed_sprintf_ok : bool = true' \
  "$test_dir/ocaml.log"
rg -Fq 'val candle_glpk_list_find_all_ok : bool = true' \
  "$test_dir/ocaml.log"
rg -Fq 'val candle_glpk_list_flatten_ok : bool = true' \
  "$test_dir/ocaml.log"

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n' "$fixture" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/candle.log" 2>&1
)
rg -Fq 'val candle_glpk_fail_closed_sprintf_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'val candle_glpk_list_find_all_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'val candle_glpk_list_flatten_ok = true: bool' \
  "$test_dir/candle.log"
if rg -q 'Parsing failed|^ERROR:|^EXCEPTION:' "$test_dir/candle.log"; then
  tail -n 100 "$test_dir/candle.log" >&2
  exit 1
fi

printf 'PASS: glpk_link fail-closed Printf and List.find_all/List.flatten compatibility\n'
