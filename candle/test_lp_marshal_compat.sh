#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
flyspeck_root=${FLYSPECK_ROOT:-/project/worktrees/flyspeck-v13-source}
ocaml=${OCAML_414:-/project/repos/hol-light/_opam/bin/ocaml}
certificate="$flyspeck_root/formal_lp/glpk/binary/hard_2.dat"
test_dir=$(mktemp -d /tmp/candle-lp-marshal.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    for log in "$test_dir"/*.log; do
      [[ -f $log ]] || continue
      printf '%s\n' "--- ${log##*/}" >&2
      tail -n 120 "$log" >&2 || true
    done
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

test -f "$certificate"
rg -Fq 'module Candle_marshal = struct' "$candle_root/candle/ocaml.ml"
rg -Fq 'Candle_marshal.decode_channel' \
  "$candle_root/candle/flyspeck_normalizations.json"

python3 "$candle_root/candle/flyspeck_normalize.py" \
  --flyspeck-root "$flyspeck_root" --write "$test_dir/overlay" \
  >"$test_dir/normalize.log" 2>&1
normalized="$test_dir/overlay/formal_lp/hypermap/main/lp_certificate.hl"

"$ocaml" -noinit -noprompt \
  "$candle_root/candle/lp_marshal_native_oracle.ml" "$certificate" \
  >"$test_dir/native.log" 2>&1
native_summary=$(rg -o 'LP_MARSHAL_SUMMARY( [0-9]+){5}' \
  "$test_dir/native.log")
test -n "$native_summary"

(
  cd "$candle_runtime_cwd"
  printf 'Cakeml.loadPath := ["%s"; Filename.currentDir];;\n#use "hol.ml";;\n#use "%s";;\nopen Lp_certificate;;\nlet _ = let rec certificate_shape lp_case = match lp_case with Lp_terminal terminal -> (1,0,List.length terminal.constraints + List.length terminal.target_variables + List.length terminal.variable_bounds) | Lp_split (_,children) -> List.fold_left (fun (terminals,splits,constraints) child -> let child_terminals,child_splits,child_constraints = certificate_shape child in (terminals + child_terminals,splits + child_splits,constraints + child_constraints)) (0,1,0) children in let certificates = read_raw_lp_certificates "%s" in match certificates with [] -> failwith "empty LP decoder probe" | certificate::_ -> let terminals,splits,constraints = certificate_shape certificate.root_case in print_endline ("LP_MARSHAL_SUMMARY " ^ string_of_int (List.length certificates) ^ " " ^ string_of_int (String.length certificate.hypermap_string) ^ " " ^ string_of_int terminals ^ " " ^ string_of_int splits ^ " " ^ string_of_int constraints);;\nlet _ = let rejected = try let _ = Candle_marshal.decode_string "bad" in false with Failure _ -> true in if rejected then print_endline "LP_MARSHAL_FAIL_CLOSED_OK" else failwith "malformed Marshal input accepted";;\n' \
    "$candle_root" "$normalized" "$certificate" |
    timeout 600 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

candle_summary=$(rg -o 'LP_MARSHAL_SUMMARY( [0-9]+){5}' \
  "$test_dir/candle.log")
test "$candle_summary" = "$native_summary"
rg -Fq 'LP_MARSHAL_FAIL_CLOSED_OK' "$test_dir/candle.log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed|Undefined variable:' \
  "$test_dir/candle.log"; then
  exit 1
fi

printf 'PASS: bounded LP Marshal decoder matches native OCaml on a real shard\n'
