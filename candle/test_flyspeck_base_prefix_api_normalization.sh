#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
flyspeck_root=${FLYSPECK_ROOT:-${1:-}}
if [[ -z "$flyspeck_root" || ! -d "$flyspeck_root" ]]; then
  echo "usage: FLYSPECK_ROOT=/exact/source/root $0" >&2
  exit 1
fi
flyspeck_root=$(realpath -- "$flyspeck_root")
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-base-prefix-api.XXXXXX)
cleanup() {
  if [[ ${CANDLE_KEEP_TEST_OUTPUT:-0} = 1 ]]; then
    echo "preserved focused compatibility output: $test_dir" >&2
    return
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT
overlay="$test_dir/overlay"
cd "$candle_root"

python3 candle/flyspeck_normalize.py \
  --flyspeck-root "$flyspeck_root" --write "$overlay" \
  >"$test_dir/normalization.log"

strictbuild="$overlay/text_formalization/build/strictbuild.hl"
lib="$overlay/text_formalization/general/lib.hl"
flyspeck_lib="$overlay/text_formalization/general/flyspeck_lib.hl"
flyspeck_eval="$overlay/text_formalization/general/flyspeck_eval_4.14.hl"
sphere="$overlay/text_formalization/general/sphere.hl"
hales="$overlay/text_formalization/general/hales_tactic.hl"
truong="$overlay/text_formalization/general/truong_tactic.hl"
collect_geom="$overlay/text_formalization/leg/collect_geom.hl"
collect_geom2="$overlay/text_formalization/leg/collect_geom2.hl"
refinement="$overlay/text_formalization/jordan/refinement.hl"
lib_ext="$flyspeck_root/text_formalization/jordan/lib_ext.hl"
hash_term="$overlay/text_formalization/jordan/hash_term.hl"
goal_printer="$overlay/text_formalization/jordan/goal_printer.hl"
parse_ext="$flyspeck_root/text_formalization/jordan/parse_ext_override_interface.hl"
prove_refinement="$flyspeck_root/text_formalization/general/prove_by_refinement.hl"
tactics="$overlay/text_formalization/general/tactics.hl"
real_ext="$overlay/text_formalization/jordan/real_ext.hl"
tactics_jordan="$overlay/text_formalization/jordan/tactics_jordan.hl"
num_ext="$overlay/text_formalization/jordan/num_ext_nabs.hl"
taylor_atn="$overlay/text_formalization/jordan/taylor_atn.hl"
float_source="$overlay/text_formalization/jordan/float.hl"
misc_defs="$overlay/text_formalization/jordan/misc_defs_and_lemmas.hl"

rg -Fq 'dynamic strictbuild build_and_report is disabled by the static manifest' \
  "$strictbuild"
if rg -Fq 'open_out_gen' "$strictbuild"; then
  echo 'normalized strictbuild retained unsupported open_out_gen' >&2
  exit 1
fi
[[ $(rg -Fc 'let rev l =' "$lib") -eq 1 ]]
if rg -Fq 'let rev =' "$lib"; then
  echo 'normalized lib retained value-restricted rev binding' >&2
  exit 1
fi
for binding in length mapf foldl foldr applyd; do
  if rg -Fq "let $binding =" "$lib"; then
    echo "normalized lib retained value-restricted $binding binding" >&2
    exit 1
  fi
done
if rg -Fq 'let undefine =' "$lib"; then
  echo 'normalized lib retained value-restricted undefine binding' >&2
  exit 1
fi
if rg -Fq 'let (|->),combine =' "$lib"; then
  echo 'normalized lib retained value-restricted update/combine pair' >&2
  exit 1
fi
rg -Fq 'let undefine x t =' "$lib"
rg -Fq 'let (|->) x y t =' "$lib"
rg -Fq 'let combine op z t1 t2 =' "$lib"
[[ $(rg -Fc 'output_string outs a' "$flyspeck_lib") -eq 1 ]]
[[ $(rg -Fc 'needs "general/flyspeck_eval_4.14.hl";;' "$flyspeck_lib") -eq 1 ]]
if rg -Fq 'needs (String.concat "/"' "$flyspeck_lib"; then
  echo 'normalized flyspeck_lib retained dynamic needs expression' >&2
  exit 1
fi
if rg -Fq 'Printf.fprintf outs "%s" a' "$flyspeck_lib"; then
  echo 'normalized flyspeck_lib retained unavailable Printf.fprintf' >&2
  exit 1
fi
[[ $(rg -Fc 'sort Term.(<) (frees bod)' "$sphere") -eq 1 ]]
rg -Fq 'let _ = prioritize_real();;' "$sphere"
if rg -Fq 'sort (<) (frees bod)' "$sphere"; then
  echo 'normalized sphere retained implicit term comparison' >&2
  exit 1
fi
rg -Fq 'let _ = prioritize_real();;' "$collect_geom"
rg -Fq 'let _ = MESON[]` (!x y z.' "$collect_geom"
if rg '^MESON' "$collect_geom" | rg -Fq 'MESON[]` (!x y z.'; then
  echo 'normalized collect_geom retained anonymous MESON example' >&2
  exit 1
fi
rg -Fq 'let _ = MATCH_MP (SPEC_ALL AFFINE_HULL_FINITE)' "$collect_geom2"
rg -Fq 'let _ = MESON[POW_2_SQRT; DIST_POS_LE]' "$collect_geom2"
if rg -q '^MATCH_MP (SPEC_ALL AFFINE_HULL_FINITE)|^MESON\[POW_2_SQRT' \
    "$collect_geom2"; then
  echo 'normalized collect_geom2 retained an anonymous theorem example' >&2
  exit 1
fi
[[ $(rg -Fc 'List.concat' "$hales") -eq 2 ]]
[[ $(rg -Fc 'List.concat' "$truong") -eq 2 ]]
if rg -Fq 'List.flatten' "$hales" "$truong"; then
  echo 'normalized tactic source retained unavailable List.flatten' >&2
  exit 1
fi
[[ $(rg -Fc 'setify Term.(<)' "$hales") -eq 3 ]]
[[ $(rg -Fc 'setify Term.(<)' "$truong") -eq 3 ]]
[[ $(rg -Fc 'Pair.compare String.compare Term.compare' "$hales") -eq 1 ]]
[[ $(rg -Fc 'Pair.compare String.compare Term.compare' "$truong") -eq 1 ]]
rg -Fq 'let rec update_all i =' "$refinement"
if rg -Fq 'for i=0 to ((length asl)-1)' "$refinement"; then
  echo 'normalized refinement retained unsupported for loop' >&2
  exit 1
fi
rg -Fq 'Char.code (String.get h 0)' "$hash_term"
rg -Fq 'let name = "??_"^(string_of_int n) in' "$hash_term"
if rg -Fq 'int_of_char' "$hash_term"; then
  echo 'normalized hash_term retained unavailable int_of_char' >&2
  exit 1
fi
rg -Fq 'let _ = Parse_ext_override_interface.unambiguous_interface();;' \
  "$goal_printer"
rg -Fq 'let _ = Parse_ext_override_interface.prioritize_real();;' \
  "$goal_printer"
[[ $(rg -c '^open (Refinement|Hash_term|Lib_ext);;$' "$goal_printer") -eq 3 ]]
rg -Fq 'let _ = select_thm' "$tactics"
[[ $(rg -Fc 'let _ = REBIND_CONV' "$hales") -eq 1 ]]
[[ $(rg -Fc 'let _ = REBIND_RULE' "$hales") -eq 1 ]]
[[ $(rg -Fc 'let _ = REBIND_CONV' "$truong") -eq 1 ]]
[[ $(rg -Fc 'let _ = REBIND_RULE' "$truong") -eq 1 ]]
if rg -q '^select_thm$' "$tactics"; then
  echo 'normalized general tactics retained anonymous select example' >&2
  exit 1
fi
[[ $(rg -Fc 'let _ = unambiguous_interface();;' "$real_ext") -eq 1 ]]
[[ $(rg -Fc 'let _ = prioritize_num();;' "$real_ext") -eq 1 ]]
[[ $(rg -Fc 'let _ = pop_priority();;' "$real_ext") -eq 1 ]]
[[ $(rg -Fc 'let _ = Parse_ext_override_interface.unambiguous_interface();;' \
  "$tactics_jordan") -eq 1 ]]
rg -Fq 'let _ = select_thm' "$tactics_jordan"
rg -Fq 'let absname = "mk_"^s in' "$tactics_jordan"
rg -Fq 'let repname = "dest_"^s in' "$tactics_jordan"
rg -Fq '(absname,repname)' "$tactics_jordan"
[[ $(rg -Fc 'let _ = dropq_conv' "$tactics_jordan") -eq 3 ]]
if rg -Fq '("mk_"^s,"dest_"^s)' "$tactics_jordan"; then
  echo 'normalized tactics_jordan retained the inferred string tuple' >&2
  exit 1
fi
[[ $(rg -Fc 'let _ = Parse_ext_override_interface.unambiguous_interface();;' \
  "$num_ext") -eq 1 ]]
rg -Fq 'let _ = prioritize_complex();;' "$taylor_atn"
rg -Fq 'let _ = prioritize_real();;' "$taylor_atn"
rg -Fq 'let _ = Parse_ext_override_interface.unambiguous_interface();;' \
  "$float_source"
rg -Fq 'let _ = Parse_ext_override_interface.prioritize_real();;' \
  "$float_source"
rg -Fq 'let _ = test();;' "$float_source"
[[ $(rg -Fc 'let _ = add_test' "$float_source") -eq 24 ]]
rg -Fq '(*test*) let _ = let f (u,v)' "$float_source"
[[ $(rg -Fc 'Assert_failure' "$float_source") -eq 4 ]]
[[ $(rg -Fc 'let b = float_fabs f in' "$float_source") -eq 2 ]]
[[ $(rg -Fc 'if Cake.Double.(>=) f 0.0 then I else minus_num' \
  "$float_source") -eq 2 ]]
if rg -q '^add_test' "$float_source"; then
  echo 'normalized float retained an anonymous test call' >&2
  exit 1
fi
if rg -q '\bassert\s*\(' "$float_source"; then
  echo 'normalized float retained an unsupported assert expression' >&2
  exit 1
fi
rg -Fq 'let _ = unambiguous_interface();;' "$misc_defs"
rg -Fq 'let _ = pop_priority();;' "$misc_defs"
rg -Fq "SUBGOAL_MP_TAC \`?t. t = x+|y'\`;" "$misc_defs"
rg -Fq 'SPEC_TAC (`x:num`,`a:num`);' "$misc_defs"
if rg -Fq "SUBGOAL_MP_TAC \`?t. t = x'+|y'\`;" "$misc_defs"; then
  echo 'normalized misc_defs retained the unrelated renamed coordinate' >&2
  exit 1
fi
[[ $(rg -Fc "Digest.to_hex (Digest.file s')" "$strictbuild") -eq 3 ]]
rg -Fq 'let print_as l str =' "$candle_root/candle/ocaml.ml"
rg -Fq 'exception Assert_failure of (string * int * int);;' \
  "$candle_root/candle/ocaml.ml"
rg -Fq 'let ceil value = negfloat (floor (negfloat value));;' \
  "$candle_root/candle/ocaml.ml"
rg -Fq 'let ldexp value scale =' "$candle_root/candle/ocaml.ml"
rg -Fq 'let float_of_num n =' "$candle_root/candle/nums.ml"

if ! command -v ocaml >/dev/null; then
  echo 'OCaml is required for the structural compatibility oracles' >&2
  exit 1
fi
ocaml -noinit -noprompt \
  <"$fixture_root/flyspeck_boundary_compatibility_ocaml_oracle.ml" \
  >"$test_dir/boundary-ocaml.log" 2>&1
rg -Fq 'FLYSPECK_BOUNDARY_COMPATIBILITY_OCAML_ORACLE_OK' \
  "$test_dir/boundary-ocaml.log"
original_pair_oracle=$(
  {
    sed -n '518,521p' "$flyspeck_root/text_formalization/general/lib.hl"
    sed -n '657,746p' "$flyspeck_root/text_formalization/general/lib.hl"
    sed -n '1,200p' "$fixture_root/lib_pair_split_oracle_driver.ml"
  } | ocaml -noinit -noprompt 2>&1 | rg '^PAIR_SPLIT_ORACLE '
)
normalized_pair_oracle=$(
  {
    sed -n '518,521p' "$flyspeck_root/text_formalization/general/lib.hl"
    sed -n '1,300p' "$fixture_root/lib_pair_split_replacement.ml"
    sed -n '1,200p' "$fixture_root/lib_pair_split_oracle_driver.ml"
  } | ocaml -noinit -noprompt 2>&1 | rg '^PAIR_SPLIT_ORACLE '
)
if [[ "$original_pair_oracle" != "$normalized_pair_oracle" ]]; then
  echo 'original/split update/combine structural oracles differ' >&2
  exit 1
fi

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\nlet candle_focused_text_root = "%s";;\nlet candle_focused_eval_original = "%s";;\nload_path := candle_focused_text_root :: !load_path;;\nCakeml.configureSourceIdentities [(candle_focused_eval_original,("flyspeck_eval_4.14.hl","0f625ae4acb1fa69d4add5957e0ff308"))];;\nCakeml.configureNormalizationOverlay [(candle_focused_eval_original,"%s")];;\nneeds "general/flyspeck_eval_4.14.hl";;\nlet process_to_string unixstring =\n  let p = Unix.open_process_in unixstring\n  and b = Buffer.create 64 in\n  let rec read () = Buffer.add_channel b p 1; read () in\n    try read () with End_of_file -> (Unix.close_process_in p; Buffer.contents b);;\nlet dest_goal gl = gl;;\nlet mk_goal (asl,w) = (asl,w);;\nlet print_as l str = Pretty.print_stdout (fun state (length,string) -> Pretty_imp.print_as state length string) (l,str);;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\nlet prove_by_refinement = Prove_by_refinement.prove_by_refinement;;\n#use "%s";;\n' \
      "$flyspeck_root/text_formalization" \
      "$flyspeck_root/text_formalization/general/flyspeck_eval_4.14.hl" \
      "$flyspeck_eval" \
      "$flyspeck_lib" \
      "$fixture_root/base_prefix_api_original_sphere.ml" \
      "$fixture_root/base_prefix_api_original_flatten.ml" \
      "$fixture_root/base_prefix_api_original_printf.ml" \
      "$fixture_root/base_prefix_api_original_rev.ml" \
      "$fixture_root/base_prefix_api_original_rebind_structure.ml" \
      "$fixture_root/base_prefix_api_original_meson_structure.ml" \
      "$fixture_root/base_prefix_api_normalized.ml" \
      "$lib" \
      "$fixture_root/flyspeck_boundary_compatibility_normalized.ml" \
      "$refinement" \
      "$lib_ext" \
      "$hash_term" \
      "$parse_ext" \
      "$goal_printer" \
      "$prove_refinement" \
      "$tactics" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/candle.log" 2>&1
)

rg -Fq 'Type mismatch between int list -> int list and term list' \
  "$test_dir/candle.log"
rg -Fq 'Undefined variable: List.flatten' "$test_dir/candle.log"
rg -Fq 'Undefined variable: Printf.fprintf' "$test_dir/candle.log"
rg -Fq 'Value restriction violated' "$test_dir/candle.log"
rg -Fq 'Undefined variable: REBIND_CONV' "$test_dir/candle.log"
rg -Fq 'Type mismatch between thm and (thm list -> term -> thm)' \
  "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_normalized_all_forall = <fun>: term -> term' \
  "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_normalized_flatten_frees = <fun>: term list -> term list' \
  "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_normalized_output_filestring = <fun>: string -> string -> unit' \
  "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_build_and_report_fail_closed = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_base_prefix_api_oracle_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_normalized_meson_structure_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_boundary_compatibility_oracle_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq -- "- Already loaded: $flyspeck_root/text_formalization/general/flyspeck_eval_4.14.hl" \
  "$test_dir/candle.log"
rg -Fq -- "- Finished loading $flyspeck_lib" "$test_dir/candle.log"
rg -Fq -- "- Finished loading $lib" "$test_dir/candle.log"
rg -Fq -- "- Finished loading $refinement" "$test_dir/candle.log"
rg -Fq -- "- Finished loading $lib_ext" "$test_dir/candle.log"
rg -Fq -- "- Finished loading $hash_term" "$test_dir/candle.log"
rg -Fq -- "- Finished loading $parse_ext" "$test_dir/candle.log"
rg -Fq -- "- Finished loading $goal_printer" "$test_dir/candle.log"
rg -Fq -- "- Finished loading $prove_refinement" "$test_dir/candle.log"
rg -Fq -- "- Finished loading $tactics" "$test_dir/candle.log"
if [[ $(rg -c '^ERROR:' "$test_dir/candle.log") -ne 6 ]]; then
  tail -n 80 "$test_dir/candle.log" >&2
  exit 1
fi

printf 'PASS: exact Flyspeck base-prefix API normalizations\n'
