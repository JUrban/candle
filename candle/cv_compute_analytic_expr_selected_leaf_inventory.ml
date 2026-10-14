(* ========================================================================== *)
(* Explicit selected Iarg-leaf weights for direct Flyspeck NL source IDs.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Iarg_facet carries a serialized terminal      *)
(* record as well as a residual tree, so [count_iargs] measures all 23,242   *)
(* parameter records.  The production reconstruction counter instead visits  *)
(* explicit Iarg_leaf constructors.  This mirrors that exact recursion.       *)
(* ========================================================================== *)

module Candle_cv_analytic_expr_selected_leaf_inventory = struct

let rec candle_nl_explicit_iarg_leaf_count = function
  | Iarg_leaf _ -> 1
  | Iarg_bisect (_,left,right) ->
      candle_nl_explicit_iarg_leaf_count left +
      candle_nl_explicit_iarg_leaf_count right
  | Iarg_facet (_,_,_,residual) ->
      candle_nl_explicit_iarg_leaf_count residual;;

let candle_nl_selected_leaf_total = ref 0;;

let candle_nl_selected_leaf_emit source_id =
  let count =
    candle_nl_explicit_iarg_leaf_count
      (Break_case_exec.get_iarg source_id) in
  candle_nl_selected_leaf_total := !candle_nl_selected_leaf_total + count;
  print_endline
    ("CANDLE_NL_SELECTED_LEAF_COUNT DEVELOPMENT_NON_RELEASE" ^
     " source_id=" ^ source_id ^
     " selected_leaves=" ^ string_of_int count);;

let _ =
  do_list candle_nl_selected_leaf_emit Break_case_exec.all_idv;;

if !candle_nl_selected_leaf_total <> 7814 then
  failwith "NL selected-leaf inventory: total drift";;

print_endline
  ("CANDLE_NL_SELECTED_LEAF_SUMMARY DEVELOPMENT_NON_RELEASE" ^
   " source_ids=" ^ string_of_int (length Break_case_exec.all_idv) ^
   " selected_leaves=" ^ string_of_int !candle_nl_selected_leaf_total);;

end;;
