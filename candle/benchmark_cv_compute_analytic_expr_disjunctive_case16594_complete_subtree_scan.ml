(* Discover self-contained genuine case-16594 subtrees of useful batch size.
   DEVELOPMENT / NON-RELEASE only. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_subtree_scan = struct

open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan;;

let rec candle_disjunctive_case16594_complete_subtree_scan_from start shape =
  match shape with
  | Candle_disjunctive_case16594_variable_axis_leaf _ -> 1,[]
  | Candle_disjunctive_case16594_variable_axis_node (axis,left,right) ->
      let left_count,left_candidates =
        candle_disjunctive_case16594_complete_subtree_scan_from start left in
      let right_count,right_candidates =
        candle_disjunctive_case16594_complete_subtree_scan_from
          (start + left_count) right in
      let count = left_count + right_count in
      let candidates = left_candidates @ right_candidates in
      if 12 <= count && count <= 20 then
        count,(start,count,axis) :: candidates
      else count,candidates;;

let rec candle_disjunctive_case16594_complete_subtree_scan_print = function
  | [] -> ()
  | (start,count,axis) :: remaining ->
      print_endline
        ("CANDLE_CV_CASE16594_COMPLETE_SUBTREE_CANDIDATE" ^
         " start=" ^ string_of_int start ^
         " cells=" ^ string_of_int count ^
         " root_axis=" ^ string_of_int axis);
      candle_disjunctive_case16594_complete_subtree_scan_print remaining;;

let _ =
  let count,candidates =
    candle_disjunctive_case16594_complete_subtree_scan_from 0
      (candle_disjunctive_case16594_variable_axis_plan ()) in
  if count <> 875 || candidates = [] then
    failwith "case16594 complete subtree scan: shape mismatch";
  candle_disjunctive_case16594_complete_subtree_scan_print candidates;
  print_endline
    ("CANDLE_CV_CASE16594_COMPLETE_SUBTREE_SCAN_OK DEVELOPMENT_NON_RELEASE" ^
     " total_cells=" ^ string_of_int count ^
     " candidates=" ^ string_of_int (length candidates));;

end;;
