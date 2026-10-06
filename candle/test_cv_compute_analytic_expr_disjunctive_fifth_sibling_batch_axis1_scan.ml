(* Test axis 1 for every fixed-nonlinear rejection in the fifth batch. *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_scan.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_split_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_axis1_scan = struct

open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_split_scan;;
open Test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_scan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_scan;;

let candle_disjunctive_fifth_batch_axis1_candidates_get,
    candle_disjunctive_fifth_batch_axis1_rejected_get,
    candle_disjunctive_fifth_batch_axis1_selected_get,
    candle_disjunctive_fifth_batch_axis1_unsolved_get =
  let source_rejected = candle_disjunctive_fifth_batch_rejected_get () in
  let candidates =
    List.flatten
      (map
        (fun (record,index,selected,domain) ->
          candle_disjunctive_next_batch_split_axis1
            record index selected domain)
        source_rejected) in
  let function0 =
    List.filter (fun (_,_,selected,_,_,_) -> selected = 0) candidates
  and function1 =
    List.filter (fun (_,_,selected,_,_,_) -> selected = 1) candidates in
  let scan_cells point_plan selected =
    map
      (fun (_,_,_,domain) ->
        candle_disjunctive_next_batch_scan_cell point_plan domain)
      (candle_disjunctive_next_batch_split_jobs selected) in
  let axioms_before = axioms () in
  let count0,failures0 =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_scan_six
      "fifth-sibling-batch-function0-axis1-fixed-nonlinear-scan"
      candle_disjunctive_next_batch_prepared0
      (scan_cells candle_disjunctive_next_batch_point_plan0 function0) in
  let count1,failures1 =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_scan_six
      "fifth-sibling-batch-function1-axis1-fixed-nonlinear-scan"
      candle_disjunctive_next_batch_prepared1
      (scan_cells candle_disjunctive_next_batch_point_plan1 function1) in
  let rejected =
    candle_disjunctive_next_batch_select_failures 0 failures0 function0 @
    candle_disjunctive_next_batch_select_failures 0 failures1 function1 in
  let child_failed record index selected side =
    List.exists
      (fun (actual_record,actual_index,actual_selected,actual_axis,
            actual_side,_) ->
        actual_record = record && actual_index = index &&
        actual_selected = selected && actual_axis = 1 &&
        actual_side = side)
      rejected in
  let rec select = function
    | [] -> [],[]
    | (record,index,selected,_)::remaining ->
        let choices,unsolved = select remaining in
        if not (child_failed record index selected 0) &&
           not (child_failed record index selected 1)
        then (record,index,selected,1)::choices,unsolved
        else choices,(record,index,selected)::unsolved in
  let selected,unsolved = select source_rejected in
  let expected = 2 * length source_rejected in
  let axioms_after = axioms () in
  if length candidates <> expected ||
     count0 <> length function0 || count1 <> length function1 ||
     count0 + count1 <> expected ||
     length selected + length unsolved <> length source_rejected ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before) axioms_after) then
    failwith "fifth sibling batch axis1 fixed nonlinear scan: validation failed";
  print_endline
    ("CANDLE_CV_FIFTH_SIBLING_BATCH_AXIS1_FIXED_NONLINEAR_SCAN_OK" ^
     " DEVELOPMENT_NON_RELEASE" ^
     " rejected_source_leaves=" ^ string_of_int (length source_rejected) ^
     " candidate_children=" ^ string_of_int expected ^
     " rejected_children=" ^ string_of_int (length rejected) ^
     " selected_splits=" ^
     candle_disjunctive_next_batch_split_selection_string selected ^
     " unsolved=" ^
     candle_disjunctive_next_batch_split_unsolved_string unsolved ^
     " assumptions=0 axiom_growth=0");
  (fun () -> candidates),
  (fun () -> rejected),
  (fun () -> selected),
  (fun () -> unsolved);;

end;;
