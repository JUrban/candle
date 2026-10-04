(* Test axis 1 first for every rejected leaf in the fourth sibling batch. *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_scan.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_split_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_axis1_scan = struct

open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_split_scan;;
open Test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_scan;;

let candle_disjunctive_fourth_batch_axis1_candidates =
  List.flatten
    (map
      (fun (record,index,selected,domain) ->
        candle_disjunctive_next_batch_split_axis1
          record index selected domain)
      candle_disjunctive_fourth_batch_rejected);;
let candle_disjunctive_fourth_batch_axis1_function0 =
  List.filter
    (fun (_,_,selected,_,_,_) -> selected = 0)
    candle_disjunctive_fourth_batch_axis1_candidates;;
let candle_disjunctive_fourth_batch_axis1_function1 =
  List.filter
    (fun (_,_,selected,_,_,_) -> selected = 1)
    candle_disjunctive_fourth_batch_axis1_candidates;;

let candle_disjunctive_fourth_batch_axis1_axioms_before = axioms ();;
let candle_disjunctive_fourth_batch_axis1_scan_failures
    label prepared point_plan candidates =
  if candidates = [] then []
  else
    snd
      (candle_disjunctive_next_batch_scan_run label prepared point_plan
        (candle_disjunctive_next_batch_split_jobs candidates));;
let candle_disjunctive_fourth_batch_axis1_function0_failures =
  candle_disjunctive_fourth_batch_axis1_scan_failures
    "fourth-sibling-batch-function0-axis1-scan"
    candle_disjunctive_next_batch_prepared0
    candle_disjunctive_next_batch_point_plan0
    candle_disjunctive_fourth_batch_axis1_function0;;
let candle_disjunctive_fourth_batch_axis1_function1_failures =
  candle_disjunctive_fourth_batch_axis1_scan_failures
    "fourth-sibling-batch-function1-axis1-scan"
    candle_disjunctive_next_batch_prepared1
    candle_disjunctive_next_batch_point_plan1
    candle_disjunctive_fourth_batch_axis1_function1;;

let candle_disjunctive_fourth_batch_axis1_rejected =
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_fourth_batch_axis1_function0_failures
    candle_disjunctive_fourth_batch_axis1_function0 @
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_fourth_batch_axis1_function1_failures
    candle_disjunctive_fourth_batch_axis1_function1;;

let candle_disjunctive_fourth_batch_axis1_child_failed
    record index selected side =
  List.exists
    (fun (actual_record,actual_index,actual_selected,actual_axis,
          actual_side,_) ->
      actual_record = record && actual_index = index &&
      actual_selected = selected && actual_axis = 1 && actual_side = side)
    candle_disjunctive_fourth_batch_axis1_rejected;;

let rec candle_disjunctive_fourth_batch_axis1_select = function
  | [] -> [],[]
  | (record,index,selected,_)::remaining ->
      let choices,unsolved =
        candle_disjunctive_fourth_batch_axis1_select remaining in
      if
        not
          (candle_disjunctive_fourth_batch_axis1_child_failed
            record index selected 0) &&
        not
          (candle_disjunctive_fourth_batch_axis1_child_failed
            record index selected 1)
      then (record,index,selected,1)::choices,unsolved
      else choices,(record,index,selected)::unsolved;;

let candle_disjunctive_fourth_batch_axis1_selected,
    candle_disjunctive_fourth_batch_axis1_unsolved =
  candle_disjunctive_fourth_batch_axis1_select
    candle_disjunctive_fourth_batch_rejected;;

let candle_disjunctive_fourth_batch_axis1_axioms_after = axioms ();;
let candle_disjunctive_fourth_batch_axis1_expected =
  2 * length candle_disjunctive_fourth_batch_rejected;;

if length candle_disjunctive_fourth_batch_axis1_candidates <>
     candle_disjunctive_fourth_batch_axis1_expected ||
   length candle_disjunctive_fourth_batch_axis1_function0 +
     length candle_disjunctive_fourth_batch_axis1_function1 <>
     candle_disjunctive_fourth_batch_axis1_expected ||
   length candle_disjunctive_fourth_batch_axis1_selected +
     length candle_disjunctive_fourth_batch_axis1_unsolved <>
     length candle_disjunctive_fourth_batch_rejected ||
   length candle_disjunctive_fourth_batch_axis1_axioms_after <>
     length candle_disjunctive_fourth_batch_axis1_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_fourth_batch_axis1_axioms_before)
       candle_disjunctive_fourth_batch_axis1_axioms_after) then
  failwith "fourth sibling batch axis1 scan: validation failed";;

print_endline
  ("CANDLE_CV_FOURTH_SIBLING_BATCH_AXIS1_SCAN_OK DEVELOPMENT_NON_RELEASE" ^
   " rejected_source_leaves=" ^
   string_of_int (length candle_disjunctive_fourth_batch_rejected) ^
   " candidate_children=" ^
   string_of_int candle_disjunctive_fourth_batch_axis1_expected ^
   " rejected_children=" ^
   string_of_int (length candle_disjunctive_fourth_batch_axis1_rejected) ^
   " selected_splits=" ^
   candle_disjunctive_next_batch_split_selection_string
     candle_disjunctive_fourth_batch_axis1_selected ^
   " unsolved=" ^
   candle_disjunctive_next_batch_split_unsolved_string
     candle_disjunctive_fourth_batch_axis1_unsolved ^
   " assumptions=0 axiom_growth=0");;

end;;
