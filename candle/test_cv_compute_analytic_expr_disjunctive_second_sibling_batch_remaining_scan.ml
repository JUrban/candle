(* Try axes 2--6 only for second-batch leaves unresolved by axis 1. *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_second_sibling_batch_axis1_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_second_sibling_batch_remaining_scan = struct

open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_split_scan;;
open Test_cv_compute_analytic_expr_disjunctive_second_sibling_batch_scan;;
open Test_cv_compute_analytic_expr_disjunctive_second_sibling_batch_axis1_scan;;

let candle_disjunctive_second_batch_remaining_source
    record index selected =
  try
    List.find
      (fun (actual_record,actual_index,actual_selected,_) ->
        actual_record = record && actual_index = index &&
        actual_selected = selected)
      candle_disjunctive_second_batch_rejected
  with Not_found ->
    failwith "second sibling remaining scan: source leaf missing";;

let candle_disjunctive_second_batch_remaining_candidates_for
    record index selected =
  let _,_,_,domain =
    candle_disjunctive_second_batch_remaining_source
      record index selected in
  List.flatten
    (map
      (fun axis ->
        let left,right = M_verifier.split_domain 6 6 axis domain in
        [(record,index,selected,axis,0,left);
         (record,index,selected,axis,1,right)])
      [2;3;4;5;6]);;

let candle_disjunctive_second_batch_remaining_candidates =
  List.flatten
    (map
      (fun (record,index,selected) ->
        candle_disjunctive_second_batch_remaining_candidates_for
          record index selected)
      candle_disjunctive_second_batch_axis1_unsolved);;
let candle_disjunctive_second_batch_remaining_function0 =
  List.filter
    (fun (_,_,selected,_,_,_) -> selected = 0)
    candle_disjunctive_second_batch_remaining_candidates;;
let candle_disjunctive_second_batch_remaining_function1 =
  List.filter
    (fun (_,_,selected,_,_,_) -> selected = 1)
    candle_disjunctive_second_batch_remaining_candidates;;

let candle_disjunctive_second_batch_remaining_jobs candidates =
  map
    (fun (record,index,selected,_,_,domain) ->
      record,index,selected,domain)
    candidates;;

let candle_disjunctive_second_batch_remaining_scan_failures
    label prepared point_plan candidates =
  if candidates = [] then []
  else
    snd
      (candle_disjunctive_next_batch_scan_run label prepared point_plan
        (candle_disjunctive_second_batch_remaining_jobs candidates));;

let candle_disjunctive_second_batch_remaining_axioms_before = axioms ();;
let candle_disjunctive_second_batch_remaining_function0_failures =
  candle_disjunctive_second_batch_remaining_scan_failures
    "second-sibling-batch-function0-remaining-scan"
    candle_disjunctive_next_batch_prepared0
    candle_disjunctive_next_batch_point_plan0
    candle_disjunctive_second_batch_remaining_function0;;
let candle_disjunctive_second_batch_remaining_function1_failures =
  candle_disjunctive_second_batch_remaining_scan_failures
    "second-sibling-batch-function1-remaining-scan"
    candle_disjunctive_next_batch_prepared1
    candle_disjunctive_next_batch_point_plan1
    candle_disjunctive_second_batch_remaining_function1;;

let candle_disjunctive_second_batch_remaining_rejected =
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_second_batch_remaining_function0_failures
    candle_disjunctive_second_batch_remaining_function0 @
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_second_batch_remaining_function1_failures
    candle_disjunctive_second_batch_remaining_function1;;

let candle_disjunctive_second_batch_remaining_child_failed
    record index selected axis side =
  List.exists
    (fun (actual_record,actual_index,actual_selected,actual_axis,
          actual_side,_) ->
      actual_record = record && actual_index = index &&
      actual_selected = selected && actual_axis = axis &&
      actual_side = side)
    candle_disjunctive_second_batch_remaining_rejected;;

let candle_disjunctive_second_batch_remaining_choose_axis
    record index selected =
  try
    Some
      (List.find
        (fun axis ->
          not
            (candle_disjunctive_second_batch_remaining_child_failed
              record index selected axis 0) &&
          not
            (candle_disjunctive_second_batch_remaining_child_failed
              record index selected axis 1))
        [2;3;4;5;6])
  with Not_found -> None;;

let rec candle_disjunctive_second_batch_remaining_select = function
  | [] -> [],[]
  | (record,index,selected)::remaining ->
      let choices,unsolved =
        candle_disjunctive_second_batch_remaining_select remaining in
      (match candle_disjunctive_second_batch_remaining_choose_axis
               record index selected with
       | Some axis -> (record,index,selected,axis)::choices,unsolved
       | None -> choices,(record,index,selected)::unsolved);;

let candle_disjunctive_second_batch_remaining_selected,
    candle_disjunctive_second_batch_remaining_unsolved =
  candle_disjunctive_second_batch_remaining_select
    candle_disjunctive_second_batch_axis1_unsolved;;
let candle_disjunctive_second_batch_split_selected_complete =
  candle_disjunctive_second_batch_axis1_selected @
  candle_disjunctive_second_batch_remaining_selected;;

let candle_disjunctive_second_batch_remaining_axioms_after = axioms ();;
let candle_disjunctive_second_batch_remaining_expected =
  10 * length candle_disjunctive_second_batch_axis1_unsolved;;

if length candle_disjunctive_second_batch_remaining_candidates <>
     candle_disjunctive_second_batch_remaining_expected ||
   length candle_disjunctive_second_batch_remaining_function0 +
     length candle_disjunctive_second_batch_remaining_function1 <>
     candle_disjunctive_second_batch_remaining_expected ||
   length candle_disjunctive_second_batch_split_selected_complete +
     length candle_disjunctive_second_batch_remaining_unsolved <>
     length candle_disjunctive_second_batch_rejected ||
   length candle_disjunctive_second_batch_remaining_axioms_after <>
     length candle_disjunctive_second_batch_remaining_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_second_batch_remaining_axioms_before)
       candle_disjunctive_second_batch_remaining_axioms_after) then
  failwith "second sibling remaining scan: validation failed";;

print_endline
  ("CANDLE_CV_SECOND_SIBLING_BATCH_REMAINING_SCAN_OK DEVELOPMENT_NON_RELEASE" ^
   " unresolved_after_axis1=" ^
   string_of_int (length candle_disjunctive_second_batch_axis1_unsolved) ^
   " candidate_children=" ^
   string_of_int candle_disjunctive_second_batch_remaining_expected ^
   " rejected_children=" ^
   string_of_int (length candle_disjunctive_second_batch_remaining_rejected) ^
   " selected_splits=" ^
   candle_disjunctive_next_batch_split_selection_string
     candle_disjunctive_second_batch_remaining_selected ^
   " unsolved=" ^
   candle_disjunctive_next_batch_split_unsolved_string
     candle_disjunctive_second_batch_remaining_unsolved ^
   " assumptions=0 axiom_growth=0");;

end;;
