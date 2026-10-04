(* Test the historically successful axis 1 first for every rejected leaf. *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_split_scan = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_scan;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let candle_disjunctive_next_batch_split_axis1
    record index selected domain =
  let left,right = M_verifier.split_domain 6 6 1 domain in
  [(record,index,selected,1,0,left);
   (record,index,selected,1,1,right)];;

let candle_disjunctive_next_batch_split_candidates =
  List.flatten
    (map
      (fun (record,index,selected,domain) ->
        candle_disjunctive_next_batch_split_axis1
          record index selected domain)
      candle_disjunctive_next_batch_rejected);;
let candle_disjunctive_next_batch_split_function0 =
  List.filter
    (fun (_,_,selected,_,_,_) -> selected = 0)
    candle_disjunctive_next_batch_split_candidates;;
let candle_disjunctive_next_batch_split_function1 =
  List.filter
    (fun (_,_,selected,_,_,_) -> selected = 1)
    candle_disjunctive_next_batch_split_candidates;;

let candle_disjunctive_next_batch_split_jobs candidates =
  map
    (fun (record,index,selected,_,_,domain) ->
      record,index,selected,domain)
    candidates;;

let candle_disjunctive_next_batch_split_axioms_before = axioms ();;
let candle_disjunctive_next_batch_split_function0_theorem,
    candle_disjunctive_next_batch_split_function0_failures =
  candle_disjunctive_next_batch_scan_run
    "next-sibling-batch-function0-split-scan"
    candle_disjunctive_next_batch_prepared0
    candle_disjunctive_next_batch_point_plan0
    (candle_disjunctive_next_batch_split_jobs
      candle_disjunctive_next_batch_split_function0);;
let candle_disjunctive_next_batch_split_function1_theorem,
    candle_disjunctive_next_batch_split_function1_failures =
  candle_disjunctive_next_batch_scan_run
    "next-sibling-batch-function1-split-scan"
    candle_disjunctive_next_batch_prepared1
    candle_disjunctive_next_batch_point_plan1
    (candle_disjunctive_next_batch_split_jobs
      candle_disjunctive_next_batch_split_function1);;

let candle_disjunctive_next_batch_split_rejected =
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_next_batch_split_function0_failures
    candle_disjunctive_next_batch_split_function0 @
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_next_batch_split_function1_failures
    candle_disjunctive_next_batch_split_function1;;

let candle_disjunctive_next_batch_split_child_failed
    record index selected axis side =
  List.exists
    (fun (actual_record,actual_index,actual_selected,actual_axis,
          actual_side,_) ->
      actual_record = record && actual_index = index &&
      actual_selected = selected && actual_axis = axis &&
      actual_side = side)
    candle_disjunctive_next_batch_split_rejected;;

let candle_disjunctive_next_batch_split_choose_axis1
    record index selected =
  if
    not
      (candle_disjunctive_next_batch_split_child_failed
        record index selected 1 0) &&
    not
      (candle_disjunctive_next_batch_split_child_failed
        record index selected 1 1)
  then Some 1
  else None;;

let rec candle_disjunctive_next_batch_split_select = function
  | [] -> [],[]
  | (record,index,selected,_)::remaining ->
      let choices,unsolved =
        candle_disjunctive_next_batch_split_select remaining in
      (match candle_disjunctive_next_batch_split_choose_axis1
               record index selected with
       | Some axis -> (record,index,selected,axis)::choices,unsolved
       | None -> choices,(record,index,selected)::unsolved);;

let candle_disjunctive_next_batch_split_selected,
    candle_disjunctive_next_batch_split_unsolved =
  candle_disjunctive_next_batch_split_select
    candle_disjunctive_next_batch_rejected;;

let rec candle_disjunctive_next_batch_split_selection_string = function
  | [] -> ""
  | [(record,index,selected,axis)] ->
      string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
      string_of_int selected ^ ":" ^ string_of_int axis
  | (record,index,selected,axis)::remaining ->
      string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
      string_of_int selected ^ ":" ^ string_of_int axis ^ "," ^
      candle_disjunctive_next_batch_split_selection_string remaining;;

let rec candle_disjunctive_next_batch_split_unsolved_string = function
  | [] -> ""
  | [(record,index,selected)] ->
      string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
      string_of_int selected
  | (record,index,selected)::remaining ->
      string_of_int record ^ ":" ^ string_of_int index ^ ":" ^
      string_of_int selected ^ "," ^
      candle_disjunctive_next_batch_split_unsolved_string remaining;;

let candle_disjunctive_next_batch_split_axioms_after = axioms ();;
let candle_disjunctive_next_batch_split_expected =
  2 * length candle_disjunctive_next_batch_rejected;;

if length candle_disjunctive_next_batch_split_candidates <>
     candle_disjunctive_next_batch_split_expected ||
   length candle_disjunctive_next_batch_split_function0 +
     length candle_disjunctive_next_batch_split_function1 <>
     candle_disjunctive_next_batch_split_expected ||
   length candle_disjunctive_next_batch_split_axioms_after <>
     length candle_disjunctive_next_batch_split_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_next_batch_split_axioms_before)
       candle_disjunctive_next_batch_split_axioms_after) then
  failwith "next sibling batch split scan: validation failed";;

print_endline
  ("CANDLE_CV_NEXT_SIBLING_BATCH_AXIS1_SCAN_OK DEVELOPMENT_NON_RELEASE" ^
   " rejected_source_leaves=" ^
   string_of_int (length candle_disjunctive_next_batch_rejected) ^
   " candidate_children=" ^
   string_of_int candle_disjunctive_next_batch_split_expected ^
   " rejected_children=" ^
   string_of_int (length candle_disjunctive_next_batch_split_rejected) ^
   " selected_splits=" ^
   candle_disjunctive_next_batch_split_selection_string
     candle_disjunctive_next_batch_split_selected ^
   " unsolved=" ^
   candle_disjunctive_next_batch_split_unsolved_string
     candle_disjunctive_next_batch_split_unsolved ^
   " assumptions=0 axiom_growth=0");;

end;;
