(* Scan the fourth authentic sibling batch with the two prepared programs. *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_scan = struct

open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let candle_disjunctive_fourth_batch_tagged =
  candle_disjunctive_next_batch_tag 16364 0
    candle_disjunctive_case16364_leaves @
  candle_disjunctive_next_batch_tag 16625 0
    candle_disjunctive_case16625_leaves @
  candle_disjunctive_next_batch_tag 16587 0
    candle_disjunctive_case16587_leaves;;
let candle_disjunctive_fourth_batch_function0 =
  List.filter
    (fun (_,_,selected,_) -> selected = 0)
    candle_disjunctive_fourth_batch_tagged;;
let candle_disjunctive_fourth_batch_function1 =
  List.filter
    (fun (_,_,selected,_) -> selected = 1)
    candle_disjunctive_fourth_batch_tagged;;

let candle_disjunctive_fourth_batch_scan_axioms_before = axioms ();;
let candle_disjunctive_fourth_batch_function0_theorem,
    candle_disjunctive_fourth_batch_function0_failures =
  candle_disjunctive_next_batch_scan_run
    "fourth-sibling-batch-function0-scan"
    candle_disjunctive_next_batch_prepared0
    candle_disjunctive_next_batch_point_plan0
    candle_disjunctive_fourth_batch_function0;;
let candle_disjunctive_fourth_batch_function1_theorem,
    candle_disjunctive_fourth_batch_function1_failures =
  candle_disjunctive_next_batch_scan_run
    "fourth-sibling-batch-function1-scan"
    candle_disjunctive_next_batch_prepared1
    candle_disjunctive_next_batch_point_plan1
    candle_disjunctive_fourth_batch_function1;;

let candle_disjunctive_fourth_batch_rejected =
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_fourth_batch_function0_failures
    candle_disjunctive_fourth_batch_function0 @
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_fourth_batch_function1_failures
    candle_disjunctive_fourth_batch_function1;;

let candle_disjunctive_fourth_batch_case_failures record =
  map (fun (_,index,_,_) -> index)
    (List.filter
      (fun (actual,_,_,_) -> actual = record)
      candle_disjunctive_fourth_batch_rejected);;

let candle_disjunctive_case16364_scan_failures =
  candle_disjunctive_fourth_batch_case_failures 16364;;
let candle_disjunctive_case16625_scan_failures =
  candle_disjunctive_fourth_batch_case_failures 16625;;
let candle_disjunctive_case16587_scan_failures =
  candle_disjunctive_fourth_batch_case_failures 16587;;
let candle_disjunctive_fourth_batch_scan_axioms_after = axioms ();;
let candle_disjunctive_fourth_batch_scan_expected =
  candle_disjunctive_case16364_leaf_count +
  candle_disjunctive_case16625_leaf_count +
  candle_disjunctive_case16587_leaf_count;;

if length candle_disjunctive_fourth_batch_tagged <>
     candle_disjunctive_fourth_batch_scan_expected ||
   length candle_disjunctive_fourth_batch_function0 +
     length candle_disjunctive_fourth_batch_function1 <>
     candle_disjunctive_fourth_batch_scan_expected ||
   length candle_disjunctive_fourth_batch_rejected <>
     length candle_disjunctive_case16364_scan_failures +
     length candle_disjunctive_case16625_scan_failures +
     length candle_disjunctive_case16587_scan_failures ||
   length candle_disjunctive_fourth_batch_scan_axioms_after <>
     length candle_disjunctive_fourth_batch_scan_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_fourth_batch_scan_axioms_before)
       candle_disjunctive_fourth_batch_scan_axioms_after) then
  failwith "fourth sibling batch scan: validation failed";;

print_endline
  ("CANDLE_CV_FOURTH_SIBLING_BATCH_SCAN_OK DEVELOPMENT_NON_RELEASE" ^
   " function0_jobs=" ^
   string_of_int (length candle_disjunctive_fourth_batch_function0) ^
   " function1_jobs=" ^
   string_of_int (length candle_disjunctive_fourth_batch_function1) ^
   candle_disjunctive_next_batch_scan_summary 16364 34
     candle_disjunctive_case16364_leaf_count
     candle_disjunctive_case16364_scan_failures ^
   candle_disjunctive_next_batch_scan_summary 16625 295
     candle_disjunctive_case16625_leaf_count
     candle_disjunctive_case16625_scan_failures ^
   candle_disjunctive_next_batch_scan_summary 16587 257
     candle_disjunctive_case16587_leaf_count
     candle_disjunctive_case16587_scan_failures ^
   " total_jobs=" ^
   string_of_int candle_disjunctive_fourth_batch_scan_expected ^
   " assumptions=0 axiom_growth=0");;

end;;
