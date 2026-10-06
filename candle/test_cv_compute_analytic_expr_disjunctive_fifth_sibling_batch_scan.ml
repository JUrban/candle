(* Scan the fifth authentic sibling batch with the fixed-nonlinear checker. *)
(* DEVELOPMENT / NON-RELEASE.  This scan selects refinement work only; the *)
(* complete checker remains the theorem-producing boundary.                 *)

needs "candle/cv_compute_analytic_expr_disjunctive_fifth_sibling_batch.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_scan = struct

open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_scan;;

(* Large job and failure vectors are exported as closures.  Candle therefore *)
(* prints only <fun> for them when the fragment returns, while downstream     *)
(* refinements still recover the exact retained values from the checkpoint.  *)
let candle_disjunctive_fifth_batch_tagged_get,
    candle_disjunctive_fifth_batch_function0_get,
    candle_disjunctive_fifth_batch_function1_get,
    candle_disjunctive_fifth_batch_rejected_get,
    candle_disjunctive_case16646_scan_failures_get,
    candle_disjunctive_case16659_scan_failures_get,
    candle_disjunctive_case16658_scan_failures_get =
  let tagged =
    candle_disjunctive_next_batch_tag 16646 0
      candle_disjunctive_case16646_leaves @
    candle_disjunctive_next_batch_tag 16659 0
      candle_disjunctive_case16659_leaves @
    candle_disjunctive_next_batch_tag 16658 0
      candle_disjunctive_case16658_leaves in
  let function0 =
    List.filter (fun (_,_,selected,_) -> selected = 0) tagged
  and function1 =
    List.filter (fun (_,_,selected,_) -> selected = 1) tagged in
  let scan_cells point_plan jobs =
    map
      (fun (_,_,_,domain) ->
        candle_disjunctive_next_batch_scan_cell point_plan domain)
      jobs in
  let axioms_before = axioms () in
  let count0,failures0 =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_scan_six
      "fifth-sibling-batch-function0-fixed-nonlinear-scan"
      candle_disjunctive_next_batch_prepared0
      (scan_cells candle_disjunctive_next_batch_point_plan0 function0) in
  let count1,failures1 =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_scan_six
      "fifth-sibling-batch-function1-fixed-nonlinear-scan"
      candle_disjunctive_next_batch_prepared1
      (scan_cells candle_disjunctive_next_batch_point_plan1 function1) in
  let rejected =
    candle_disjunctive_next_batch_select_failures 0 failures0 function0 @
    candle_disjunctive_next_batch_select_failures 0 failures1 function1 in
  let case_failures record =
    map (fun (_,index,_,_) -> index)
      (List.filter (fun (actual,_,_,_) -> actual = record) rejected) in
  let case16646_failures = case_failures 16646
  and case16659_failures = case_failures 16659
  and case16658_failures = case_failures 16658 in
  let expected =
    candle_disjunctive_case16646_leaf_count +
    candle_disjunctive_case16659_leaf_count +
    candle_disjunctive_case16658_leaf_count in
  let axioms_after = axioms () in
  if length tagged <> expected ||
     count0 <> length function0 || count1 <> length function1 ||
     count0 + count1 <> expected ||
     length rejected <>
       length case16646_failures + length case16659_failures +
       length case16658_failures ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before) axioms_after) then
    failwith "fifth sibling batch fixed nonlinear scan: validation failed";
  print_endline
    ("CANDLE_CV_FIFTH_SIBLING_BATCH_FIXED_NONLINEAR_SCAN_OK" ^
     " DEVELOPMENT_NON_RELEASE" ^
     " function0_jobs=" ^ string_of_int count0 ^
     " function1_jobs=" ^ string_of_int count1 ^
     candle_disjunctive_next_batch_scan_summary 16646 316
       candle_disjunctive_case16646_leaf_count case16646_failures ^
     candle_disjunctive_next_batch_scan_summary 16659 329
       candle_disjunctive_case16659_leaf_count case16659_failures ^
     candle_disjunctive_next_batch_scan_summary 16658 328
       candle_disjunctive_case16658_leaf_count case16658_failures ^
     " total_jobs=" ^ string_of_int expected ^
     " assumptions=0 axiom_growth=0");
  (fun () -> tagged),
  (fun () -> function0),
  (fun () -> function1),
  (fun () -> rejected),
  (fun () -> case16646_failures),
  (fun () -> case16659_failures),
  (fun () -> case16658_failures);;

end;;
