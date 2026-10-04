(* Scan three authentic sibling plans, retaining each selected disjunct. *)

needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_scan;;

let rec candle_disjunctive_next_batch_tag record index = function
  | [] -> []
  | (selected,domain)::remaining ->
      (record,index,selected,domain)::
      candle_disjunctive_next_batch_tag record (index + 1) remaining;;

let candle_disjunctive_next_batch_tagged =
  candle_disjunctive_next_batch_tag 16617 0
    candle_disjunctive_case16617_leaves @
  candle_disjunctive_next_batch_tag 16593 0
    candle_disjunctive_case16593_leaves @
  candle_disjunctive_next_batch_tag 16582 0
    candle_disjunctive_case16582_leaves;;
let candle_disjunctive_next_batch_function0 =
  List.filter
    (fun (_,_,selected,_) -> selected = 0)
    candle_disjunctive_next_batch_tagged;;
let candle_disjunctive_next_batch_function1 =
  List.filter
    (fun (_,_,selected,_) -> selected = 1)
    candle_disjunctive_next_batch_tagged;;

let candle_disjunctive_next_batch_prepared0 =
  List.nth candle_disjunctive_case16594_plan_prepared 0;;
let candle_disjunctive_next_batch_prepared1 =
  List.nth candle_disjunctive_case16594_plan_prepared 1;;
let candle_disjunctive_next_batch_point_plan0 =
  candle_q_dim_taylor_model_point_plan_six
    candle_disjunctive_next_batch_prepared0;;
let candle_disjunctive_next_batch_point_plan1 =
  candle_q_dim_taylor_model_point_plan_six
    candle_disjunctive_next_batch_prepared1;;

let candle_disjunctive_next_batch_scan_cell point_plan domain =
  let lower,upper = candle_disjunctive_fixed_outer_domain_bounds domain in
  let center =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  {variable_batch_box_intervals =
     map (candle_disjunctive_fixed_outer_widen 5 4) center;
   variable_batch_stable_cell =
     {stable_batch_center_intervals = center;
      stable_batch_lower = lower;
      stable_batch_upper = upper}};;

let candle_disjunctive_next_batch_scan_run label prepared point_plan jobs =
  let cells =
    map
      (fun (_,_,_,domain) ->
        candle_disjunctive_next_batch_scan_cell point_plan domain)
      jobs in
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  let call =
    list_mk_comb
      (`candle_cv_fso_variable_jobs_scan`,
       [prepared.program_representation_term;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event (label ^ "-begin");
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_variable_jobs_scan_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event (label ^ "-end");
  let count,failures =
    candle_cv_fso_variable_jobs_scan_decode label (rand (concl theorem)) in
  if count <> length jobs || hyp theorem <> [] ||
     not (aconv (lhand (concl theorem)) call) then
    failwith (label ^ ": validation failed");
  theorem,failures;;

let candle_disjunctive_next_batch_scan_axioms_before = axioms ();;
let candle_disjunctive_next_batch_function0_theorem,
    candle_disjunctive_next_batch_function0_failures =
  candle_disjunctive_next_batch_scan_run
    "next-sibling-batch-function0-scan"
    candle_disjunctive_next_batch_prepared0
    candle_disjunctive_next_batch_point_plan0
    candle_disjunctive_next_batch_function0;;
let candle_disjunctive_next_batch_function1_theorem,
    candle_disjunctive_next_batch_function1_failures =
  candle_disjunctive_next_batch_scan_run
    "next-sibling-batch-function1-scan"
    candle_disjunctive_next_batch_prepared1
    candle_disjunctive_next_batch_point_plan1
    candle_disjunctive_next_batch_function1;;

let rec candle_disjunctive_next_batch_select_failures offset failures = function
  | [] -> []
  | job::remaining ->
      let selected =
        candle_disjunctive_next_batch_select_failures
          (offset + 1) failures remaining in
      if List.mem offset failures then job::selected else selected;;

let candle_disjunctive_next_batch_rejected =
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_next_batch_function0_failures
    candle_disjunctive_next_batch_function0 @
  candle_disjunctive_next_batch_select_failures 0
    candle_disjunctive_next_batch_function1_failures
    candle_disjunctive_next_batch_function1;;

let candle_disjunctive_next_batch_case_failures record =
  map (fun (_,index,_,_) -> index)
    (List.filter
      (fun (actual,_,_,_) -> actual = record)
      candle_disjunctive_next_batch_rejected);;

let candle_disjunctive_case16617_scan_failures =
  candle_disjunctive_next_batch_case_failures 16617;;
let candle_disjunctive_case16593_scan_failures =
  candle_disjunctive_next_batch_case_failures 16593;;
let candle_disjunctive_case16582_scan_failures =
  candle_disjunctive_next_batch_case_failures 16582;;
let candle_disjunctive_next_batch_scan_axioms_after = axioms ();;
let candle_disjunctive_next_batch_scan_expected =
  candle_disjunctive_case16617_leaf_count +
  candle_disjunctive_case16593_leaf_count +
  candle_disjunctive_case16582_leaf_count;;

if length candle_disjunctive_next_batch_tagged <>
     candle_disjunctive_next_batch_scan_expected ||
   length candle_disjunctive_next_batch_function0 +
     length candle_disjunctive_next_batch_function1 <>
     candle_disjunctive_next_batch_scan_expected ||
   length candle_disjunctive_next_batch_rejected <>
     length candle_disjunctive_case16617_scan_failures +
     length candle_disjunctive_case16593_scan_failures +
     length candle_disjunctive_case16582_scan_failures ||
   length candle_disjunctive_next_batch_scan_axioms_after <>
     length candle_disjunctive_next_batch_scan_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_next_batch_scan_axioms_before)
       candle_disjunctive_next_batch_scan_axioms_after) then
  failwith "next sibling batch scan: validation failed";;

let candle_disjunctive_next_batch_scan_summary record index count failures =
  " record" ^ string_of_int record ^ "_index=" ^ string_of_int index ^
  " jobs=" ^ string_of_int count ^
  " accepted=" ^ string_of_int (count - length failures) ^
  " rejected=" ^ string_of_int (length failures) ^
  " rejected_indices=" ^
  candle_cv_fso_variable_jobs_scan_indices_string failures;;

print_endline
  ("CANDLE_CV_NEXT_SIBLING_BATCH_SCAN_OK DEVELOPMENT_NON_RELEASE" ^
   " function0_jobs=" ^
   string_of_int (length candle_disjunctive_next_batch_function0) ^
   " function1_jobs=" ^
   string_of_int (length candle_disjunctive_next_batch_function1) ^
   candle_disjunctive_next_batch_scan_summary 16617 287
     candle_disjunctive_case16617_leaf_count
     candle_disjunctive_case16617_scan_failures ^
   candle_disjunctive_next_batch_scan_summary 16593 263
     candle_disjunctive_case16593_leaf_count
     candle_disjunctive_case16593_scan_failures ^
   candle_disjunctive_next_batch_scan_summary 16582 252
     candle_disjunctive_case16582_leaf_count
     candle_disjunctive_case16582_scan_failures ^
   " total_jobs=" ^
   string_of_int candle_disjunctive_next_batch_scan_expected ^
   " assumptions=0 axiom_growth=0");;

end;;
