(* Rediscover the known case-16479 retry leaves from numerical data only. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16479_direct_leaf_grouping.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_scan.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16479_plan_scan = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16479_leaf_grouping;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_scan;;

let candle_disjunctive_case16479_scan_prepared =
  candle_disjunctive_case16594_engine_state.family_engine_prepared;;
let candle_disjunctive_case16479_scan_point_plan =
  candle_disjunctive_case16594_engine_state.family_engine_point_plan;;

let candle_disjunctive_case16479_scan_cell domain =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds domain in
  let center =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_disjunctive_case16479_scan_point_plan lower upper in
  {variable_batch_box_intervals =
     map (candle_disjunctive_fixed_outer_widen 5 4) center;
   variable_batch_stable_cell =
     {stable_batch_center_intervals = center;
      stable_batch_lower = lower;
      stable_batch_upper = upper}};;

let candle_disjunctive_case16479_scan_cells =
  map candle_disjunctive_case16479_scan_cell
    candle_disjunctive_case16479_leaves;;
let candle_disjunctive_case16479_scan_encoded_jobs =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
    candle_disjunctive_case16479_scan_cells;;
let candle_disjunctive_case16479_scan_call =
  list_mk_comb
    (`candle_cv_fso_variable_jobs_scan`,
     [candle_disjunctive_case16479_scan_prepared.program_representation_term;
      candle_disjunctive_case16479_scan_encoded_jobs]);;

let candle_disjunctive_case16479_scan_axioms_before = axioms ();;
let _ =
  candle_q_dim_analytic_jet_profile_event "case16479-plan-scan-begin";;
let candle_disjunctive_case16479_scan_theorem =
  candle_q_dim_analytic_jet_compute
    candle_cv_fso_variable_jobs_scan_compute_eqs
    candle_disjunctive_case16479_scan_call;;
let _ =
  candle_q_dim_analytic_jet_profile_event "case16479-plan-scan-end";;

let candle_disjunctive_case16479_scan_count,
    candle_disjunctive_case16479_scan_failures =
  candle_cv_fso_variable_jobs_scan_decode "case16479 plan scan"
    (rand (concl candle_disjunctive_case16479_scan_theorem));;
let candle_disjunctive_case16479_scan_axioms_after = axioms ();;

if length candle_disjunctive_case16479_scan_cells <> 788 ||
   candle_disjunctive_case16479_scan_count <> 788 ||
   candle_disjunctive_case16479_scan_failures <>
     [387;420;422;424;446;536;688] ||
   hyp candle_disjunctive_case16479_scan_theorem <> [] ||
   not
     (aconv (lhand (concl candle_disjunctive_case16479_scan_theorem))
       candle_disjunctive_case16479_scan_call) ||
   length candle_disjunctive_case16479_scan_axioms_after <>
     length candle_disjunctive_case16479_scan_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_case16479_scan_axioms_before)
       candle_disjunctive_case16479_scan_axioms_after) then
  failwith "case16479 plan scan: validation failed";;

print_endline
  "CANDLE_CV_CASE16479_PLAN_SCAN_OK DEVELOPMENT_NON_RELEASE jobs=788 accepted=781 rejected=7 rejected_indices=387,420,422,424,446,536,688 assumptions=0 axiom_growth=0";;

end;;
