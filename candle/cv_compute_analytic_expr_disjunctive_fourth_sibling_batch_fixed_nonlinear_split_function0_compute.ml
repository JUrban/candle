(* Split-call complete reflected verdict for function 0 of the fourth        *)
(* authentic sibling batch.  Each Kernel.compute invocation has its own      *)
(* verified evaluator clock; the resulting closed equalities are combined   *)
(* with primitive equality rules into the unchanged complete-check theorem.  *)
(* DEVELOPMENT / NON-RELEASE.                                                *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute.ml";;

module Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_split_function0_compute = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let candle_disjunctive_fourth_split_encoded_tokens tokens =
  candle_q_dim_stable_program_cval_list
    (map candle_disjunctive_next_batch_encode_token tokens);;

let candle_disjunctive_fourth_split_encoded_jobs0 =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
    candle_disjunctive_fourth_batch_cells0;;

let candle_disjunctive_fourth_split_encoded_tokens0 =
  candle_disjunctive_fourth_split_encoded_tokens
    candle_disjunctive_fourth_batch_tokens0;;

let candle_disjunctive_fourth_split_numerical_call0 =
  list_mk_comb
    (`candle_cv_fsn_variable_raw_jobs_check`,
     [candle_disjunctive_next_batch_prepared0.program_representation_term;
      candle_disjunctive_fourth_split_encoded_jobs0]);;

let candle_disjunctive_fourth_split_topology_call0 =
  list_mk_comb
    (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`,
     [`Cexp_num 6`;candle_disjunctive_fourth_split_encoded_tokens0;
      candle_disjunctive_fourth_split_encoded_jobs0;`Cexp_num 0`]);;

let candle_disjunctive_fourth_split_complete_call0 =
  list_mk_comb
    (`candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check`,
     [candle_disjunctive_next_batch_prepared0.program_representation_term;
      `Cexp_num 6`;candle_disjunctive_fourth_split_encoded_tokens0;
      candle_disjunctive_fourth_split_encoded_jobs0]);;

let candle_disjunctive_fourth_split_combine_complete
    complete_call numerical_compute topology_compute =
  if hyp numerical_compute <> [] || hyp topology_compute <> [] then
    failwith "fourth split complete: component theorem has assumptions";
  let unfolded =
    REWRITE_CONV
      [candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check_def]
      complete_call in
  let paired =
    MK_COMB (AP_TERM `Cexp_pair` numerical_compute,topology_compute) in
  if not (aconv (rand (concl unfolded)) (lhand (concl paired))) then
    failwith "fourth split complete: component theorem shape mismatch";
  TRANS unfolded paired;;

let candle_disjunctive_fourth_split_computed_accepts call theorem =
  let numerical,topology =
    candle_q_dim_stable_program_dest_cval_pair
      "fourth split reflected result" (rand (concl theorem)) in
  let topology_success,topology_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "fourth split topology result" topology in
  let remaining_jobs,_ =
    candle_q_dim_stable_program_dest_cval_pair
      "fourth split topology payload" topology_payload in
  hyp theorem = [] && aconv (lhand (concl theorem)) call &&
  aconv numerical `Cexp_num 1` &&
  aconv topology_success `Cexp_num 1` &&
  aconv remaining_jobs `Cexp_num 0`;;

let candle_disjunctive_fourth_split_axioms_before = axioms ();;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-batch-function0-split-topology-begin";;

let candle_disjunctive_fourth_split_topology_compute0 =
  candle_q_dim_analytic_jet_compute
    candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs
    candle_disjunctive_fourth_split_topology_call0;;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-batch-function0-split-topology-end";;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-batch-function0-split-numerical-begin";;

let candle_disjunctive_fourth_split_numerical_compute0 =
  candle_q_dim_analytic_jet_compute
    candle_cv_fixed_nonlinear_compute_eqs
    candle_disjunctive_fourth_split_numerical_call0;;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-batch-function0-split-numerical-end";;

let candle_disjunctive_fourth_split_compute0 =
  candle_disjunctive_fourth_split_combine_complete
    candle_disjunctive_fourth_split_complete_call0
    candle_disjunctive_fourth_split_numerical_compute0
    candle_disjunctive_fourth_split_topology_compute0;;

let candle_disjunctive_fourth_split_axioms_after = axioms ();;

if not
     (candle_disjunctive_fourth_split_computed_accepts
       candle_disjunctive_fourth_split_complete_call0
       candle_disjunctive_fourth_split_compute0) ||
   length candle_disjunctive_fourth_split_axioms_after <>
     length candle_disjunctive_fourth_split_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_fourth_split_axioms_before)
       candle_disjunctive_fourth_split_axioms_after) then
  failwith "fourth split complete: function0 validation failed";;

let candle_disjunctive_fourth_split_compute0_get () =
  candle_disjunctive_fourth_split_compute0;;

print_endline
  ("CANDLE_CV_FOURTH_SIBLING_BATCH_FIXED_NONLINEAR_SPLIT_FUNCTION0_OK" ^
   " DEVELOPMENT_NON_RELEASE" ^
   " numerical_cells=" ^
   string_of_int (length candle_disjunctive_fourth_batch_cells0) ^
   " components=" ^
   string_of_int (length candle_disjunctive_fourth_batch_components0) ^
   " assumptions=0 axiom_growth=0");;

end;;
