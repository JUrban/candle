(* Two complete fixed-nonlinear reflected verdicts for the fifth authentic  *)
(* sibling batch.  The numerical checker consumes ordinary encoded data and *)
(* returns one compact verdict per shared source program.                    *)

needs "candle/cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_forest_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute.ml";;

module Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_complete_compute = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let candle_disjunctive_fifth_batch_encoded_tokens tokens =
  candle_q_dim_stable_program_cval_list
    (map candle_disjunctive_next_batch_encode_token tokens);;

let candle_disjunctive_fifth_batch_logical_tokens tokens =
  mk_list
    (map candle_disjunctive_next_batch_logical_token tokens,
     type_of
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`);;

let candle_disjunctive_fifth_batch_encoded_jobs0 =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
    candle_disjunctive_fifth_batch_cells0;;
let candle_disjunctive_fifth_batch_encoded_jobs1 =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
    candle_disjunctive_fifth_batch_cells1;;
let candle_disjunctive_fifth_batch_encoded_tokens0 =
  candle_disjunctive_fifth_batch_encoded_tokens
    candle_disjunctive_fifth_batch_tokens0;;
let candle_disjunctive_fifth_batch_encoded_tokens1 =
  candle_disjunctive_fifth_batch_encoded_tokens
    candle_disjunctive_fifth_batch_tokens1;;
let candle_disjunctive_fifth_batch_logical_tokens0 =
  candle_disjunctive_fifth_batch_logical_tokens
    candle_disjunctive_fifth_batch_tokens0;;
let candle_disjunctive_fifth_batch_logical_tokens1 =
  candle_disjunctive_fifth_batch_logical_tokens
    candle_disjunctive_fifth_batch_tokens1;;

let candle_disjunctive_fifth_batch_complete_call
    prepared encoded_tokens encoded_jobs =
  list_mk_comb
    (`candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check`,
     [prepared.program_representation_term;`Cexp_num 6`;encoded_tokens;
      encoded_jobs]);;

let candle_disjunctive_fifth_batch_call0 =
  candle_disjunctive_fifth_batch_complete_call
    candle_disjunctive_next_batch_prepared0
    candle_disjunctive_fifth_batch_encoded_tokens0
    candle_disjunctive_fifth_batch_encoded_jobs0;;
let candle_disjunctive_fifth_batch_call1 =
  candle_disjunctive_fifth_batch_complete_call
    candle_disjunctive_next_batch_prepared1
    candle_disjunctive_fifth_batch_encoded_tokens1
    candle_disjunctive_fifth_batch_encoded_jobs1;;

let candle_disjunctive_fifth_batch_computed_accepts label call theorem =
  let numerical,topology =
    candle_q_dim_stable_program_dest_cval_pair
      (label ^ " reflected result") (rand (concl theorem)) in
  let topology_success,topology_payload =
    candle_q_dim_stable_program_dest_cval_pair
      (label ^ " topology result") topology in
  let remaining_jobs,_ =
    candle_q_dim_stable_program_dest_cval_pair
      (label ^ " topology payload") topology_payload in
  hyp theorem = [] && aconv (lhand (concl theorem)) call &&
  aconv numerical `Cexp_num 1` &&
  aconv topology_success `Cexp_num 1` &&
  aconv remaining_jobs `Cexp_num 0`;;

let candle_disjunctive_fifth_batch_compute0_get,
    candle_disjunctive_fifth_batch_compute1_get =
  let axioms_before = axioms () in
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-function0-fixed-nonlinear-complete-begin";
  let compute0 =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_compute_eqs ())
      candle_disjunctive_fifth_batch_call0 in
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-function0-fixed-nonlinear-complete-end";
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-function1-fixed-nonlinear-complete-begin";
  let compute1 =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_compute_eqs ())
      candle_disjunctive_fifth_batch_call1 in
  candle_q_dim_analytic_jet_profile_event
    "fifth-sibling-batch-function1-fixed-nonlinear-complete-end";
  let axioms_after = axioms () in
  if not
       (candle_disjunctive_fifth_batch_computed_accepts
         "fifth sibling batch function0"
         candle_disjunctive_fifth_batch_call0 compute0) ||
     not
       (candle_disjunctive_fifth_batch_computed_accepts
         "fifth sibling batch function1"
         candle_disjunctive_fifth_batch_call1 compute1) ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "fifth sibling batch complete compute: validation failed";
  print_endline
    ("CANDLE_CV_FIFTH_SIBLING_BATCH_FIXED_NONLINEAR_COMPLETE_COMPUTE_OK" ^
     " DEVELOPMENT_NON_RELEASE" ^
     " numerical_cells=" ^
     string_of_int candle_disjunctive_fifth_batch_total_cells ^
     " token_items=" ^
     string_of_int candle_disjunctive_fifth_batch_total_tokens ^
     " complete_verdicts=2 assumptions=0 axiom_growth=0");
  (fun () -> compute0),(fun () -> compute1);;

end;;
