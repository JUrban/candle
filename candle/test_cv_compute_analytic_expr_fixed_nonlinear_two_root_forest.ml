(* Two-root integration test for the fixed-nonlinear complete forest handoff. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_forest_prove.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_fixed_nonlinear_discriminator.ml";;

module Test_cv_compute_analytic_expr_fixed_nonlinear_two_root_forest = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_forest_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_fixed_nonlinear_discriminator;;

let candle_fixed_nonlinear_two_root_cells =
  let rec select index remaining cells =
    match remaining,cells with
    | 0,_ -> []
    | _,[] -> failwith "fixed nonlinear two-root forest: accepted underflow"
    | needed,head::tail ->
        if List.mem index candle_disjunctive_fsn_discriminator_fixed_failures
        then select (index + 1) needed tail
        else head::select (index + 1) (needed - 1) tail in
  select 0 2 candle_disjunctive_fsn_discriminator_cells;;

let candle_fixed_nonlinear_two_root_tokens =
  mk_list
    ([`Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`;
      `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`],
     type_of
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`);;

let candle_fixed_nonlinear_two_root_encoded_tokens =
  candle_q_dim_stable_program_cval_list [`Cexp_num 0`;`Cexp_num 0`];;

let candle_fixed_nonlinear_two_root_encoded_jobs =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
    candle_fixed_nonlinear_two_root_cells;;

let candle_fixed_nonlinear_two_root_expected_stack =
  rev
    (map
      (fun cell ->
        let stable = cell.variable_batch_stable_cell in
        candle_poly_fixture_q_boxes
          stable.stable_batch_lower stable.stable_batch_upper)
      candle_fixed_nonlinear_two_root_cells);;

let candle_fixed_nonlinear_two_root_call =
  list_mk_comb
    (`candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check`,
     [candle_disjunctive_next_batch_prepared1.program_representation_term;
      `Cexp_num 6`;candle_fixed_nonlinear_two_root_encoded_tokens;
      candle_fixed_nonlinear_two_root_encoded_jobs]);;

let candle_fixed_nonlinear_two_root_axioms_before = axioms ();;
let _ =
  print_endline
    "CANDLE_CV_FIXED_NONLINEAR_TWO_ROOT_COMPUTE_BEGIN DEVELOPMENT_NON_RELEASE";;
let candle_fixed_nonlinear_two_root_compute =
  candle_q_dim_analytic_jet_compute
    (candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_compute_eqs ())
    candle_fixed_nonlinear_two_root_call;;
let _ =
  print_endline
    "CANDLE_CV_FIXED_NONLINEAR_TWO_ROOT_COMPUTE_END DEVELOPMENT_NON_RELEASE";;

let candle_fixed_nonlinear_two_root_forest =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_computed_forest_six
    candle_disjunctive_next_batch_prepared1
    candle_fixed_nonlinear_two_root_tokens
    candle_fixed_nonlinear_two_root_encoded_tokens
    candle_fixed_nonlinear_two_root_encoded_jobs
    candle_fixed_nonlinear_two_root_compute
    candle_fixed_nonlinear_two_root_expected_stack;;

let candle_fixed_nonlinear_two_root_axioms_after = axioms ();;

if length candle_fixed_nonlinear_two_root_cells <> 2 ||
   length
     candle_fixed_nonlinear_two_root_forest.
       fixed_nonlinear_variable_complete_forest_root_boxes <> 2 ||
   length
     candle_fixed_nonlinear_two_root_forest.
       fixed_nonlinear_variable_complete_forest_source_theorems <> 2 ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [])
       candle_fixed_nonlinear_two_root_forest.
         fixed_nonlinear_variable_complete_forest_source_theorems) ||
   length candle_fixed_nonlinear_two_root_axioms_after <>
     length candle_fixed_nonlinear_two_root_axioms_before ||
   not
     (List.for_all
       (fun axiom -> List.mem axiom candle_fixed_nonlinear_two_root_axioms_before)
       candle_fixed_nonlinear_two_root_axioms_after) then
  failwith "fixed nonlinear two-root forest: validation failed";;

print_endline
  "CANDLE_CV_FIXED_NONLINEAR_TWO_ROOT_FOREST_OK DEVELOPMENT_NON_RELEASE roots=2 source_theorems=2 assumptions=0 axiom_growth=0";;

end;;
