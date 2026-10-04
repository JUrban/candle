(* Exercise the complete-checker handoff with a genuine two-root stack. *)

needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch_forest_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_forest_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_two_root_forest_adapter = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_forest_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let candle_disjunctive_two_root_cells =
  [List.nth candle_disjunctive_next_batch_cells0 0;
   List.nth candle_disjunctive_next_batch_cells0 1];;
let candle_disjunctive_two_root_tokens =
  [Candle_disjunctive_next_batch_token_leaf;
   Candle_disjunctive_next_batch_token_leaf];;
let candle_disjunctive_two_root_encoded_jobs =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
    candle_disjunctive_two_root_cells;;
let candle_disjunctive_two_root_encoded_tokens =
  candle_q_dim_stable_program_cval_list
    (map candle_disjunctive_next_batch_encode_token
      candle_disjunctive_two_root_tokens);;
let candle_disjunctive_two_root_logical_tokens =
  mk_list
    (map candle_disjunctive_next_batch_logical_token
       candle_disjunctive_two_root_tokens,
     type_of
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`);;

let candle_disjunctive_two_root_call =
  list_mk_comb
    (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
     [candle_disjunctive_next_batch_prepared0.program_representation_term;
      `Cexp_num 6`;candle_disjunctive_two_root_encoded_tokens;
      candle_disjunctive_two_root_encoded_jobs]);;
let candle_disjunctive_two_root_axioms_before = axioms ();;
let candle_disjunctive_two_root_compute =
  candle_q_dim_analytic_jet_compute
    (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
    candle_disjunctive_two_root_call;;

let candle_disjunctive_two_root_boxes cell =
  candle_poly_fixture_q_boxes
    cell.variable_batch_stable_cell.stable_batch_lower
    cell.variable_batch_stable_cell.stable_batch_upper;;
let candle_disjunctive_two_root_expected_stack =
  rev (map candle_disjunctive_two_root_boxes
         candle_disjunctive_two_root_cells);;
let candle_disjunctive_two_root_forest =
  candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_forest_six
    candle_disjunctive_next_batch_prepared0
    candle_disjunctive_two_root_logical_tokens
    candle_disjunctive_two_root_encoded_tokens
    candle_disjunctive_two_root_encoded_jobs
    candle_disjunctive_two_root_compute
    candle_disjunctive_two_root_expected_stack;;
let candle_disjunctive_two_root_axioms_after = axioms ();;

if length candle_disjunctive_two_root_forest.
     variable_complete_forest_source_theorems <> 2 ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [])
       candle_disjunctive_two_root_forest.
         variable_complete_forest_source_theorems) ||
   length candle_disjunctive_two_root_axioms_after <>
     length candle_disjunctive_two_root_axioms_before ||
   not
     (List.for_all
       (fun axiom -> List.mem axiom candle_disjunctive_two_root_axioms_before)
       candle_disjunctive_two_root_axioms_after) then
  failwith "two-root forest adapter: final validation failed";;

print_endline
  "CANDLE_CV_TWO_ROOT_FOREST_ADAPTER_OK DEVELOPMENT_NON_RELEASE roots=2 assumptions=0 axiom_growth=0";;

end;;
