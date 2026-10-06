(* Two authentic fourth-batch cells, checked as independent one-cell raw      *)
(* batches and then composed before the existing compact-topology handoff.    *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_combined_split_prove.ml";;

module Test_cv_compute_analytic_expr_fixed_nonlinear_combined_split_two_root = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_combine_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_combined_split_prove;;

let candle_fixed_nonlinear_combined_split_two_root_cells =
  match candle_disjunctive_fourth_batch_cells1 with
  | first::second::_ -> [first;second]
  | _ -> failwith "fixed nonlinear combined split: cell underflow";;

let candle_fixed_nonlinear_combined_split_two_root_raw_results =
  map
    (fun cell ->
      candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_prove_six
        candle_disjunctive_next_batch_prepared1 [cell])
    candle_fixed_nonlinear_combined_split_two_root_cells;;

let candle_fixed_nonlinear_combined_split_two_root_acceptance =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_combine
    candle_fixed_nonlinear_combined_split_two_root_raw_results;;

let candle_fixed_nonlinear_combined_split_two_root_tokens =
  mk_list
    ([`Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`;
      `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`],
     type_of
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`);;

let candle_fixed_nonlinear_combined_split_two_root_encoded_tokens =
  candle_q_dim_stable_program_cval_list [`Cexp_num 0`;`Cexp_num 0`];;

let candle_fixed_nonlinear_combined_split_two_root_expected_stack =
  rev
    (map
      (fun cell ->
        let stable = cell.variable_batch_stable_cell in
        candle_poly_fixture_q_boxes
          stable.stable_batch_lower stable.stable_batch_upper)
      candle_fixed_nonlinear_combined_split_two_root_cells);;

let candle_fixed_nonlinear_combined_split_two_root_axioms_before = axioms ();;

let candle_fixed_nonlinear_combined_split_two_root_forest =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_combined_split_forest_six
    candle_fixed_nonlinear_combined_split_two_root_acceptance
    candle_fixed_nonlinear_combined_split_two_root_tokens
    candle_fixed_nonlinear_combined_split_two_root_encoded_tokens
    candle_fixed_nonlinear_combined_split_two_root_expected_stack;;

let candle_fixed_nonlinear_combined_split_two_root_axioms_after = axioms ();;

if candle_fixed_nonlinear_combined_split_two_root_acceptance.
     fixed_nonlinear_raw_acceptance_compute_count <> 2 ||
   length
     candle_fixed_nonlinear_combined_split_two_root_forest.
       fixed_nonlinear_split_forest_source_theorems <> 2 ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
       candle_fixed_nonlinear_combined_split_two_root_forest.
         fixed_nonlinear_split_forest_source_theorems) ||
   length candle_fixed_nonlinear_combined_split_two_root_axioms_after <>
     length candle_fixed_nonlinear_combined_split_two_root_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom
           candle_fixed_nonlinear_combined_split_two_root_axioms_before)
       candle_fixed_nonlinear_combined_split_two_root_axioms_after) then
  failwith "fixed nonlinear combined split: validation failed";;

print_endline
  "CANDLE_CV_FIXED_NONLINEAR_COMBINED_SPLIT_TWO_ROOT_OK DEVELOPMENT_NON_RELEASE raw_batches=2 cells=2 roots=2 assumptions=0 frees=0 axiom_growth=0";;

end;;
