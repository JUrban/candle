(* Unified fourth-batch forest sources: the retained split function-0 result *)
(* plus checkpointed, subtree-bounded function-1 batches.  DEVELOPMENT /    *)
(* NON-RELEASE.                                                             *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_split_function0_compute.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function1_state.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_forest_prove.ml";;

module Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_forests = struct

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_split_function0_compute;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function1_state;;
open Candle_cv_analytic_expr_disjunctive_component_bounded_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_forest_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let candle_disjunctive_fourth_bounded_logical_tokens tokens =
  mk_list
    (map candle_disjunctive_next_batch_logical_token tokens,
     type_of
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`);;

let candle_disjunctive_fourth_bounded_function0_forest =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_computed_forest_six
    candle_disjunctive_next_batch_prepared0
    (candle_disjunctive_fourth_bounded_logical_tokens
      candle_disjunctive_fourth_batch_tokens0)
    candle_disjunctive_fourth_split_encoded_tokens0
    candle_disjunctive_fourth_split_encoded_jobs0
    (candle_disjunctive_fourth_split_compute0_get ())
    candle_disjunctive_fourth_batch_expected_stack0;;

let candle_disjunctive_fourth_bounded_reflected_sources0 =
  candle_disjunctive_fourth_bounded_function0_forest.
    fixed_nonlinear_variable_complete_forest_source_theorems;;

let candle_disjunctive_fourth_bounded_sources0 =
  let rec convert components sources =
    match components,sources with
    | [],[] -> []
    | component::remaining_components,source::remaining_sources ->
        candle_disjunctive_component_bounded_source_pass
          candle_disjunctive_next_batch_prepared0.function_term
          source component.next_batch_component_domain ::
        convert remaining_components remaining_sources
    | _ -> failwith "fourth bounded forests: function0 source drift" in
  convert (rev candle_disjunctive_fourth_batch_components0)
    candle_disjunctive_fourth_bounded_reflected_sources0;;

let candle_disjunctive_fourth_bounded_sources1 =
  candle_disjunctive_fourth_bounded_f1_source_theorems ();;

if length candle_disjunctive_fourth_bounded_sources0 <>
     length candle_disjunctive_fourth_batch_components0 ||
   length candle_disjunctive_fourth_bounded_sources1 <>
     length candle_disjunctive_fourth_batch_components1 ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
       (candle_disjunctive_fourth_bounded_sources0 @
        candle_disjunctive_fourth_bounded_sources1)) then
  failwith "fourth bounded forests: final validation failed";;

print_endline
  ("CANDLE_CV_FOURTH_SIBLING_BATCH_FIXED_NONLINEAR_BOUNDED_FORESTS_OK" ^
   " DEVELOPMENT_NON_RELEASE roots=" ^
   string_of_int (length candle_disjunctive_fourth_batch_components) ^
   " function0_roots=" ^
   string_of_int (length candle_disjunctive_fourth_bounded_sources0) ^
   " function1_roots=" ^
   string_of_int (length candle_disjunctive_fourth_bounded_sources1) ^
   " assumptions=0 frees=0");;

end;;
