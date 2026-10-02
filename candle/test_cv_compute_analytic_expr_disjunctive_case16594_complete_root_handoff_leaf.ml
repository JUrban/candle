(* Focused real-data control for the complete checker's singleton-root handoff. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_complete_root_handoff_leaf = struct

open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan;;

let rec candle_disjunctive_case16594_complete_root_handoff_first_leaf = function
  | Candle_disjunctive_case16594_variable_axis_leaf cell -> cell
  | Candle_disjunctive_case16594_variable_axis_node (_,left,_) ->
      candle_disjunctive_case16594_complete_root_handoff_first_leaf left;;

let _ =
  let axioms_before = axioms () in
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  let cell =
    candle_disjunctive_case16594_complete_root_handoff_first_leaf
      (candle_disjunctive_case16594_variable_axis_plan ()) in
  let leaf =
    `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf` in
  let tokens = mk_list ([leaf],type_of leaf) in
  let encoded_tokens =
    candle_q_dim_stable_program_cval_list [`Cexp_num 0`] in
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      [cell] in
  let call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check`,
       [prepared.program_representation_term;`Cexp_num 6`;
        encoded_tokens;encoded_jobs]) in
  let compute_theorem =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs ())
      call in
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_root_six
      prepared tokens encoded_tokens encoded_jobs compute_theorem in
  let stable = cell.variable_batch_stable_cell in
  let expected_boxes =
    candle_poly_fixture_q_boxes
      stable.stable_batch_lower stable.stable_batch_upper in
  let axioms_after = axioms () in
  if not (aconv result.variable_complete_root_boxes_term expected_boxes) ||
     hyp result.variable_complete_root_cell_theorem <> [] ||
     hyp result.variable_complete_root_source_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 complete root handoff leaf: validation failed";
  print_endline
    "CANDLE_CV_CASE16594_COMPLETE_ROOT_HANDOFF_LEAF_OK DEVELOPMENT_NON_RELEASE numerical_cells=1 token_items=1 active_roots=1 assumptions=0 axiom_growth=0";;

end;;
