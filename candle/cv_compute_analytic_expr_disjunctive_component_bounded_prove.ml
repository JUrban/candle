(* Bounded reflected proof of one uniform-function disjunctive component.     *)
(* Large component trees are cut only at authenticated split nodes.  Each    *)
(* bounded subtree uses the ordinary reflected numerical/topology checker;   *)
(* the existing Flyspeck split theorem reconstructs the original component. *)

needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch_forest_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_combined_split_prove.ml";;
needs "candle/cv_compute_flyspeck_nonlinear_term_order_compat.ml";;

module Candle_cv_analytic_expr_disjunctive_component_bounded_prove = struct

open M_verifier;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_flyspeck_nonlinear_term_order_compat;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_combine_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_combined_split_prove;;

type candle_disjunctive_component_bounded_result = {
  component_bounded_list_theorem : thm;
  component_bounded_numerical_batches : int;
  component_bounded_reflected_subtrees : int;
  component_bounded_max_subtree_cells : int;
};;

let rec candle_disjunctive_component_bounded_shape_cells = function
  | Candle_disjunctive_next_batch_leaf (_,_,cell) -> [cell]
  | Candle_disjunctive_next_batch_node (_,_,left,right) ->
      candle_disjunctive_component_bounded_shape_cells left @
      candle_disjunctive_component_bounded_shape_cells right;;

let rec candle_disjunctive_component_bounded_shape_tokens = function
  | Candle_disjunctive_next_batch_leaf _ ->
      [Candle_disjunctive_next_batch_token_leaf]
  | Candle_disjunctive_next_batch_node (axis,_,left,right) ->
      candle_disjunctive_component_bounded_shape_tokens left @
      candle_disjunctive_component_bounded_shape_tokens right @
      [Candle_disjunctive_next_batch_token_glue axis];;

let candle_disjunctive_component_bounded_encoded_tokens tokens =
  candle_q_dim_stable_program_cval_list
    (map candle_disjunctive_next_batch_encode_token tokens);;

let candle_disjunctive_component_bounded_logical_tokens tokens =
  mk_list
    (map candle_disjunctive_next_batch_logical_token tokens,
     type_of
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`);;

let candle_disjunctive_component_bounded_box domain =
  let lower,upper = candle_disjunctive_fixed_outer_domain_bounds domain in
  candle_poly_fixture_q_boxes lower upper;;

let candle_disjunctive_component_bounded_root_decode root_box =
  let theorem =
    REWRITE_CONV
      [candle_cv_q_interval_list_decode_def;
       candle_cv_q_interval_decode_def;candle_cv_q_decode_def;
       candle_cv_lc_z_decode_def;candle_cv_lc_num_decode_def;
       cexp_fst_def;cexp_snd_def;FST;SND]
      root_box in
  if hyp theorem <> [] ||
     not (aconv (lhand (concl theorem)) root_box) then
    failwith "bounded component: root decode mismatch";
  theorem;;

let candle_disjunctive_component_bounded_source_pass
    function_term source_theorem domain =
  let logical_source =
    REWRITE_RULE
      [candle_cv_q_interval_list_decode_def;
       candle_cv_q_interval_decode_def;candle_cv_q_decode_def;
       candle_cv_lc_z_decode_def;candle_cv_lc_num_decode_def;
       cexp_fst_def;cexp_snd_def;FST;SND]
      source_theorem in
  let expected_lower,expected_upper =
    candle_disjunctive_fixed_outer_domain_bounds domain in
  candle_reflected_nl_source_pass_with function_term
    (fun actual_lower actual_upper ->
      if not
          (candle_disjunctive_fixed_outer_aconv_lists
             actual_lower expected_lower &&
           candle_disjunctive_fixed_outer_aconv_lists
             actual_upper expected_upper) then
        failwith "bounded component: source handoff domain drift";
      logical_source)
    domain;;

let candle_disjunctive_component_bounded_leaf_prove
    prepared cells tokens domain =
  let raw =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_prove_six
      prepared cells in
  let acceptance =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_acceptance_combine
      [raw] in
  let forest =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_combined_split_forest_six
      acceptance
      (candle_disjunctive_component_bounded_logical_tokens tokens)
      (candle_disjunctive_component_bounded_encoded_tokens tokens)
      [candle_disjunctive_component_bounded_box domain] in
  match forest.fixed_nonlinear_split_forest_root_boxes,
        forest.fixed_nonlinear_split_forest_source_theorems with
  | [root_box],[source_theorem] ->
      let root_decode =
        candle_disjunctive_component_bounded_root_decode root_box in
      if not
          (aconv (rand (concl root_decode))
             (candle_disjunctive_component_bounded_box domain)) then
        failwith "bounded component: decoded root box drift";
      let logical_source = REWRITE_RULE [root_decode] source_theorem in
      let list_theorem =
        candle_disjunctive_component_bounded_source_pass
          prepared.function_term logical_source domain in
      if hyp source_theorem <> [] || hyp logical_source <> [] ||
         hyp list_theorem <> [] ||
         frees (concl list_theorem) <> [] then
        failwith "bounded component: open reflected subtree theorem";
      {component_bounded_list_theorem = list_theorem;
       component_bounded_numerical_batches = 1;
       component_bounded_reflected_subtrees = 1;
       component_bounded_max_subtree_cells = length cells}
  | _ -> failwith "bounded component: reflected subtree cardinality";;

let rec candle_disjunctive_component_bounded_shape_prove
    prepared cell_limit shape =
  let cells = candle_disjunctive_component_bounded_shape_cells shape in
  let cell_count = length cells in
  if cell_count <= cell_limit then
    candle_disjunctive_component_bounded_leaf_prove
      prepared cells
      (candle_disjunctive_component_bounded_shape_tokens shape)
      (candle_disjunctive_next_batch_shape_domain shape)
  else
    match shape with
    | Candle_disjunctive_next_batch_leaf _ ->
        failwith "bounded component: oversized leaf"
    | Candle_disjunctive_next_batch_node (axis,_,left,right) ->
        let left_result =
          candle_disjunctive_component_bounded_shape_prove
            prepared cell_limit left in
        let right_result =
          candle_disjunctive_component_bounded_shape_prove
            prepared cell_limit right in
        let appended =
          M_verifier.m_glue_cells_list 6 axis
            left_result.component_bounded_list_theorem
            right_result.component_bounded_list_theorem in
        let list_theorem =
          candle_nonlinear_merge_m_cell_list_pass 6 appended in
        if hyp list_theorem <> [] || frees (concl list_theorem) <> [] then
          failwith "bounded component: open reconstructed theorem";
        {component_bounded_list_theorem = list_theorem;
         component_bounded_numerical_batches =
           left_result.component_bounded_numerical_batches +
           right_result.component_bounded_numerical_batches;
         component_bounded_reflected_subtrees =
           left_result.component_bounded_reflected_subtrees +
           right_result.component_bounded_reflected_subtrees;
         component_bounded_max_subtree_cells =
           max left_result.component_bounded_max_subtree_cells
             right_result.component_bounded_max_subtree_cells};;

let candle_disjunctive_component_bounded_prove
    prepared cell_limit component =
  if cell_limit <= 0 then failwith "bounded component: invalid cell limit";
  let result =
    candle_disjunctive_component_bounded_shape_prove
      prepared cell_limit component.next_batch_component_shape in
  if result.component_bounded_max_subtree_cells > cell_limit then
    failwith "bounded component: subtree limit drift";
  result;;

print_endline
  "CANDLE_CV_DISJUNCTIVE_COMPONENT_BOUNDED_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
