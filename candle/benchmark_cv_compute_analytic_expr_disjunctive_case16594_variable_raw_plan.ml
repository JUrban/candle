(* Reusable 875-cell plan for the complete real case-16594 raw certificate. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan = struct

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_fixture;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_leaf_grouping;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;

type candle_disjunctive_case16594_variable_raw_tree_shape =
  | Candle_disjunctive_case16594_variable_raw_leaf of
      candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six
  | Candle_disjunctive_case16594_variable_raw_node of
      candle_disjunctive_case16594_variable_raw_tree_shape *
      candle_disjunctive_case16594_variable_raw_tree_shape;;

let candle_disjunctive_case16594_variable_raw_split_leaves =
  [388;455;459;465;473;477;485;491;560;574;578;582;750;752;767];;

let candle_disjunctive_case16594_variable_raw_cell domain =
  let lower,upper = candle_disjunctive_fixed_outer_domain_bounds domain in
  let center =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_disjunctive_case16594_engine_state.family_engine_point_plan
      lower upper in
  {variable_batch_box_intervals =
     map (candle_disjunctive_fixed_outer_widen 5 4) center;
   variable_batch_stable_cell =
     {stable_batch_center_intervals = center;
      stable_batch_lower = lower;
      stable_batch_upper = upper}};;

let rec candle_disjunctive_case16594_variable_raw_shape_build
    next_leaf domain tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 1 || raw_flag then
        failwith "case16594 variable raw plan: pass selection drift";
      let leaf_index = next_leaf in
      if List.mem leaf_index
           candle_disjunctive_case16594_variable_raw_split_leaves then
        let left_domain,right_domain =
          M_verifier.split_domain 6 6 1 domain in
        Candle_disjunctive_case16594_variable_raw_node
          (Candle_disjunctive_case16594_variable_raw_leaf
             (candle_disjunctive_case16594_variable_raw_cell left_domain),
           Candle_disjunctive_case16594_variable_raw_leaf
             (candle_disjunctive_case16594_variable_raw_cell right_domain)),
        leaf_index + 1
      else
        Candle_disjunctive_case16594_variable_raw_leaf
          (candle_disjunctive_case16594_variable_raw_cell domain),
        leaf_index + 1
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "case16594 variable raw plan: convex node";
      let axis = split_index + 1 in
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 axis domain in
      let left_shape,after_left =
        candle_disjunctive_case16594_variable_raw_shape_build
          next_leaf left_domain left in
      let right_shape,after_right =
        candle_disjunctive_case16594_variable_raw_shape_build
          after_left right_domain right in
      Candle_disjunctive_case16594_variable_raw_node
        (left_shape,right_shape),after_right
  | P_result_mono _ ->
      failwith "case16594 variable raw plan: monotonicity node"
  | P_result_ref _ ->
      failwith "case16594 variable raw plan: reference node";;

let rec candle_disjunctive_case16594_variable_raw_shape_cells = function
  | Candle_disjunctive_case16594_variable_raw_leaf cell -> [cell]
  | Candle_disjunctive_case16594_variable_raw_node (left,right) ->
      candle_disjunctive_case16594_variable_raw_shape_cells left @
      candle_disjunctive_case16594_variable_raw_shape_cells right;;

let rec candle_disjunctive_case16594_variable_raw_shape_counts = function
  | Candle_disjunctive_case16594_variable_raw_leaf _ -> 1,0
  | Candle_disjunctive_case16594_variable_raw_node (left,right) ->
      let left_leaves,left_nodes =
        candle_disjunctive_case16594_variable_raw_shape_counts left and
          right_leaves,right_nodes =
            candle_disjunctive_case16594_variable_raw_shape_counts right in
      left_leaves + right_leaves,1 + left_nodes + right_nodes;;

let candle_disjunctive_case16594_variable_raw_plan_shape,
    candle_disjunctive_case16594_variable_raw_plan_cells =
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_PLAN event=begin";
  let shape,next_leaf =
    candle_disjunctive_case16594_variable_raw_shape_build
      0 candle_disjunctive_case16594_root_domain
      candle_disjunctive_case16594_plan_precision_tree in
  let cells =
    candle_disjunctive_case16594_variable_raw_shape_cells shape in
  let leaf_count,node_count =
    candle_disjunctive_case16594_variable_raw_shape_counts shape in
  if next_leaf <> 860 || leaf_count <> 875 || node_count <> 874 ||
     length cells <> 875 then
    failwith "case16594 variable raw plan: shape mismatch";
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_PLAN event=end authenticated_leaves=860 numerical_cells=875 glue_nodes=874";
  shape,cells;;

print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_PLAN_OK DEVELOPMENT_NON_RELEASE";;

end;;
