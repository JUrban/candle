(* Axis-preserving overlay for the already-built corrected raw cell plan. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan = struct

open Candle_cv_analytic_expr_disjunctive_case16594_plan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;

type candle_disjunctive_case16594_variable_axis_tree_shape =
  | Candle_disjunctive_case16594_variable_axis_leaf of
      candle_q_dim_taylor_model_fixed_outer_variable_batch_cell_six
  | Candle_disjunctive_case16594_variable_axis_node of
      int * candle_disjunctive_case16594_variable_axis_tree_shape *
      candle_disjunctive_case16594_variable_axis_tree_shape;;

let rec candle_disjunctive_case16594_variable_axis_plan_build
    next_leaf cells tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 1 || raw_flag then
        failwith "case16594 variable axis plan: pass selection drift";
      let leaf_index = next_leaf in
      if List.mem leaf_index
           candle_disjunctive_case16594_variable_raw_split_leaves then
        (match cells with
         | left :: right :: remaining ->
             Candle_disjunctive_case16594_variable_axis_node
               (1,
                Candle_disjunctive_case16594_variable_axis_leaf left,
                Candle_disjunctive_case16594_variable_axis_leaf right),
             remaining,leaf_index + 1,2,1
         | _ -> failwith "case16594 variable axis plan: short split cells")
      else
        (match cells with
         | cell :: remaining ->
             Candle_disjunctive_case16594_variable_axis_leaf cell,
             remaining,leaf_index + 1,1,0
         | [] -> failwith "case16594 variable axis plan: short leaf cells")
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "case16594 variable axis plan: convex node";
      let axis = split_index + 1 in
      let left_shape,after_left_cells,after_left,left_leaves,left_glues =
        candle_disjunctive_case16594_variable_axis_plan_build
          next_leaf cells left in
      let right_shape,remaining,after_right,right_leaves,right_glues =
        candle_disjunctive_case16594_variable_axis_plan_build
          after_left after_left_cells right in
      Candle_disjunctive_case16594_variable_axis_node
        (axis,left_shape,right_shape),
      remaining,after_right,left_leaves + right_leaves,
      1 + left_glues + right_glues
  | P_result_mono _ ->
      failwith "case16594 variable axis plan: monotonicity node"
  | P_result_ref _ ->
      failwith "case16594 variable axis plan: reference node";;

let candle_disjunctive_case16594_variable_axis_plan,
    candle_disjunctive_case16594_variable_axis_plan_leaf_count,
    candle_disjunctive_case16594_variable_axis_plan_glue_count =
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_AXIS_PLAN event=begin";
  let shape,remaining,next_leaf,leaf_count,glue_count =
    candle_disjunctive_case16594_variable_axis_plan_build 0
      candle_disjunctive_case16594_variable_raw_plan_cells
      candle_disjunctive_case16594_plan_precision_tree in
  if remaining <> [] || next_leaf <> 860 || leaf_count <> 875 ||
     glue_count <> 874 then
    failwith "case16594 variable axis plan: shape mismatch";
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_AXIS_PLAN event=end authenticated_leaves=860 numerical_cells=875 glue_nodes=874";
  (fun () -> shape),leaf_count,glue_count;;

print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_AXIS_PLAN_OK DEVELOPMENT_NON_RELEASE";;

end;;
