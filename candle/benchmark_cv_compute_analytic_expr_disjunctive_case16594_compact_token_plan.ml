(* Box-free compact token plan for the corrected case-16594 raw cells. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_axis_plan;;

let candle_disjunctive_case16594_compact_token_leaf =
  `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`;;

let candle_disjunctive_case16594_compact_token_glue axis =
  mk_comb
    (`Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue`,
     mk_small_numeral axis);;

type candle_disjunctive_case16594_compact_token_task =
  | Candle_disjunctive_case16594_compact_token_visit of
      candle_disjunctive_case16594_variable_axis_tree_shape
  | Candle_disjunctive_case16594_compact_token_emit_glue of int;;

let rec candle_disjunctive_case16594_compact_token_run
    tasks reversed_tokens leaf_count glue_count =
  match tasks with
  | [] -> reversed_tokens,leaf_count,glue_count
  | Candle_disjunctive_case16594_compact_token_visit shape :: remaining ->
      (match shape with
       | Candle_disjunctive_case16594_variable_axis_leaf _ ->
           candle_disjunctive_case16594_compact_token_run
             remaining
             (candle_disjunctive_case16594_compact_token_leaf ::
               reversed_tokens)
             (leaf_count + 1) glue_count
       | Candle_disjunctive_case16594_variable_axis_node (axis,left,right) ->
           candle_disjunctive_case16594_compact_token_run
             (Candle_disjunctive_case16594_compact_token_visit left ::
              Candle_disjunctive_case16594_compact_token_visit right ::
              Candle_disjunctive_case16594_compact_token_emit_glue axis ::
              remaining)
             reversed_tokens leaf_count glue_count)
  | Candle_disjunctive_case16594_compact_token_emit_glue axis :: remaining ->
      candle_disjunctive_case16594_compact_token_run
        remaining
        (candle_disjunctive_case16594_compact_token_glue axis ::
          reversed_tokens)
        leaf_count (glue_count + 1);;

let rec candle_disjunctive_case16594_compact_token_term
    reversed_tokens result =
  match reversed_tokens with
  | [] -> result
  | head :: tail ->
      candle_disjunctive_case16594_compact_token_term
        tail (mk_cons head result);;

let candle_disjunctive_case16594_compact_token_plan,
    candle_disjunctive_case16594_compact_token_leaf_count,
    candle_disjunctive_case16594_compact_token_glue_count =
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_TOKEN_PLAN event=begin";
  let reversed_tokens,leaf_count,glue_count =
    candle_disjunctive_case16594_compact_token_run
      [Candle_disjunctive_case16594_compact_token_visit
         (candle_disjunctive_case16594_variable_axis_plan ())]
      [] 0 0 in
  if leaf_count <> 875 || glue_count <> 874 ||
     length reversed_tokens <> 1749 then
    failwith "case16594 compact token plan: shape mismatch";
  let empty =
    mk_list ([],type_of candle_disjunctive_case16594_compact_token_leaf) in
  let token_term =
    candle_disjunctive_case16594_compact_token_term reversed_tokens empty in
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_TOKEN_PLAN event=end authenticated_leaves=860 leaf_tokens=875 glue_tokens=874";
  (fun () -> token_term),leaf_count,glue_count;;

print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_TOKEN_PLAN_OK DEVELOPMENT_NON_RELEASE";;

end;;
