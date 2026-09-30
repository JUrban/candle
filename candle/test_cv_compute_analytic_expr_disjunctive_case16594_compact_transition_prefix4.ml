(* Focused proof test for authenticated compact-stack token transitions. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16594_compact_stack_complete_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_compact_transition_prefix4 = struct

open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_compact_stack_complete_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan;;

let _ =
  let chunks =
    candle_disjunctive_case16594_compact_complete_split_chunks 4
      candle_disjunctive_case16594_variable_raw_plan_cells in
  let cells = hd chunks in
  let all_tokens =
    dest_list (candle_disjunctive_case16594_compact_token_plan ()) in
  let segment,_ =
    candle_disjunctive_case16594_compact_complete_take_token_segment
      (length cells) [] all_tokens in
  let final_state =
    candle_disjunctive_case16594_compact_complete_prove_chunks
      candle_disjunctive_case16594_engine_state.family_engine_prepared
      1 segment [cells] in
  if hyp final_state.variable_compact_state_pass_theorem <> [] then
    failwith "case16594 compact transition prefix4: assumptions";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_TRANSITION_PREFIX4_OK" ^
     " numerical_cells=4 token_items=" ^ string_of_int (length segment) ^
     " active_roots=" ^
       string_of_int
         (length
           (dest_list final_state.variable_compact_state_stack_term)) ^
     " max_transition_tokens=2 DEVELOPMENT_NON_RELEASE");;

end;;
