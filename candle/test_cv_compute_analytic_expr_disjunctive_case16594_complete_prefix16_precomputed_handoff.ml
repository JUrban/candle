(* ========================================================================== *)
(* Late proof handoff for the lean genuine prefix-16 complete-checker verdict.*)
(* DEVELOPMENT / NON-RELEASE only.                                           *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_prefix16_precomputed_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_complete_prefix16_precomputed_handoff = struct

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_complete_prefix16_precomputed_capture;;

let candle_disjunctive_case16594_complete_prefix16_logical_token = function
  | Candle_disjunctive_case16594_complete_prefix16_leaf ->
      `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf`
  | Candle_disjunctive_case16594_complete_prefix16_glue axis ->
      mk_comb
        (`Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue`,
         mk_small_numeral axis);;

let rec candle_disjunctive_case16594_complete_prefix16_handoff_stack_length
    encoded =
  if aconv encoded `Cexp_num 0` then 0
  else
    let _,tail =
      candle_q_dim_stable_program_dest_cval_pair
        "case16594 complete prefix16 handoff stack" encoded in
    1 +
    candle_disjunctive_case16594_complete_prefix16_handoff_stack_length tail;;

let _ =
  let axioms_before = axioms () in
  let captured =
    candle_disjunctive_case16594_complete_prefix16_precomputed () in
  let token_items =
    map candle_disjunctive_case16594_complete_prefix16_logical_token
      captured.complete_prefix16_precomputed_token_data in
  let leaf =
    `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf` in
  let tokens = mk_list (token_items,type_of leaf) in
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_stack_six
      captured.complete_prefix16_precomputed_prepared tokens
      captured.complete_prefix16_precomputed_encoded_tokens
      captured.complete_prefix16_precomputed_encoded_jobs
      captured.complete_prefix16_precomputed_theorem in
  let active_roots =
    candle_disjunctive_case16594_complete_prefix16_handoff_stack_length
      result.variable_complete_encoded_stack_term in
  let axioms_after = axioms () in
  if length token_items <> 29 || active_roots <> 3 ||
     captured.complete_prefix16_precomputed_active_roots <> active_roots ||
     hyp result.variable_complete_compute_theorem <> [] ||
     hyp result.variable_complete_stack_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 complete prefix16 precomputed handoff: validation failed";
  print_endline
    "CANDLE_CV_CASE16594_COMPLETE_PREFIX16_PRECOMPUTED_HANDOFF_RESULT numerical_cells=16 token_items=29 active_roots=3 assumptions=0 axiom_growth=0";
  print_endline
    "CANDLE_CV_CASE16594_COMPLETE_PREFIX16_PRECOMPUTED_HANDOFF_OK DEVELOPMENT_NON_RELEASE";;

end;;
