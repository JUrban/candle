(* ========================================================================== *)
(* Genuine case-16594 subtree from two independently checked raw batches.    *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_token_subtree.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_combine_prove.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_token_subtree_chunked = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_combine_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_token_subtree;;

let _ =
  let axioms_before = axioms () in
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-variable-token-subtree-chunked" ^
         " phase=" ^ event));
  let left_cell =
    candle_disjunctive_case16594_variable_token_nth 0
      candle_disjunctive_case16594_variable_token_cells
  and right_cell =
    candle_disjunctive_case16594_variable_token_nth 1
      candle_disjunctive_case16594_variable_token_cells in
  let left =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
      candle_disjunctive_case16594_engine_state.family_engine_prepared
      [left_cell] in
  let right =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
      candle_disjunctive_case16594_engine_state.family_engine_prepared
      [right_cell] in
  let acceptance =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_combine
      [left;right] in
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_acceptance_source_six
      acceptance candle_disjunctive_case16594_variable_token_stream in
  let theorem = result.variable_token_core_source_theorem in
  let digest = Digest.to_hex (Digest.string (string_of_thm theorem)) in
  let axioms_after = axioms () in
  if acceptance.variable_raw_acceptance_compute_count <> 2 ||
     hyp theorem <> [] ||
     digest <> "d88ef874dd7e0fdf114cb999e0bfcd55" ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 variable token chunked subtree: validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_TOKEN_SUBTREE_CHUNKED_RESULT" ^
     " raw_batches=2 numerical_cells=2 leaf_tokens=2 glue_tokens=1" ^
     " combined_root_theorem=1 assumptions=0 theorem_digest=" ^ digest);
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_TOKEN_SUBTREE_CHUNKED_OK DEVELOPMENT_NON_RELEASE";;

end;;
