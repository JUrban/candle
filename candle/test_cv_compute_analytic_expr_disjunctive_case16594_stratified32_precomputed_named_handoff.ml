(* Authenticate and compactly name a stratified 32-cell verdict computed
   before loading this adapter.  DEVELOPMENT / NON-RELEASE only. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_stratified32_precomputed_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_postcompute_named_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_stratified32_precomputed_named_handoff = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_postcompute_named_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_stratified32_state_fixture;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_stratified32_precomputed_capture;;

let _ =
  let axioms_before = axioms () in
  let captured =
    candle_disjunctive_case16594_stratified32_precomputed () in
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_postcompute_named_handoff_computed_six
      captured.stratified32_precomputed_prepared
      `candle_disjunctive_case16594_stratified32_precomputed_jobs:cval`
      captured.stratified32_precomputed_encoded_jobs
      captured.stratified32_precomputed_theorem in
  let raw_result = result.variable_postcompute_named_raw_result in
  let axioms_after = axioms () in
  if hyp result.variable_postcompute_named_jobs_definition <> [] ||
     hyp raw_result.variable_raw_representation_theorem <> [] ||
     hyp raw_result.variable_raw_accept_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 stratified32 precomputed handoff: validation failed";
  print_endline
    ("CANDLE_CV_CASE16594_STRATIFIED32_PRECOMPUTED_NAMED_HANDOFF_RESULT" ^
     " cells=32 plan_cells=875 first=0 last=874 assumptions=0" ^
     " axiom_growth=0 indices=" ^
     String.concat ","
       (map string_of_int candle_disjunctive_case16594_stratified32_indices));
  print_endline
    "CANDLE_CV_CASE16594_STRATIFIED32_PRECOMPUTED_NAMED_HANDOFF_OK DEVELOPMENT_NON_RELEASE";;

end;;
