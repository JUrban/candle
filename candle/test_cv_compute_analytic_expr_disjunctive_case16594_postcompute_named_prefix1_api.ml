(* Focused regression for the existing compute-and-name API after splitting
   out the precomputed theorem handoff.  DEVELOPMENT / NON-RELEASE only. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_postcompute_named_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_postcompute_named_prefix1_api = struct

open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_postcompute_named_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;

let _ =
  let axioms_before = axioms () in
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  let cells =
    match candle_disjunctive_case16594_variable_raw_plan_cells with
    | first :: _ -> [first]
    | [] -> failwith "case16594 postcompute prefix1 API: empty plan" in
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_postcompute_named_prove_six
      prepared `candle_disjunctive_case16594_postcompute_prefix1_api_jobs:cval`
      cells in
  let raw_result = result.variable_postcompute_named_raw_result in
  let axioms_after = axioms () in
  if hyp result.variable_postcompute_named_jobs_definition <> [] ||
     hyp raw_result.variable_raw_representation_theorem <> [] ||
     hyp raw_result.variable_raw_accept_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 postcompute prefix1 API: validation failed";
  print_endline
    "CANDLE_CV_CASE16594_POSTCOMPUTE_NAMED_PREFIX1_API_OK DEVELOPMENT_NON_RELEASE";;

end;;
