(* A precomputed handoff must reject a closed theorem about the wrong result
   before introducing a certificate definition.  DEVELOPMENT / NON-RELEASE. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_postcompute_named_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_precomputed_handoff_reject = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_postcompute_named_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture;;

let _ =
  let prepared,encoded_jobs =
    candle_disjunctive_case16594_prefix32_state_prepare () in
  let call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [prepared.program_representation_term;encoded_jobs]) in
  let requested_name =
    `candle_disjunctive_case16594_rejected_precomputed_jobs:cval` in
  let rejects theorem =
    try
      let _ =
        candle_q_dim_taylor_model_fixed_outer_variable_postcompute_named_handoff_computed_six
          prepared requested_name encoded_jobs theorem in
      false
    with Failure message ->
      message =
        "fixed outer postcompute named prover: computed theorem mismatch" in
  let expected = mk_eq (call,`Cexp_num 1`) in
  if not (rejects (REFL call)) then
    failwith "case16594 precomputed handoff: wrong result was accepted";
  if not (rejects (ASSUME expected)) then
    failwith "case16594 precomputed handoff: open theorem was accepted";
  print_endline
    "CANDLE_CV_CASE16594_PRECOMPUTED_HANDOFF_REJECT_OK DEVELOPMENT_NON_RELEASE";;

end;;
