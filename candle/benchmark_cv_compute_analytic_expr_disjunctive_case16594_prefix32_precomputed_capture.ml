(* Compute the genuine prefix-32 verdict before loading downstream handoff
   support.  The record is allocated only after Kernel.compute returns, so the
   large inputs remain local while evaluation is active.  DEVELOPMENT /
   NON-RELEASE only. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_precomputed_capture = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture;;

type candle_disjunctive_case16594_prefix32_precomputed_capture = {
  prefix32_precomputed_prepared : candle_q_dim_analytic_jet_prepared_six;
  prefix32_precomputed_encoded_jobs : term;
  prefix32_precomputed_theorem : thm;
};;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-prefix32-precomputed" ^
         " phase=" ^ event));;

let candle_disjunctive_case16594_prefix32_precomputed =
  candle_q_dim_analytic_jet_profile_event
    "prefix32-precomputed-encoding-begin";
  let prepared,encoded_jobs =
    candle_disjunctive_case16594_prefix32_state_prepare () in
  candle_q_dim_analytic_jet_profile_event
    "prefix32-precomputed-encoding-end";
  let call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [prepared.program_representation_term;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "prefix32-precomputed-kernel-compute-begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_variable_raw_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event
    "prefix32-precomputed-kernel-compute-end";
  if hyp theorem <> [] ||
     not (aconv (concl theorem) (mk_eq (call,`Cexp_num 1`))) then
    failwith "case16594 prefix32 precomputed capture: theorem mismatch";
  {prefix32_precomputed_prepared = prepared;
   prefix32_precomputed_encoded_jobs = encoded_jobs;
   prefix32_precomputed_theorem = theorem};;

let _ =
  print_endline
    "CANDLE_CV_CASE16594_PREFIX32_PRECOMPUTED_CAPTURE_OK DEVELOPMENT_NON_RELEASE";;

end;;
