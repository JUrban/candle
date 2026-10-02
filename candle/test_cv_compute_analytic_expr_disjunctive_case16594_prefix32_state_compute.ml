(* Matched raw numerical compute used to distinguish checker-state overhead
   from genuine input drift.  DEVELOPMENT / NON-RELEASE only. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_compute = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-prefix32-state-compute" ^
         " phase=" ^ event));
  candle_q_dim_analytic_jet_profile_event
    "prefix32-state-encoding-begin";
  let prepared,encoded =
    candle_disjunctive_case16594_prefix32_state_prepare () in
  candle_q_dim_analytic_jet_profile_event
    "prefix32-state-encoding-end";
  print_endline
    ("CANDLE_CV_CASE16594_PREFIX32_STATE_INPUT" ^
     " encoded_md5=" ^
     candle_disjunctive_case16594_prefix32_state_term_digest encoded ^
     " source_md5=" ^
     candle_disjunctive_case16594_prefix32_state_term_digest
       prepared.program_representation_term);
  let call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [prepared.program_representation_term;encoded]) in
  candle_q_dim_analytic_jet_profile_event
    "prefix32-state-kernel-compute-begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_variable_raw_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event
    "prefix32-state-kernel-compute-end";
  if hyp theorem <> [] ||
     not (aconv (rand (concl theorem)) `Cexp_num 1`) then
    failwith "case16594 prefix32 state compute: rejected";
  print_endline
    "CANDLE_CV_CASE16594_PREFIX32_STATE_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
