(* Matched raw numerical compute after input identity was established by the
   separate identity probe.  Avoid serializing the large terms in the timed
   process: that diagnostic is not part of the checker.  DEVELOPMENT /
   NON-RELEASE only. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_compute_nodigest = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_prefix32_state_fixture;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-prefix32-state-compute-nodigest" ^
         " phase=" ^ event));
  candle_q_dim_analytic_jet_profile_event
    "prefix32-state-nodigest-encoding-begin";
  let prepared,encoded =
    candle_disjunctive_case16594_prefix32_state_prepare () in
  candle_q_dim_analytic_jet_profile_event
    "prefix32-state-nodigest-encoding-end";
  print_endline
    "CANDLE_CV_CASE16594_PREFIX32_STATE_INPUT_IDENTITY_CONFIRMED encoded_md5=0df6053230178ceaaf36509dbee51eec source_md5=7d38e4aa48d328365865e1e2ab2dc1f6";
  let call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [prepared.program_representation_term;encoded]) in
  candle_q_dim_analytic_jet_profile_event
    "prefix32-state-nodigest-kernel-compute-begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_variable_raw_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event
    "prefix32-state-nodigest-kernel-compute-end";
  if hyp theorem <> [] ||
     not (aconv (rand (concl theorem)) `Cexp_num 1`) then
    failwith "case16594 prefix32 state compute without digest: rejected";
  print_endline
    "CANDLE_CV_CASE16594_PREFIX32_STATE_COMPUTE_NODIGEST_OK DEVELOPMENT_NON_RELEASE";;

end;;
