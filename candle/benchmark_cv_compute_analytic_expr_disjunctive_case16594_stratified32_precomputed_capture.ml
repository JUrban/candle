(* Compute a stratified genuine 32-cell verdict before loading downstream
   handoff support.  The large inputs remain local during Kernel.compute.
   DEVELOPMENT / NON-RELEASE only. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_stratified32_state_fixture.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_stratified32_precomputed_capture = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_stratified32_state_fixture;;

type candle_disjunctive_case16594_stratified32_precomputed_capture = {
  stratified32_precomputed_prepared : candle_q_dim_analytic_jet_prepared_six;
  stratified32_precomputed_encoded_jobs : term;
  stratified32_precomputed_theorem : thm;
};;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-stratified32-precomputed" ^
         " phase=" ^ event));;

let candle_disjunctive_case16594_stratified32_precomputed_slot :
    candle_disjunctive_case16594_stratified32_precomputed_capture option ref =
  ref None;;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "stratified32-precomputed-encoding-begin";
  let prepared,encoded_jobs =
    candle_disjunctive_case16594_stratified32_state_prepare () in
  candle_q_dim_analytic_jet_profile_event
    "stratified32-precomputed-encoding-end";
  let call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [prepared.program_representation_term;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "stratified32-precomputed-kernel-compute-begin";
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_cv_fso_variable_raw_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event
    "stratified32-precomputed-kernel-compute-end";
  if hyp theorem <> [] ||
     not (aconv (concl theorem) (mk_eq (call,`Cexp_num 1`))) then
    failwith "case16594 stratified32 precomputed capture: theorem mismatch";
  candle_disjunctive_case16594_stratified32_precomputed_slot :=
    Some
      ({stratified32_precomputed_prepared = prepared;
        stratified32_precomputed_encoded_jobs = encoded_jobs;
        stratified32_precomputed_theorem = theorem});
  print_endline
    "CANDLE_CV_CASE16594_STRATIFIED32_PRECOMPUTED_CAPTURE_OK DEVELOPMENT_NON_RELEASE";;

let candle_disjunctive_case16594_stratified32_precomputed () =
  match !candle_disjunctive_case16594_stratified32_precomputed_slot with
  | Some captured -> captured
  | None -> failwith "case16594 stratified32 precomputed capture: unavailable";;

end;;
