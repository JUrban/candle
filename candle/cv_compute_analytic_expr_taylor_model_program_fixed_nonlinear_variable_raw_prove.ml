(* ========================================================================== *)
(* Proof-producing adapter for canonical raw fixed-nonlinear batches.         *)
(*                                                                            *)
(* Jobs are encoded directly as cval data.  One Kernel.compute result checks  *)
(* both their canonical representation and every numerical certificate, then  *)
(* the general raw-batch theorem supplies a closed logical acceptance result. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_sound;;

type candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_result_six = {
  fixed_nonlinear_variable_raw_prepared_source :
    candle_q_dim_analytic_jet_prepared_six;
  fixed_nonlinear_variable_raw_encoded_jobs_term : term;
  fixed_nonlinear_variable_raw_decoded_jobs_term : term;
  fixed_nonlinear_variable_raw_representation_theorem : thm;
  fixed_nonlinear_variable_raw_accept_theorem : thm;
};;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_prove_encoded_six
    prepared encoded_jobs =
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-raw-proof-preparation-begin";
  let decoded_jobs =
    mk_comb (`candle_cv_fso_variable_jobs_decode`,encoded_jobs) in
  let source_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        prepared.compile_theorem)
      prepared.program_representation in
  let concrete_call =
    list_mk_comb
      (`candle_cv_fsn_variable_raw_jobs_check`,
       [prepared.program_representation_term;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-raw-proof-preparation-end";
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-raw-batch-compute-begin";
  let concrete_compute =
    candle_q_dim_analytic_jet_compute
      candle_cv_fixed_nonlinear_compute_eqs concrete_call in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-raw-batch-compute-end";
  if not (aconv (rand (concl concrete_compute)) `Cexp_num 1`) then
    failwith "fixed nonlinear variable raw prover: raw batch rejected";
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-raw-batch-handoff-begin";
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL `candle_cv_fsn_variable_raw_jobs_check`)
      [source_program_encoding;REFL encoded_jobs] in
  let abstract_compute = TRANS call_encoding concrete_compute in
  let representation_theorem =
    MATCH_MP
      (SPECL
        [encoded_jobs;prepared.expression_term]
        candle_cv_fsn_variable_raw_jobs_check_representation_accept)
      abstract_compute in
  let accept_theorem =
    MATCH_MP
      (SPECL
        [encoded_jobs;prepared.expression_term]
        candle_cv_fsn_variable_raw_jobs_check_accept)
      abstract_compute in
  let accept_operator,accept_arguments =
    strip_comb (concl accept_theorem) in
  if hyp accept_theorem <> [] ||
     not
       (aconv accept_operator
          `candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept`) ||
     (match accept_arguments with
      | [actual_source;actual_jobs] ->
          not
            (aconv actual_source prepared.expression_term &&
             aconv actual_jobs decoded_jobs)
      | _ -> true) then
    failwith "fixed nonlinear variable raw prover: acceptance mismatch";
  let expected_representation =
    mk_eq
      (mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs`,
         decoded_jobs),
       encoded_jobs) in
  if hyp representation_theorem <> [] ||
     not (aconv (concl representation_theorem) expected_representation) then
    failwith "fixed nonlinear variable raw prover: representation mismatch";
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-raw-batch-handoff-end";
  {fixed_nonlinear_variable_raw_prepared_source = prepared;
   fixed_nonlinear_variable_raw_encoded_jobs_term = encoded_jobs;
   fixed_nonlinear_variable_raw_decoded_jobs_term = decoded_jobs;
   fixed_nonlinear_variable_raw_representation_theorem =
     representation_theorem;
   fixed_nonlinear_variable_raw_accept_theorem = accept_theorem};;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_prove_six
    prepared cells =
  if cells = [] then
    failwith "fixed nonlinear variable raw prover: empty batch";
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-raw-certificate-encoding-begin";
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-raw-certificate-encoding-end";
  candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_prove_encoded_six
    prepared encoded_jobs;;

end;;
