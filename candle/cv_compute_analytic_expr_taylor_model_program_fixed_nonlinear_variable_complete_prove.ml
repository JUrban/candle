(* ========================================================================== *)
(* General-stack handoff for the one-verdict fixed-nonlinear checker.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_stable_program_data.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_prove = struct

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_sound;;

type candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_stack_result_six = {
  fixed_nonlinear_variable_complete_encoded_jobs_term : term;
  fixed_nonlinear_variable_complete_encoded_stack_term : term;
  fixed_nonlinear_variable_complete_compute_theorem : thm;
  fixed_nonlinear_variable_complete_stack_theorem : thm;
};;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_token_encoding
    tokens encoded_tokens =
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-complete-validation-begin";
  let token_call =
    mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens`,
       tokens) in
  let token_encoding =
    REWRITE_CONV
      [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def]
      token_call in
  if hyp token_encoding <> [] ||
     not (aconv (lhand (concl token_encoding)) token_call) ||
     not (aconv (rand (concl token_encoding)) encoded_tokens) then
    failwith "fixed nonlinear complete checker: token encoding mismatch";
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-complete-validation-end";
  token_encoding;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_with_encoding_six
    prepared tokens encoded_tokens encoded_jobs token_encoding
    concrete_compute =
  if aconv encoded_tokens `Cexp_num 0` ||
     aconv encoded_jobs `Cexp_num 0` then
    failwith "fixed nonlinear complete checker: empty certificate";
  let concrete_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check`,
       [prepared.program_representation_term;`Cexp_num 6`;
        encoded_tokens;encoded_jobs]) in
  let numerical,topology =
    candle_q_dim_stable_program_dest_cval_pair
      "fixed nonlinear complete reflected result"
      (rand (concl concrete_compute)) in
  let topology_success,topology_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "fixed nonlinear complete topology result" topology in
  let remaining_jobs,final_stack =
    candle_q_dim_stable_program_dest_cval_pair
      "fixed nonlinear complete topology payload" topology_payload in
  if hyp concrete_compute <> [] ||
     not (aconv (lhand (concl concrete_compute)) concrete_call) ||
     not (aconv numerical `Cexp_num 1`) ||
     not (aconv topology_success `Cexp_num 1`) ||
     not (aconv remaining_jobs `Cexp_num 0`) then
    failwith "fixed nonlinear complete checker: certificate rejected";
  let source_program_encoding =
    TRANS
      (AP_TERM `candle_cv_analytic_instruction_list`
        prepared.compile_theorem)
      prepared.program_representation in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-complete-handoff-begin";
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL
        `candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check`)
      [source_program_encoding;REFL `Cexp_num 6`;token_encoding;
       REFL encoded_jobs] in
  let abstract_compute = TRANS call_encoding concrete_compute in
  let soundness =
    REWRITE_RULE
      [candle_q_dim_analytic_jet_dim_six]
      (ISPECL
        [prepared.expression_term;`ARB:real^6`;tokens;encoded_jobs;
         final_stack]
        candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_stack_accept) in
  let premise = CONJ prepared.valid_theorem abstract_compute in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "fixed nonlinear complete checker: soundness premise mismatch";
  let stack_theorem = MP soundness premise in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-complete-handoff-end";
  if hyp stack_theorem <> [] then
    failwith "fixed nonlinear complete checker: unexpected assumptions";
  {fixed_nonlinear_variable_complete_encoded_jobs_term = encoded_jobs;
   fixed_nonlinear_variable_complete_encoded_stack_term = final_stack;
   fixed_nonlinear_variable_complete_compute_theorem = concrete_compute;
   fixed_nonlinear_variable_complete_stack_theorem = stack_theorem};;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_computed_stack_six
    prepared tokens encoded_tokens encoded_jobs concrete_compute =
  let token_encoding =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_token_encoding
      tokens encoded_tokens in
  candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_with_encoding_six
    prepared tokens encoded_tokens encoded_jobs token_encoding
    concrete_compute;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_stack_six
    prepared cells tokens encoded_tokens =
  if cells = [] then
    failwith "fixed nonlinear complete checker: empty certificate";
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-complete-certificate-encoding-begin";
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-complete-certificate-encoding-end";
  let token_encoding =
    candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_token_encoding
      tokens encoded_tokens in
  let concrete_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check`,
       [prepared.program_representation_term;`Cexp_num 6`;
        encoded_tokens;encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-complete-compute-begin";
  let concrete_compute =
    candle_q_dim_analytic_jet_compute
      (candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_compute_eqs ())
      concrete_call in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-variable-complete-compute-end";
  candle_q_dim_taylor_model_fixed_nonlinear_variable_complete_handoff_with_encoding_six
    prepared tokens encoded_tokens encoded_jobs token_encoding
    concrete_compute;;

print_endline
  "CANDLE_CV_FIXED_NONLINEAR_VARIABLE_COMPLETE_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
