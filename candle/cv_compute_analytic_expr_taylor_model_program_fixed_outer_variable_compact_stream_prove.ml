(* ========================================================================== *)
(* Proof-producing adapter for the reflected compact topology stream.         *)
(*                                                                            *)
(* Raw numerical jobs and compact topology remain cval data through the       *)
(* executable check.  The correspondence theorem is used once at the end to  *)
(* recover the logical compact-run equation expected by the existing analytic *)
(* soundness theorem.                                                         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_prove = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;

type candle_q_dim_taylor_model_fixed_outer_variable_compact_reflected_result_six = {
  variable_compact_reflected_root_boxes_term : term;
  variable_compact_reflected_compute_theorem : thm;
  variable_compact_reflected_run_theorem : thm;
  variable_compact_reflected_source_theorem : thm;
};;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_reflected_source_six
    (raw_result:
      candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six)
    tokens encoded_tokens =
  let prepared = raw_result.variable_raw_prepared_source in
  let encoded_jobs = raw_result.variable_raw_encoded_jobs_term in
  let decoded_jobs = raw_result.variable_raw_decoded_jobs_term in
  let empty_stack =
    `[]:((((num#num)#num)#((num#num)#num))list)list` in
  let empty_jobs =
    `[]:((((num#num)#num)#((num#num)#num))list#
         ((((num#num)#num)#((num#num)#num))list#
          (((num#num)#num)#((num#num)#num))list))list` in
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-validation-begin";
  let expected_acceptance =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept`,
       [prepared.expression_term;decoded_jobs]) in
  if hyp raw_result.variable_raw_accept_theorem <> [] ||
     not (aconv (concl raw_result.variable_raw_accept_theorem)
       expected_acceptance) then
    failwith "fixed outer reflected compact prover: acceptance mismatch";
  let token_encoding_call =
    mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens`,
       tokens) in
  let token_encoding =
    REWRITE_CONV
      [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def]
      token_encoding_call in
  if not (aconv (rand (concl token_encoding)) encoded_tokens) then
    failwith "fixed outer reflected compact prover: token encoding mismatch";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-validation-end";

  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-jobs-representation-reuse-begin";
  let jobs_representation =
    raw_result.variable_raw_representation_theorem in
  let expected_jobs_representation =
    mk_eq
      (mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs`,
         decoded_jobs),
       encoded_jobs) in
  if hyp jobs_representation <> [] ||
     not (aconv (concl jobs_representation) expected_jobs_representation) then
    failwith "fixed outer reflected compact prover: job representation mismatch";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-jobs-representation-reuse-end";

  let reflected_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`,
       [`Cexp_num 6`;encoded_tokens;encoded_jobs;`Cexp_num 0`]) in
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-topology-compute-begin";
  let reflected_compute =
    Kernel.compute
      (COMPUTE_INIT_THMS,
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs)
      reflected_call in
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-topology-compute-end";
  let reflected_success,reflected_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "reflected compact result" (rand (concl reflected_compute)) in
  let reflected_remaining,reflected_stack =
    candle_q_dim_stable_program_dest_cval_pair
      "reflected compact payload" reflected_payload in
  let reflected_root,reflected_stack_tail =
    candle_q_dim_stable_program_dest_cval_pair
      "reflected compact stack" reflected_stack in
  if hyp reflected_compute <> [] ||
     not (aconv reflected_success `Cexp_num 1`) ||
     not (aconv reflected_remaining `Cexp_num 0`) ||
     not (aconv reflected_stack_tail `Cexp_num 0`) then
    failwith "fixed outer reflected compact prover: stream rejected";

  let root_boxes =
    mk_comb (`candle_cv_q_interval_list_decode`,reflected_root) in

  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-theorem-handoff-begin";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-correspondence-begin";
  let correspondence =
    SPECL
      [tokens;`6`;decoded_jobs;empty_stack]
      candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_correct in
  let stack_encoding =
    REWRITE_CONV [candle_cv_q_boxes_stack_def]
      (mk_comb (`candle_cv_q_boxes_stack`,empty_stack)) in
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL
        `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`)
      [REFL `Cexp_num 6`;token_encoding;jobs_representation;stack_encoding] in
  let correspondence_encoded =
    TRANS (SYM call_encoding) correspondence in
  if not (aconv (lhand (concl correspondence_encoded)) reflected_call) then
    failwith "fixed outer reflected compact prover: correspondence mismatch";
  let encoded_logical_result =
    TRANS (SYM correspondence_encoded) reflected_compute in
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-correspondence-end";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-result-decode-begin";
  let decoded_logical_result =
    AP_TERM
      `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode`
      encoded_logical_result in
  let run_theorem =
    REWRITE_RULE
      [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_roundtrip;
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_def;
       CONJUNCT1 candle_cv_fso_variable_jobs_decode_def;
       candle_cv_q_boxes_stack_decode_def;
       cexp_fst_def;cexp_snd_def;injectivity "cval"]
      decoded_logical_result in
  if hyp run_theorem <> [] then
    failwith "fixed outer reflected compact prover: result decode assumptions";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-result-decode-end";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-analytic-soundness-begin";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-soundness-instantiation-begin";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-soundness-dimension-specialization-begin";
  let soundness_dimension =
    REWRITE_RULE
      [candle_q_dim_analytic_jet_dim_six]
      (ISPECL
        [prepared.expression_term;`ARB:real^6`]
        candle_q_dim_taylor_model_fixed_outer_variable_compact_sound) in
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-soundness-dimension-specialization-end";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-soundness-data-instantiation-begin";
  let soundness =
    ISPECL [tokens;decoded_jobs;root_boxes] soundness_dimension in
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-soundness-data-instantiation-end";
  let premise =
    CONJ prepared.valid_theorem
      (CONJ raw_result.variable_raw_accept_theorem run_theorem) in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "fixed outer reflected compact prover: soundness mismatch";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-soundness-instantiation-end";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-soundness-match-begin";
  let cell_theorem = MATCH_MP soundness premise in
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-soundness-match-end";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-source-rewrite-begin";
  let source_theorem =
    REWRITE_RULE [m_cell_pass;prepared.source_theorem] cell_theorem in
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-source-rewrite-end";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-analytic-soundness-end";
  candle_q_dim_analytic_jet_profile_event
    "variable-compact-reflected-theorem-handoff-end";
  if hyp run_theorem <> [] || hyp source_theorem <> [] then
    failwith "fixed outer reflected compact prover: unexpected assumptions";
  {variable_compact_reflected_root_boxes_term = root_boxes;
   variable_compact_reflected_compute_theorem = reflected_compute;
   variable_compact_reflected_run_theorem = run_theorem;
   variable_compact_reflected_source_theorem = source_theorem};;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_COMPACT_STREAM_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
