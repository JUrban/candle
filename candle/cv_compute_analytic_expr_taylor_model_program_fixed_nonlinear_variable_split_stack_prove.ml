(* General split numerical/topology handoff for fixed-nonlinear raw batches.  *)
(* Each numerical batch and topology segment is checked by Kernel.compute;   *)
(* the existing representation and compact-run theorems supply soundness.    *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_compact_stack_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_stack_prove = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_compact_stack_sound;;

type candle_q_dim_taylor_model_fixed_nonlinear_variable_split_stack_result_six = {
  fixed_nonlinear_split_encoded_stack_term : term;
  fixed_nonlinear_split_logical_stack_term : term;
  fixed_nonlinear_split_topology_compute_theorem : thm;
  fixed_nonlinear_split_run_theorem : thm;
  fixed_nonlinear_split_stack_theorem : thm;
};;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_split_stack_six
    (raw_result:
      candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_result_six)
    tokens encoded_tokens =
  let prepared = raw_result.fixed_nonlinear_variable_raw_prepared_source in
  let encoded_jobs = raw_result.fixed_nonlinear_variable_raw_encoded_jobs_term in
  let decoded_jobs = raw_result.fixed_nonlinear_variable_raw_decoded_jobs_term in
  let empty_stack =
    `[]:((((num#num)#num)#((num#num)#num))list)list` in
  let empty_jobs =
    `[]:((((num#num)#num)#((num#num)#num))list#
         ((((num#num)#num)#((num#num)#num))list#
          (((num#num)#num)#((num#num)#num))list))list` in
  let expected_acceptance =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept`,
       [prepared.expression_term;decoded_jobs]) in
  if hyp raw_result.fixed_nonlinear_variable_raw_accept_theorem <> [] ||
     not
       (aconv
         (concl raw_result.fixed_nonlinear_variable_raw_accept_theorem)
         expected_acceptance) then
    failwith "fixed nonlinear split: numerical acceptance mismatch";
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
     not (aconv (rand (concl token_encoding)) encoded_tokens) then
    failwith "fixed nonlinear split: token encoding mismatch";
  let jobs_representation =
    raw_result.fixed_nonlinear_variable_raw_representation_theorem in
  let expected_jobs_representation =
    mk_eq
      (mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs`,decoded_jobs),
       encoded_jobs) in
  if hyp jobs_representation <> [] ||
     not (aconv (concl jobs_representation) expected_jobs_representation) then
    failwith "fixed nonlinear split: job representation mismatch";
  let reflected_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`,
       [`Cexp_num 6`;encoded_tokens;encoded_jobs;`Cexp_num 0`]) in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-split-topology-compute-begin";
  let reflected_compute =
    candle_q_dim_analytic_jet_compute
      candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs
      reflected_call in
  candle_q_dim_analytic_jet_profile_event
    "fixed-nonlinear-split-topology-compute-end";
  let reflected_success,reflected_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "fixed nonlinear split topology result" (rand (concl reflected_compute)) in
  let reflected_remaining,reflected_stack =
    candle_q_dim_stable_program_dest_cval_pair
      "fixed nonlinear split topology payload" reflected_payload in
  if not (aconv reflected_success `Cexp_num 1`) ||
     not (aconv reflected_remaining `Cexp_num 0`) then
    failwith "fixed nonlinear split: topology rejected";
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
  let correspondence_encoded = TRANS (SYM call_encoding) correspondence in
  if not (aconv (lhand (concl correspondence_encoded)) reflected_call) then
    failwith "fixed nonlinear split: topology correspondence mismatch";
  let encoded_logical_result =
    TRANS (SYM correspondence_encoded) reflected_compute in
  let decoded_logical_result =
    AP_TERM
      `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode`
      encoded_logical_result in
  let decoded_logical_left =
    CONV_RULE
      (LAND_CONV
        (REWR_CONV
          candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_roundtrip))
      decoded_logical_result in
  let run_theorem =
    CONV_RULE
      (RAND_CONV
        (REWRITE_CONV
          [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_def;
           CONJUNCT1 candle_cv_fso_variable_jobs_decode_def;
           candle_cv_q_boxes_stack_decode_def;
           cexp_fst_def;cexp_snd_def;injectivity "cval"]))
      decoded_logical_left in
  if hyp run_theorem <> [] then
    failwith "fixed nonlinear split: run theorem assumptions";
  let logical_result = rand (concl run_theorem) in
  let logical_payload = rand logical_result in
  let final_stack = rand logical_payload in
  let initial_stack_pass =
    EQT_ELIM
      (REWRITE_CONV
        [candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def]
        (mk_icomb
          (mk_icomb
            (mk_icomb
              (`candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass`,
               `ARB:real^6`),
             prepared.expression_term),
           empty_stack))) in
  let soundness =
    REWRITE_RULE
      [candle_q_dim_analytic_jet_dim_six]
      (ISPECL
        [tokens;prepared.expression_term;`ARB:real^6`;decoded_jobs;
         empty_stack;empty_jobs;final_stack]
        candle_q_dim_taylor_model_fixed_nonlinear_variable_compact_run_sound) in
  let premise =
    CONJ prepared.valid_theorem
      (CONJ raw_result.fixed_nonlinear_variable_raw_accept_theorem
        (CONJ initial_stack_pass run_theorem)) in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "fixed nonlinear split: soundness premise mismatch";
  let stack_theorem = CONJUNCT2 (MATCH_MP soundness premise) in
  if hyp stack_theorem <> [] then
    failwith "fixed nonlinear split: stack theorem assumptions";
  {fixed_nonlinear_split_encoded_stack_term = reflected_stack;
   fixed_nonlinear_split_logical_stack_term = final_stack;
   fixed_nonlinear_split_topology_compute_theorem = reflected_compute;
   fixed_nonlinear_split_run_theorem = run_theorem;
   fixed_nonlinear_split_stack_theorem = stack_theorem};;

print_endline
  "CANDLE_CV_FIXED_NONLINEAR_VARIABLE_SPLIT_STACK_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
