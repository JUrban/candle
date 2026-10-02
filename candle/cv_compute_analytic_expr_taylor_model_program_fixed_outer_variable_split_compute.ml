(* Reflected topology computation and representation handoff for split checks. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_split_validate.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_split_compute = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_split_validate;;

type candle_q_dim_taylor_model_fixed_outer_variable_split_compute_six = {
  variable_split_compute_prepared : candle_q_dim_analytic_jet_prepared_six;
  variable_split_compute_decoded_jobs : term;
  variable_split_compute_encoded_stack : term;
  variable_split_compute_theorem : thm;
  variable_split_compute_run_theorem : thm;
  variable_split_compute_final_stack : term;
};;

let candle_q_dim_taylor_model_fixed_outer_variable_split_compute_with_encoded_jobs_six
    (raw_result:
      candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six)
    compute_encoded_jobs jobs_to_compute_encoding tokens encoded_tokens =
  let prepared = raw_result.variable_raw_prepared_source in
  let encoded_jobs = raw_result.variable_raw_encoded_jobs_term in
  let decoded_jobs = raw_result.variable_raw_decoded_jobs_term in
  let empty_stack =
    `[]:((((num#num)#num)#((num#num)#num))list)list` in
  let token_encoding,jobs_representation =
    candle_q_dim_taylor_model_fixed_outer_variable_split_validate_six
      raw_result tokens encoded_tokens in
  let reflected_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`,
       [`Cexp_num 6`;encoded_tokens;compute_encoded_jobs;`Cexp_num 0`]) in
  candle_q_dim_analytic_jet_profile_event
    "variable-split-topology-compute-begin";
  let reflected_compute =
    Kernel.compute
      (COMPUTE_INIT_THMS,
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs)
      reflected_call in
  candle_q_dim_analytic_jet_profile_event
    "variable-split-topology-compute-end";
  let reflected_success,reflected_payload =
    candle_q_dim_stable_program_dest_cval_pair
      "split topology result" (rand (concl reflected_compute)) in
  let reflected_remaining,reflected_stack =
    candle_q_dim_stable_program_dest_cval_pair
      "split topology payload" reflected_payload in
  if hyp reflected_compute <> [] ||
     not (aconv reflected_success `Cexp_num 1`) ||
     not (aconv reflected_remaining `Cexp_num 0`) then
    failwith "fixed outer split checker: topology rejected";
  candle_q_dim_analytic_jet_profile_event
    "variable-split-topology-correspondence-begin";
  let correspondence =
    SPECL
      [tokens;`6`;decoded_jobs;empty_stack]
      candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_correct in
  let stack_encoding =
    REWRITE_CONV [candle_cv_q_boxes_stack_def]
      (mk_comb (`candle_cv_q_boxes_stack`,empty_stack)) in
  if hyp jobs_to_compute_encoding <> [] ||
     not
       (aconv (concl jobs_to_compute_encoding)
          (mk_eq (encoded_jobs,compute_encoded_jobs))) then
    failwith "fixed outer split checker: compute job encoding mismatch";
  let logical_call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL
        `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`)
      [REFL `Cexp_num 6`;token_encoding;jobs_representation;stack_encoding] in
  let compute_call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL
        `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`)
      [REFL `Cexp_num 6`;REFL encoded_tokens;jobs_to_compute_encoding;
       REFL `Cexp_num 0`] in
  let call_encoding =
    TRANS logical_call_encoding compute_call_encoding in
  let correspondence_encoded = TRANS (SYM call_encoding) correspondence in
  if not (aconv (lhand (concl correspondence_encoded)) reflected_call) then
    failwith "fixed outer split checker: correspondence mismatch";
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
    failwith "fixed outer split checker: run theorem assumptions";
  let logical_result = rand (concl run_theorem) in
  let logical_payload = rand logical_result in
  let final_stack = rand logical_payload in
  candle_q_dim_analytic_jet_profile_event
    "variable-split-topology-correspondence-end";
  {variable_split_compute_prepared = prepared;
   variable_split_compute_decoded_jobs = decoded_jobs;
   variable_split_compute_encoded_stack = reflected_stack;
   variable_split_compute_theorem = reflected_compute;
   variable_split_compute_run_theorem = run_theorem;
   variable_split_compute_final_stack = final_stack};;

let candle_q_dim_taylor_model_fixed_outer_variable_split_compute_six
    (raw_result:
      candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six)
    tokens encoded_tokens =
  let encoded_jobs = raw_result.variable_raw_encoded_jobs_term in
  candle_q_dim_taylor_model_fixed_outer_variable_split_compute_with_encoded_jobs_six
    raw_result encoded_jobs (REFL encoded_jobs) tokens encoded_tokens;;

end;;
