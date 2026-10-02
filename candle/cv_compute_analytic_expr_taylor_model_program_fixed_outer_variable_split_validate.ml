(* Validation shared by the split numerical/topology certificate adapter. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_split_validate = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;

let candle_q_dim_taylor_model_fixed_outer_variable_split_validate_six
    (raw_result:
      candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six)
    tokens encoded_tokens =
  let prepared = raw_result.variable_raw_prepared_source in
  let encoded_jobs = raw_result.variable_raw_encoded_jobs_term in
  let decoded_jobs = raw_result.variable_raw_decoded_jobs_term in
  candle_q_dim_analytic_jet_profile_event
    "variable-split-topology-validation-begin";
  let expected_acceptance =
    list_mk_comb
      (`candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept`,
       [prepared.expression_term;decoded_jobs]) in
  if hyp raw_result.variable_raw_accept_theorem <> [] ||
     not (aconv (concl raw_result.variable_raw_accept_theorem)
       expected_acceptance) then
    failwith "fixed outer split checker: numerical acceptance mismatch";
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
    failwith "fixed outer split checker: token encoding mismatch";
  let jobs_representation = raw_result.variable_raw_representation_theorem in
  let expected_jobs_representation =
    mk_eq
      (mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs`,
         decoded_jobs),
       encoded_jobs) in
  if hyp jobs_representation <> [] ||
     not (aconv (concl jobs_representation) expected_jobs_representation) then
    failwith "fixed outer split checker: job representation mismatch";
  candle_q_dim_analytic_jet_profile_event
    "variable-split-topology-validation-end";
  token_encoding,jobs_representation;;

end;;
