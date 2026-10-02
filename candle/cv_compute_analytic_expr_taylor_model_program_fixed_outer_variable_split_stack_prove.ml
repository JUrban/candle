(* ========================================================================== *)
(* General soundness handoff for separately computed numerical and topology   *)
(* verdicts.  Kernel.compute remains the sole authority for both executions.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_split_compute.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_split_stack_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_split_compute;;

type candle_q_dim_taylor_model_fixed_outer_variable_split_stack_result_six = {
  variable_split_encoded_stack_term : term;
  variable_split_logical_stack_term : term;
  variable_split_topology_compute_theorem : thm;
  variable_split_run_theorem : thm;
  variable_split_stack_theorem : thm;
};;

let candle_q_dim_taylor_model_fixed_outer_variable_split_stack_with_encoded_jobs_six
    (raw_result:
      candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six)
    compute_encoded_jobs jobs_to_compute_encoding tokens encoded_tokens =
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_split_compute_with_encoded_jobs_six
      raw_result compute_encoded_jobs jobs_to_compute_encoding
      tokens encoded_tokens in
  let prepared = result.variable_split_compute_prepared in
  let empty_stack =
    `[]:((((num#num)#num)#((num#num)#num))list)list` in
  let empty_jobs =
    `[]:((((num#num)#num)#((num#num)#num))list#
         ((((num#num)#num)#((num#num)#num))list#
          (((num#num)#num)#((num#num)#num))list))list` in
  candle_q_dim_analytic_jet_profile_event
    "variable-split-topology-handoff-begin";
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
        [tokens;prepared.expression_term;`ARB:real^6`;
         result.variable_split_compute_decoded_jobs;empty_stack;empty_jobs;
         result.variable_split_compute_final_stack]
        candle_q_dim_taylor_model_fixed_outer_variable_compact_run_sound) in
  let premise =
    CONJ prepared.valid_theorem
      (CONJ raw_result.variable_raw_accept_theorem
        (CONJ initial_stack_pass result.variable_split_compute_run_theorem)) in
  if not (aconv (fst (dest_imp (concl soundness))) (concl premise)) then
    failwith "fixed outer split checker: soundness premise mismatch";
  let sound_result = MATCH_MP soundness premise in
  let stack_theorem = CONJUNCT2 sound_result in
  candle_q_dim_analytic_jet_profile_event
    "variable-split-topology-handoff-end";
  if hyp stack_theorem <> [] then
    failwith "fixed outer split checker: stack theorem assumptions";
  {variable_split_encoded_stack_term =
     result.variable_split_compute_encoded_stack;
   variable_split_logical_stack_term =
     result.variable_split_compute_final_stack;
   variable_split_topology_compute_theorem =
     result.variable_split_compute_theorem;
   variable_split_run_theorem = result.variable_split_compute_run_theorem;
   variable_split_stack_theorem = stack_theorem};;

let candle_q_dim_taylor_model_fixed_outer_variable_split_stack_six
    (raw_result:
      candle_q_dim_taylor_model_fixed_outer_variable_raw_result_six)
    tokens encoded_tokens =
  let encoded_jobs = raw_result.variable_raw_encoded_jobs_term in
  candle_q_dim_taylor_model_fixed_outer_variable_split_stack_with_encoded_jobs_six
    raw_result encoded_jobs (REFL encoded_jobs) tokens encoded_tokens;;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_SPLIT_STACK_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
