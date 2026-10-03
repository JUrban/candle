(* ========================================================================== *)
(* Soundness of canonical raw fixed-nonlinear variable-certificate batches.   *)
(*                                                                            *)
(* The existing canonical decoder authenticates the complete raw cval batch.  *)
(* Once that representation check succeeds, the fixed-nonlinear batch theorem *)
(* turns the single computed verdict into logical acceptance of every job.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_sound = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound;;

let candle_cv_fsn_variable_raw_jobs_check_correct = prove
 (`!encoded source_e.
     candle_cv_fsn_variable_raw_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e)) encoded =
     candle_cv_bool
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
          (candle_cv_fso_variable_jobs_decode encoded) = encoded /\
        candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_numerical_accept
          source_e (candle_cv_fso_variable_jobs_decode encoded))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_fsn_variable_raw_jobs_check_def;
     candle_cv_fso_variable_jobs_canonical_equal] THEN
  ASM_CASES_TAC
    `candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
       (candle_cv_fso_variable_jobs_decode encoded) = encoded` THENL
   [FIRST_ASSUM
      (fun representation ->
        ASSUME_TAC
          (REWRITE_RULE
            [candle_cv_fsn_variable_jobs_check_correct]
            (AP_TERM
              `\jobs:cval.
                 candle_cv_fsn_variable_jobs_check
                   (candle_cv_analytic_instruction_list
                     (candle_analytic_compile source_e)) jobs`
              (SYM representation)))) THEN
    ASM_REWRITE_TAC
      [candle_cv_bool_and_def;candle_cv_bool_def;cexp_if_def];
    ASM_REWRITE_TAC
      [candle_cv_bool_and_def;candle_cv_bool_def;cexp_if_def]]);;

let candle_cv_fsn_variable_raw_jobs_check_representation_accept = prove
 (`!encoded source_e.
     candle_cv_fsn_variable_raw_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e)) encoded = Cexp_num 1
     ==>
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
       (candle_cv_fso_variable_jobs_decode encoded) = encoded`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_fsn_variable_raw_jobs_check_correct;candle_cv_bool_def] THEN
  COND_CASES_TAC THENL
   [ASM_MESON_TAC[];
    REWRITE_TAC[injectivity "cval"] THEN CONV_TAC NUM_REDUCE_CONV]);;

let candle_cv_fsn_variable_raw_jobs_check_accept = prove
 (`!encoded source_e.
     candle_cv_fsn_variable_raw_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e)) encoded = Cexp_num 1
     ==>
     candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
       source_e (candle_cv_fso_variable_jobs_decode encoded)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_fsn_variable_raw_jobs_check_correct;candle_cv_bool_def] THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC
      candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[injectivity "cval"] THEN CONV_TAC NUM_REDUCE_CONV]);;

end;;
