(* ========================================================================== *)
(* Soundness of per-job fixed-nonlinear certificate batches.                  *)
(*                                                                            *)
(* One authenticated analytic source program is fixed.  Every job supplies   *)
(* its whole-box square-root payload, center payload, and box as data.  The   *)
(* executable checker validates both payload shapes before using the proved   *)
(* fixed-nonlinear Taylor evaluator.                                           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_certified_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_batch.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound = struct

open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_certificate_patch;;
open Candle_cv_analytic_expr_certificate_patch_compute;;
open Candle_cv_analytic_expr_certificate_patch_exact;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_stable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_certified_sound;;

(* A logical job is (whole_box_hints,(center_hints,box)). *)
let candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_numerical_accept_def =
  define
 `(candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_numerical_accept
      source_e [] <=> T) /\
  (candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_numerical_accept
      source_e (CONS job jobs) <=>
     let box_patched =
       candle_analytic_patch_sqrt_certificates (FST job) source_e in
     let center_patched =
       candle_analytic_patch_sqrt_certificates (FST (SND job)) source_e in
     candle_analytic_program_sqrt_data_exact
       (FST job) (candle_analytic_compile source_e) /\
     candle_analytic_program_sqrt_data_exact
       (FST (SND job)) (candle_analytic_compile source_e) /\
     candle_q_dim_taylor_model_result_domain
       (candle_q_dim_taylor_model_program_fixed_nonlinear
         (candle_analytic_compile (SND center_patched))
         (candle_analytic_compile (SND box_patched)) (SND (SND job))) /\
     candle_q_box_valid_list (SND (SND job)) /\
     ~(candle_q_le candle_q_zero
        (candle_q_dim_taylor_model_certified_upper
          (candle_q_dim_taylor_model_program_fixed_nonlinear
            (candle_analytic_compile (SND center_patched))
            (candle_analytic_compile (SND box_patched))
            (SND (SND job))))) /\
     candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_numerical_accept
       source_e jobs)`;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_def = define
 `(candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
      source_e [] <=> T) /\
  (candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
      source_e (CONS job jobs) <=>
     candle_q_dim_taylor_model_fixed_nonlinear_certified_accept
       (SND
         (candle_analytic_patch_sqrt_certificates
           (FST (SND job)) source_e))
       (SND
         (candle_analytic_patch_sqrt_certificates (FST job) source_e))
       (SND (SND job)) /\
     candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
       source_e jobs)`;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept = prove
 (`!jobs source_e.
     candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_numerical_accept
       source_e jobs
     ==>
     candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
       source_e jobs`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_numerical_accept_def;
       candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_def];
    POP_ASSUM (LABEL_TAC "tail_ih") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_numerical_accept_def;
       candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_def;
       candle_q_dim_taylor_model_fixed_nonlinear_certified_accept_def;
       candle_analytic_patch_sqrt_certificates_erasure;
       LET_DEF; LET_END_DEF] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "tail_ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_mem = prove
 (`!jobs source_e job.
     candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
       source_e jobs /\
     MEM job jobs
     ==>
     candle_q_dim_taylor_model_fixed_nonlinear_certified_accept
       (SND
         (candle_analytic_patch_sqrt_certificates
           (FST (SND job)) source_e))
       (SND
         (candle_analytic_patch_sqrt_certificates (FST job) source_e))
       (SND (SND job))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_def; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let candle_cv_fsn_variable_jobs_check_correct = prove
 (`!jobs source_e.
     candle_cv_fsn_variable_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e))
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs) =
     Cexp_num
       (if candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_numerical_accept
             source_e jobs
        then SUC 0 else 0)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
     candle_cv_fsn_variable_jobs_check_def;
     candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_numerical_accept_def;
     candle_cv_analytic_program_sqrt_data_exact_correct;
     candle_cv_analytic_compile_patch_sqrt_correct;
     candle_cv_fsn_certified_check_correct;
     cexp_fst_def; cexp_snd_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[candle_cv_fsa_batch_bool_and; CONJ_ASSOC;
              ARITH_RULE `1 = SUC 0`]);;

end;;
