(* ========================================================================== *)
(* Stable-source batches for the reflected fixed-algebraic Taylor checker.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  One authenticated source program is patched  *)
(* inside reflected computation with exact whole-box and per-cell square-root *)
(* certificate lists.                                                        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_certificate_patch_exact.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_batch.ml";;

module Candle_cv_analytic_expr_stable_batch = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_certificate_patch;;
open Candle_cv_analytic_expr_certificate_patch_compute;;
open Candle_cv_analytic_expr_certificate_patch_exact;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch;;

let candle_q_dim_taylor_model_stable_jobs_numerical_accept_def = define
 `(candle_q_dim_taylor_model_stable_jobs_numerical_accept
      source_e box_e [] <=> T) /\
  (candle_q_dim_taylor_model_stable_jobs_numerical_accept
      source_e box_e (CONS job jobs) <=>
     let center_patched =
       candle_analytic_patch_sqrt_certificates (FST job) source_e in
     candle_analytic_program_sqrt_data_exact
       (FST job) (candle_analytic_compile source_e) /\
     candle_q_dim_taylor_model_result_domain
       (candle_q_dim_taylor_model_program_fixed_algebraic
         (candle_analytic_compile (SND center_patched))
         (candle_analytic_compile box_e) (SND job)) /\
     candle_q_box_valid_list (SND job) /\
     ~(candle_q_le candle_q_zero
        (candle_q_dim_taylor_model_certified_upper
          (candle_q_dim_taylor_model_program_fixed_algebraic
            (candle_analytic_compile (SND center_patched))
            (candle_analytic_compile box_e) (SND job)))) /\
     candle_q_dim_taylor_model_stable_jobs_numerical_accept
       source_e box_e jobs)`;;

let candle_q_dim_taylor_model_stable_batch_numerical_accept_def =
  new_definition
 `candle_q_dim_taylor_model_stable_batch_numerical_accept
      source_e box_intervals jobs <=>
    let box_patched =
      candle_analytic_patch_sqrt_certificates box_intervals source_e in
    candle_analytic_program_sqrt_data_exact
      box_intervals (candle_analytic_compile source_e) /\
    candle_q_dim_taylor_model_stable_jobs_numerical_accept
      source_e (SND box_patched) jobs`;;

let candle_cv_q_dim_taylor_model_stable_jobs_def = define
 `(candle_cv_q_dim_taylor_model_stable_jobs [] = Cexp_num 0) /\
  (candle_cv_q_dim_taylor_model_stable_jobs (CONS job jobs) =
     Cexp_pair
       (Cexp_pair
         (candle_cv_q_interval_list (FST job))
         (candle_cv_q_interval_list (SND job)))
       (candle_cv_q_dim_taylor_model_stable_jobs jobs))`;;

let candle_cv_fsa_stable_jobs_check_def = define
 `(candle_cv_fsa_stable_jobs_check source_program box_program
      (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fsa_stable_jobs_check source_program box_program
      (Cexp_pair job jobs) =
     Cexp_if
       (candle_cv_analytic_program_sqrt_data_exact
         (Cexp_fst job) source_program)
       (let center_patched =
          candle_cv_analytic_program_patch_sqrt
            (Cexp_fst job) source_program in
        Cexp_if
          (Cexp_fst
            (candle_cv_fsa_certified_check
              (Cexp_snd center_patched) box_program (Cexp_snd job)))
          (candle_cv_fsa_stable_jobs_check
            source_program box_program jobs)
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_fsa_stable_batch_check_def = new_definition
 `candle_cv_fsa_stable_batch_check source_program box_intervals jobs =
    Cexp_if
      (candle_cv_analytic_program_sqrt_data_exact
        box_intervals source_program)
      (let box_patched =
         candle_cv_analytic_program_patch_sqrt
           box_intervals source_program in
       candle_cv_fsa_stable_jobs_check
         source_program (Cexp_snd box_patched) jobs)
      (Cexp_num 0)`;;

let candle_cv_fsa_stable_jobs_check_compute = prove
 (`!source_program box_program jobs.
     candle_cv_fsa_stable_jobs_check source_program box_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if
         (candle_cv_analytic_program_sqrt_data_exact
           (Cexp_fst (Cexp_fst jobs)) source_program)
         (let center_patched =
            candle_cv_analytic_program_patch_sqrt
              (Cexp_fst (Cexp_fst jobs)) source_program in
          Cexp_if
            (Cexp_fst
              (candle_cv_fsa_certified_check
                (Cexp_snd center_patched) box_program
                (Cexp_snd (Cexp_fst jobs))))
            (candle_cv_fsa_stable_jobs_check
              source_program box_program (Cexp_snd jobs))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsa_stable_jobs_check_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_analytic_compile_patch_sqrt_correct = prove
 (`!e intervals.
     candle_cv_analytic_program_patch_sqrt
       (candle_cv_q_interval_list intervals)
       (candle_cv_analytic_instruction_list (candle_analytic_compile e)) =
     Cexp_pair
       (candle_cv_q_interval_list
         (FST (candle_analytic_patch_sqrt_certificates intervals e)))
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile
           (SND (candle_analytic_patch_sqrt_certificates intervals e))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_analytic_program_patch_sqrt_correct;
              candle_analytic_program_patch_sqrt_compile;
              LET_DEF; LET_END_DEF; FST; SND]);;

let candle_cv_fsa_stable_jobs_check_correct = prove
 (`!jobs source_e box_e.
     candle_cv_fsa_stable_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e))
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile box_e))
       (candle_cv_q_dim_taylor_model_stable_jobs jobs) =
     Cexp_num
       (if candle_q_dim_taylor_model_stable_jobs_numerical_accept
             source_e box_e jobs
        then SUC 0 else 0)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_dim_taylor_model_stable_jobs_def;
     candle_cv_fsa_stable_jobs_check_def;
     candle_q_dim_taylor_model_stable_jobs_numerical_accept_def;
     candle_cv_analytic_program_sqrt_data_exact_correct;
     candle_cv_analytic_compile_patch_sqrt_correct;
     candle_cv_fsa_certified_check_correct;
     cexp_fst_def; cexp_snd_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[candle_cv_fsa_batch_bool_and; CONJ_ASSOC;
              ARITH_RULE `1 = SUC 0`]);;

let candle_cv_fsa_stable_batch_check_correct = prove
 (`!source_e box_intervals jobs.
     candle_cv_fsa_stable_batch_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e))
       (candle_cv_q_interval_list box_intervals)
       (candle_cv_q_dim_taylor_model_stable_jobs jobs) =
     Cexp_num
       (if candle_q_dim_taylor_model_stable_batch_numerical_accept
             source_e box_intervals jobs
        then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_fsa_stable_batch_check_def;
     candle_q_dim_taylor_model_stable_batch_numerical_accept_def;
     candle_cv_analytic_program_sqrt_data_exact_correct;
     candle_cv_analytic_compile_patch_sqrt_correct;
     candle_cv_fsa_stable_jobs_check_correct;
     cexp_snd_def; LET_DEF; LET_END_DEF;
     candle_cv_fsa_batch_bool_and;
     ARITH_RULE `1 = SUC 0`]);;

let candle_cv_fsa_stable_batch_compute_eqs =
  union candle_cv_fsa_compute_eqs
    (candle_cv_analytic_program_patch_sqrt_compute_eqs @
     candle_cv_analytic_program_sqrt_data_exact_compute_eqs @
     [SPEC_ALL candle_cv_fsa_stable_jobs_check_compute;
      SPEC_ALL candle_cv_fsa_stable_batch_check_def]);;

end;;
