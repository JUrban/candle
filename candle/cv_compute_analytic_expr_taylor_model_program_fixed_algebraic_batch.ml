(* ========================================================================== *)
(* One-verdict batches for the proved tagged fixed/rational Taylor checker.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch = struct

open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound;;

let candle_q_dim_taylor_model_fixed_algebraic_batch_numerical_accept_def =
  define
 `(candle_q_dim_taylor_model_fixed_algebraic_batch_numerical_accept
      box_e [] <=> T) /\
  (candle_q_dim_taylor_model_fixed_algebraic_batch_numerical_accept
      box_e (CONS job jobs) <=>
     candle_q_dim_taylor_model_result_domain
       (candle_q_dim_taylor_model_program_fixed_algebraic
         (candle_analytic_compile (FST job))
         (candle_analytic_compile box_e) (SND job)) /\
     candle_q_box_valid_list (SND job) /\
     ~(candle_q_le candle_q_zero
        (candle_q_dim_taylor_model_certified_upper
          (candle_q_dim_taylor_model_program_fixed_algebraic
            (candle_analytic_compile (FST job))
            (candle_analytic_compile box_e) (SND job)))) /\
     candle_q_dim_taylor_model_fixed_algebraic_batch_numerical_accept
       box_e jobs)`;;

let candle_q_dim_taylor_model_fixed_algebraic_batch_accept_def = define
 `(candle_q_dim_taylor_model_fixed_algebraic_batch_accept box_e [] <=> T) /\
  (candle_q_dim_taylor_model_fixed_algebraic_batch_accept
      box_e (CONS job jobs) <=>
     candle_q_dim_taylor_model_fixed_algebraic_certified_accept
       (FST job) box_e (SND job) /\
     candle_q_dim_taylor_model_fixed_algebraic_batch_accept box_e jobs)`;;

let candle_q_dim_taylor_model_fixed_algebraic_batch_erasure_def = define
 `(candle_q_dim_taylor_model_fixed_algebraic_batch_erasure
      (box_e:candle_analytic_expr)
      ([]:(candle_analytic_expr#
           (((num#num)#num)#((num#num)#num))list)list) <=> T) /\
  (candle_q_dim_taylor_model_fixed_algebraic_batch_erasure
      box_e (CONS job jobs) <=>
     candle_analytic_erase_sqrt_certificates (FST job) =
       candle_analytic_erase_sqrt_certificates box_e /\
     candle_q_dim_taylor_model_fixed_algebraic_batch_erasure box_e jobs)`;;

let candle_q_dim_taylor_model_fixed_algebraic_batch_accept_iff = prove
 (`!jobs box_e.
     candle_q_dim_taylor_model_fixed_algebraic_batch_accept box_e jobs <=>
     candle_q_dim_taylor_model_fixed_algebraic_batch_numerical_accept
       box_e jobs /\
     candle_q_dim_taylor_model_fixed_algebraic_batch_erasure box_e jobs`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_algebraic_batch_accept_def;
     candle_q_dim_taylor_model_fixed_algebraic_batch_numerical_accept_def;
     candle_q_dim_taylor_model_fixed_algebraic_batch_erasure_def;
     candle_q_dim_taylor_model_fixed_algebraic_certified_accept_def] THEN
  MESON_TAC[]);;

let candle_q_dim_taylor_model_fixed_algebraic_batch_accept_mem = prove
 (`!jobs box_e job.
     candle_q_dim_taylor_model_fixed_algebraic_batch_accept box_e jobs /\
     MEM job jobs
     ==> candle_q_dim_taylor_model_fixed_algebraic_certified_accept
           (FST job) box_e (SND job)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_algebraic_batch_accept_def; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let candle_q_dim_taylor_model_fixed_algebraic_batch_covers_def =
  new_definition
 `candle_q_dim_taylor_model_fixed_algebraic_batch_covers
      (type_witness:real^N) root_boxes jobs <=>
    !(p:real^N).
      p IN interval
        [candle_q_box_lower_vector root_boxes,
         candle_q_box_upper_vector root_boxes]
      ==> ?job. MEM job jobs /\
            p IN interval
              [candle_q_box_lower_vector (SND job),
               candle_q_box_upper_vector (SND job)]`;;

let candle_q_dim_taylor_model_fixed_algebraic_batch_sound = prove
 (`!box_e root_boxes jobs (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_q_dim_taylor_model_fixed_algebraic_batch_accept box_e jobs /\
     (!job. MEM job jobs ==> LENGTH (SND job) = dimindex (:N)) /\
     candle_q_dim_taylor_model_fixed_algebraic_batch_covers
       type_witness root_boxes jobs
     ==> !(p:real^N).
       p IN interval
         [candle_q_box_lower_vector root_boxes,
          candle_q_box_upper_vector root_boxes]
       ==> candle_analytic_denote_dim box_e p < &0`,
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_algebraic_batch_covers_def] THEN
  MESON_TAC
    [candle_q_dim_taylor_model_fixed_algebraic_batch_accept_mem;
     candle_q_dim_taylor_model_fixed_algebraic_certified_accept_sound]);;

let candle_cv_q_dim_taylor_model_fixed_algebraic_batch_jobs_def = define
 `(candle_cv_q_dim_taylor_model_fixed_algebraic_batch_jobs [] =
     Cexp_num 0) /\
  (candle_cv_q_dim_taylor_model_fixed_algebraic_batch_jobs
      (CONS job jobs) =
     Cexp_pair
       (Cexp_pair
         (candle_cv_analytic_instruction_list
           (candle_analytic_compile (FST job)))
         (candle_cv_q_interval_list (SND job)))
       (candle_cv_q_dim_taylor_model_fixed_algebraic_batch_jobs jobs))`;;

let candle_cv_fsa_batch_check_def = define
 `(candle_cv_fsa_batch_check box_program (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fsa_batch_check box_program (Cexp_pair job jobs) =
     Cexp_if
       (Cexp_fst
         (candle_cv_fsa_certified_check
           (Cexp_fst job) box_program (Cexp_snd job)))
       (candle_cv_fsa_batch_check box_program jobs)
       (Cexp_num 0))`;;

let candle_cv_fsa_batch_check_compute = prove
 (`!box_program jobs.
     candle_cv_fsa_batch_check box_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if
         (Cexp_fst
           (candle_cv_fsa_certified_check
             (Cexp_fst (Cexp_fst jobs)) box_program
             (Cexp_snd (Cexp_fst jobs))))
         (candle_cv_fsa_batch_check box_program (Cexp_snd jobs))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsa_batch_check_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_fsa_batch_bool_and = prove
 (`!p q.
     Cexp_if (Cexp_num (if p then SUC 0 else 0))
       (Cexp_num (if q then SUC 0 else 0)) (Cexp_num 0) =
     Cexp_num (if p /\ q then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN
  BOOL_CASES_TAC `q:bool` THEN REWRITE_TAC[cexp_if_def]);;

let candle_cv_fsa_batch_check_correct = prove
 (`!jobs box_e.
     candle_cv_fsa_batch_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile box_e))
       (candle_cv_q_dim_taylor_model_fixed_algebraic_batch_jobs jobs) =
     Cexp_num
       (if candle_q_dim_taylor_model_fixed_algebraic_batch_numerical_accept
             box_e jobs
        then SUC 0 else 0)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_dim_taylor_model_fixed_algebraic_batch_jobs_def;
     candle_cv_fsa_batch_check_def;
     candle_q_dim_taylor_model_fixed_algebraic_batch_numerical_accept_def;
     cexp_fst_def; cexp_snd_def;
     candle_cv_fsa_certified_check_correct] THEN
  REWRITE_TAC[ONE; candle_cv_fsa_batch_bool_and; CONJ_ASSOC]);;

let candle_cv_fsa_batch_compute_eqs =
  union candle_cv_fsa_compute_eqs
    [SPEC_ALL candle_cv_fsa_batch_check_compute];;

end;;
