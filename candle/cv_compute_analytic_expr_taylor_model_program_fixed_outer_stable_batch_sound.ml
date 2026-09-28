(* ========================================================================== *)
(* Stable-source batches for the certified fixed-outer Taylor checker.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_stable_batch.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_certified_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_stable_batch_sound = struct

open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_certificate_patch;;
open Candle_cv_analytic_expr_certificate_patch_exact;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch;;
open Candle_cv_analytic_expr_stable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_certified_sound;;

let candle_q_dim_taylor_model_fixed_outer_batch_numerical_accept_def =
  define
 `(candle_q_dim_taylor_model_fixed_outer_batch_numerical_accept
      box_e [] <=> T) /\
  (candle_q_dim_taylor_model_fixed_outer_batch_numerical_accept
      box_e (CONS job jobs) <=>
     candle_q_dim_taylor_model_result_domain
       (candle_q_dim_taylor_model_program_fixed_outer
         (candle_analytic_compile (FST job))
         (candle_analytic_compile box_e) (SND job)) /\
     candle_q_box_valid_list (SND job) /\
     ~(candle_q_le candle_q_zero
        (candle_q_dim_taylor_model_certified_upper
          (candle_q_dim_taylor_model_program_fixed_outer
            (candle_analytic_compile (FST job))
            (candle_analytic_compile box_e) (SND job)))) /\
     candle_q_dim_taylor_model_fixed_outer_batch_numerical_accept
       box_e jobs)`;;

let candle_q_dim_taylor_model_fixed_outer_batch_accept_def = define
 `(candle_q_dim_taylor_model_fixed_outer_batch_accept box_e [] <=> T) /\
  (candle_q_dim_taylor_model_fixed_outer_batch_accept
      box_e (CONS job jobs) <=>
     candle_q_dim_taylor_model_fixed_outer_certified_accept
       (FST job) box_e (SND job) /\
     candle_q_dim_taylor_model_fixed_outer_batch_accept box_e jobs)`;;

let candle_q_dim_taylor_model_fixed_outer_batch_accept_iff = prove
 (`!jobs box_e.
     candle_q_dim_taylor_model_fixed_outer_batch_accept box_e jobs <=>
     candle_q_dim_taylor_model_fixed_outer_batch_numerical_accept
       box_e jobs /\
     candle_q_dim_taylor_model_fixed_algebraic_batch_erasure box_e jobs`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_batch_accept_def;
     candle_q_dim_taylor_model_fixed_outer_batch_numerical_accept_def;
     candle_q_dim_taylor_model_fixed_algebraic_batch_erasure_def;
     candle_q_dim_taylor_model_fixed_outer_certified_accept_def] THEN
  MESON_TAC[]);;

let candle_q_dim_taylor_model_fixed_outer_batch_accept_mem = prove
 (`!jobs box_e job.
     candle_q_dim_taylor_model_fixed_outer_batch_accept box_e jobs /\
     MEM job jobs
     ==> candle_q_dim_taylor_model_fixed_outer_certified_accept
           (FST job) box_e (SND job)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_batch_accept_def; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let candle_q_dim_taylor_model_fixed_outer_batch_sound = prove
 (`!box_e root_boxes jobs (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_q_dim_taylor_model_fixed_outer_batch_accept box_e jobs /\
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
    [candle_q_dim_taylor_model_fixed_outer_batch_accept_mem;
     candle_q_dim_taylor_model_fixed_outer_certified_accept_sound]);;

let candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept_def =
  define
 `(candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept
      source_e box_e [] <=> T) /\
  (candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept
      source_e box_e (CONS job jobs) <=>
     let center_patched =
       candle_analytic_patch_sqrt_certificates (FST job) source_e in
     candle_analytic_program_sqrt_data_exact
       (FST job) (candle_analytic_compile source_e) /\
     candle_q_dim_taylor_model_result_domain
       (candle_q_dim_taylor_model_program_fixed_outer
         (candle_analytic_compile (SND center_patched))
         (candle_analytic_compile box_e) (SND job)) /\
     candle_q_box_valid_list (SND job) /\
     ~(candle_q_le candle_q_zero
        (candle_q_dim_taylor_model_certified_upper
          (candle_q_dim_taylor_model_program_fixed_outer
            (candle_analytic_compile (SND center_patched))
            (candle_analytic_compile box_e) (SND job)))) /\
     candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept
       source_e box_e jobs)`;;

let candle_q_dim_taylor_model_fixed_outer_stable_batch_numerical_accept_def =
  new_definition
 `candle_q_dim_taylor_model_fixed_outer_stable_batch_numerical_accept
      source_e box_intervals jobs <=>
    let box_patched =
      candle_analytic_patch_sqrt_certificates box_intervals source_e in
    candle_analytic_program_sqrt_data_exact
      box_intervals (candle_analytic_compile source_e) /\
    candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept
      source_e (SND box_patched) jobs`;;

let candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept = prove
 (`!jobs source_e box_e.
     candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept
       source_e box_e jobs
     ==>
     candle_q_dim_taylor_model_fixed_outer_batch_numerical_accept
       box_e
       (candle_q_dim_taylor_model_stable_jobs_materialize source_e jobs)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept_def;
       candle_q_dim_taylor_model_stable_jobs_materialize_def;
       candle_q_dim_taylor_model_fixed_outer_batch_numerical_accept_def];
    POP_ASSUM (LABEL_TAC "tail_ih") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept_def;
       candle_q_dim_taylor_model_stable_jobs_materialize_def;
       candle_q_dim_taylor_model_fixed_outer_batch_numerical_accept_def;
       LET_DEF; LET_END_DEF] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "exact")
        (CONJUNCTS_THEN2 (LABEL_TAC "domain")
          (CONJUNCTS_THEN2 (LABEL_TAC "box")
            (CONJUNCTS_THEN2 (LABEL_TAC "negative")
              (LABEL_TAC "tail"))))) THEN
    (REPEAT CONJ_TAC THENL
     [USE_THEN "domain" ACCEPT_TAC;
      USE_THEN "box" ACCEPT_TAC;
      USE_THEN "negative" ACCEPT_TAC;
      USE_THEN "tail_ih"
        (fun ih ->
          MATCH_MP_TAC
            (SPECL
              [`source_e:candle_analytic_expr`;
               `box_e:candle_analytic_expr`]
              ih)) THEN
      USE_THEN "tail" ACCEPT_TAC])]);;

let candle_q_dim_taylor_model_fixed_outer_stable_jobs_accept = prove
 (`!jobs source_e box_e.
     candle_analytic_erase_sqrt_certificates box_e =
       candle_analytic_erase_sqrt_certificates source_e /\
     candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept
       source_e box_e jobs
     ==>
     candle_q_dim_taylor_model_fixed_outer_batch_accept
       box_e
       (candle_q_dim_taylor_model_stable_jobs_materialize source_e jobs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (snd
      (EQ_IMP_RULE
        (ISPECL
          [`candle_q_dim_taylor_model_stable_jobs_materialize
              source_e jobs`;
           `box_e:candle_analytic_expr`]
          candle_q_dim_taylor_model_fixed_outer_batch_accept_iff))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
      candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_dim_taylor_model_stable_jobs_erasure THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_dim_taylor_model_fixed_outer_stable_batch_accept = prove
 (`!source_e box_intervals jobs.
     candle_q_dim_taylor_model_fixed_outer_stable_batch_numerical_accept
       source_e box_intervals jobs
     ==>
     candle_q_dim_taylor_model_fixed_outer_batch_accept
       (SND
         (candle_analytic_patch_sqrt_certificates
           box_intervals source_e))
       (candle_q_dim_taylor_model_stable_jobs_materialize source_e jobs)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_stable_batch_numerical_accept_def;
     LET_DEF; LET_END_DEF] THEN
  DISCH_THEN (LABEL_TAC "stable_accept") THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_fixed_outer_stable_jobs_accept THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_analytic_patch_sqrt_certificates_erasure];
    USE_THEN "stable_accept" (ACCEPT_TAC o CONJUNCT2)]);;

let candle_cv_fso_stable_jobs_check_correct = prove
 (`!jobs source_e box_e.
     candle_cv_fso_stable_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e))
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile box_e))
       (candle_cv_q_dim_taylor_model_stable_jobs jobs) =
     Cexp_num
       (if candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept
             source_e box_e jobs
        then SUC 0 else 0)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_dim_taylor_model_stable_jobs_def;
     candle_cv_fso_stable_jobs_check_def;
     candle_q_dim_taylor_model_fixed_outer_stable_jobs_numerical_accept_def;
     candle_cv_analytic_program_sqrt_data_exact_correct;
     candle_cv_analytic_compile_patch_sqrt_correct;
     candle_cv_fso_certified_check_correct;
     cexp_fst_def; cexp_snd_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[candle_cv_fsa_batch_bool_and; CONJ_ASSOC;
              ARITH_RULE `1 = SUC 0`]);;

let candle_cv_fso_stable_batch_check_correct = prove
 (`!source_e box_intervals jobs.
     candle_cv_fso_stable_batch_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e))
       (candle_cv_q_interval_list box_intervals)
       (candle_cv_q_dim_taylor_model_stable_jobs jobs) =
     Cexp_num
       (if candle_q_dim_taylor_model_fixed_outer_stable_batch_numerical_accept
             source_e box_intervals jobs
        then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_fso_stable_batch_check_def;
     candle_q_dim_taylor_model_fixed_outer_stable_batch_numerical_accept_def;
     candle_cv_analytic_program_sqrt_data_exact_correct;
     candle_cv_analytic_compile_patch_sqrt_correct;
     candle_cv_fso_stable_jobs_check_correct;
     cexp_snd_def; LET_DEF; LET_END_DEF;
     candle_cv_fsa_batch_bool_and;
     ARITH_RULE `1 = SUC 0`]);;

end;;
