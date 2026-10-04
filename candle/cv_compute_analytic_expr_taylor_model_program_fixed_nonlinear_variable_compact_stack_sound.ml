(* ========================================================================== *)
(* Compact-topology soundness for accepted fixed-nonlinear variable jobs.     *)
(*                                                                            *)
(* Topology, box joining, and stack semantics are checker-independent.  This  *)
(* unit connects those reusable definitions to the fixed-nonlinear per-job    *)
(* acceptance contract.                                                       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_compact_stack_sound = struct

open M_verifier;;
open Candle_cv_analytic_expr_stable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_certified_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_compact_job_sound = prove
 (`!source_e (type_witness:real^N) job.
     candle_analytic_valid_dim (dimindex (:N)) source_e /\
     candle_q_dim_taylor_model_fixed_nonlinear_certified_accept
       (SND
         (candle_analytic_patch_sqrt_certificates
           (FST (SND job)) source_e))
       (SND
         (candle_analytic_patch_sqrt_certificates (FST job) source_e))
       (SND (SND job)) /\
     LENGTH (SND (SND job)) = dimindex (:N)
     ==>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector (SND (SND job)):real^N),
        (candle_q_box_upper_vector (SND (SND job)):real^N))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[m_cell_pass] THEN
  MESON_TAC
    [candle_analytic_patch_sqrt_certificates_valid_dim;
     candle_analytic_patch_sqrt_certificates_denote_dim;
     candle_q_dim_taylor_model_fixed_nonlinear_certified_accept_sound]);;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_compact_run_sound = prove
 (`!tokens source_e (type_witness:real^N) jobs stack remaining_jobs
      final_stack.
     candle_analytic_valid_dim (dimindex (:N)) source_e /\
     candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
       source_e jobs /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass
       type_witness source_e stack /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_run
       (dimindex (:N)) tokens jobs stack =
       (T,(remaining_jobs,final_stack))
     ==>
     candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
       source_e remaining_jobs /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass
       type_witness source_e final_stack`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
       PAIR_EQ] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "tokens_ih") THEN
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC
      (SPEC
        `a0:candle_q_dim_taylor_model_fixed_outer_variable_compact_token`
        (cases
          "candle_q_dim_taylor_model_fixed_outer_variable_compact_token")) THENL
     [STRUCT_CASES_TAC
        (ISPEC
          `jobs:((((num#num)#num)#((num#num)#num))list#
                 ((((num#num)#num)#((num#num)#num))list#
                  (((num#num)#num)#((num#num)#num))list))list`
          list_CASES) THENL
       [REWRITE_TAC
          [candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
           PAIR_EQ;distinctness "bool"];
        REWRITE_TAC
          [candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
           candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_def] THEN
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[PAIR_EQ;distinctness "bool"] THEN
        REPEAT STRIP_TAC THEN
        USE_THEN "tokens_ih"
          (fun tokens_ih ->
            ASM_MESON_TAC
              [tokens_ih;
               candle_q_dim_taylor_model_fixed_nonlinear_variable_compact_job_sound;
               candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def])];
      STRUCT_CASES_TAC
        (ISPEC
          `stack:((((num#num)#num)#((num#num)#num))list)list`
          list_CASES) THENL
       [REWRITE_TAC
          [candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
           PAIR_EQ;distinctness "bool"];
        STRUCT_CASES_TAC
          (ISPEC
            `t:((((num#num)#num)#((num#num)#num))list)list`
            list_CASES) THENL
         [REWRITE_TAC
            [candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
             PAIR_EQ;distinctness "bool"];
          REWRITE_TAC
            [candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
             LET_DEF;LET_END_DEF] THEN
          COND_CASES_TAC THEN
          ASM_REWRITE_TAC[PAIR_EQ;distinctness "bool"] THEN
          REPEAT STRIP_TAC THEN
          USE_THEN "tokens_ih"
            (fun tokens_ih ->
              ASM_MESON_TAC
                [tokens_ih;
                 candle_q_dim_taylor_model_fixed_outer_variable_compact_glue_sound;
                 candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def])]]]]);;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_compact_sound = prove
 (`!source_e (type_witness:real^N) tokens jobs root_boxes.
     candle_analytic_valid_dim (dimindex (:N)) source_e /\
     candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
       source_e jobs /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_run
       (dimindex (:N)) tokens jobs [] = (T,([],[root_boxes]))
     ==>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector root_boxes:real^N),
        (candle_q_box_upper_vector root_boxes:real^N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`tokens:candle_q_dim_taylor_model_fixed_outer_variable_compact_token list`;
       `source_e:candle_analytic_expr`;`type_witness:real^N`;
       `jobs:((((num#num)#num)#((num#num)#num))list#
         ((((num#num)#num)#((num#num)#num))list#
          (((num#num)#num)#((num#num)#num))list))list`;
       `[]:((((num#num)#num)#((num#num)#num))list)list`;
       `[]:((((num#num)#num)#((num#num)#num))list#
         ((((num#num)#num)#((num#num)#num))list#
          (((num#num)#num)#((num#num)#num))list))list`;
       `[root_boxes]:((((num#num)#num)#((num#num)#num))list)list`]
      candle_q_dim_taylor_model_fixed_nonlinear_variable_compact_run_sound) THEN
  ASM_REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def;
     candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_def]);;

end;;
