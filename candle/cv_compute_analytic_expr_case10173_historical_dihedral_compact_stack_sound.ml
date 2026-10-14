(* ========================================================================== *)
(* Compact-topology soundness for checked historical case-10173 jobs.        *)
(*                                                                            *)
(* The numerical/source bridge already turns every authenticated historical  *)
(* job into an ordinary [m_cell_pass].  The generic compact runner can then  *)
(* consume those jobs and glue their boxes without reconstructing individual *)
(* arithmetic proofs.                                                        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_variable_batch_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_compact_stack_sound = struct

open M_verifier;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_variable_batch_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;

let candle_case10173_hist_jobs_compact_run_sound = prove
 (`!tokens source_e (type_witness:real^6) jobs stack remaining_jobs
      final_stack.
     candle_case10173_hist_jobs_pass source_e jobs /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass
       type_witness source_e stack /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_run
       (dimindex (:6)) tokens jobs stack =
       (T,(remaining_jobs,final_stack))
     ==>
     candle_case10173_hist_jobs_pass source_e remaining_jobs /\
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
          "candle_q_dim_taylor_model_fixed_outer_variable_compact_token"))
    THENL
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
           candle_case10173_hist_jobs_pass_def] THEN
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[PAIR_EQ;distinctness "bool"] THEN
        REPEAT STRIP_TAC THEN
        USE_THEN "tokens_ih"
          (fun tokens_ih ->
            ASM_MESON_TAC
              [tokens_ih;
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

let candle_case10173_hist_jobs_compact_sound = prove
 (`!source_e (type_witness:real^6) tokens jobs root_boxes.
     candle_case10173_hist_jobs_pass source_e jobs /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_run
       (dimindex (:6)) tokens jobs [] = (T,([],[root_boxes]))
     ==>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector root_boxes:real^6),
        (candle_q_box_upper_vector root_boxes:real^6))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`tokens:candle_q_dim_taylor_model_fixed_outer_variable_compact_token list`;
       `source_e:candle_analytic_expr`;`type_witness:real^6`;
       `jobs:((((num#num)#num)#((num#num)#num))list#
         ((((num#num)#num)#((num#num)#num))list#
          (((num#num)#num)#((num#num)#num))list))list`;
       `[]:((((num#num)#num)#((num#num)#num))list)list`;
       `[]:((((num#num)#num)#((num#num)#num))list#
         ((((num#num)#num)#((num#num)#num))list#
          (((num#num)#num)#((num#num)#num))list))list`;
       `[root_boxes]:((((num#num)#num)#((num#num)#num))list)list`]
      candle_case10173_hist_jobs_compact_run_sound) THEN
  ASM_REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def;
     candle_case10173_hist_jobs_pass_def]);;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_COMPACT_STACK_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
