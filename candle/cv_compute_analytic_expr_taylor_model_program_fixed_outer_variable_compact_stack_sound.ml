(* ========================================================================== *)
(* Memory-bounded topology checking for accepted variable Taylor jobs.       *)
(*                                                                            *)
(* The reflected state retains only the root boxes of active subtrees.  A    *)
(* glue token derives its parent boxes from the two children, verifies the   *)
(* exact split, and immediately discards both children.  No complete tree or *)
(* per-node parent-box stream is materialized.                                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound = struct

open M_verifier;;
open Candle_cv_analytic_expr_stable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_certified_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound;;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_token_INDUCT,
    candle_q_dim_taylor_model_fixed_outer_variable_compact_token_RECURSION =
  define_type
    "candle_q_dim_taylor_model_fixed_outer_variable_compact_token =
       Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf
     | Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue num";;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_join_def = define
 `(candle_q_dim_taylor_model_fixed_outer_variable_compact_join [] [] = []) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_compact_join
      [] (CONS right rights) = []) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_compact_join
      (CONS left lefts) [] = []) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_compact_join
      (CONS left lefts) (CONS right rights) =
     CONS (FST left,SND right)
       (candle_q_dim_taylor_model_fixed_outer_variable_compact_join
         lefts rights))`;;

(* The result is (success,(unconsumed jobs,top-first root-box stack)). *)
let candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def = define
 `(candle_q_dim_taylor_model_fixed_outer_variable_compact_run
      tree_dim [] jobs stack = (T,(jobs,stack))) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_compact_run
      tree_dim
      (CONS
        Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf tokens)
      [] stack = (F,([],stack))) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_compact_run
      tree_dim
      (CONS
        Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf tokens)
      (CONS job jobs) stack =
     if LENGTH (SND (SND job)) = tree_dim then
       candle_q_dim_taylor_model_fixed_outer_variable_compact_run
         tree_dim tokens jobs (CONS (SND (SND job)) stack)
     else (F,(CONS job jobs,stack))) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_compact_run
      tree_dim
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue axis)
        tokens)
      jobs [] = (F,(jobs,[]))) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_compact_run
      tree_dim
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue axis)
        tokens)
      jobs (CONS only []) = (F,(jobs,CONS only []))) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_compact_run
      tree_dim
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue axis)
        tokens)
      jobs (CONS right (CONS left stack)) =
     let parent =
       candle_q_dim_taylor_model_fixed_outer_variable_compact_join left right in
     if LENGTH parent = tree_dim /\
        1 <= axis /\ axis <= tree_dim /\
        candle_q_boxes_split_exact_from 1 axis parent left right
     then
       candle_q_dim_taylor_model_fixed_outer_variable_compact_run
         tree_dim tokens jobs (CONS parent stack)
     else (F,(jobs,CONS right (CONS left stack))))`;;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def =
  define
 `(candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass
      (type_witness:real^N) source_e [] <=> T) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass
      (type_witness:real^N) source_e (CONS boxes stack) <=>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector boxes:real^N),
        (candle_q_box_upper_vector boxes:real^N)) /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass
       type_witness source_e stack)`;;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_job_sound = prove
 (`!source_e (type_witness:real^N) job.
     candle_analytic_valid_dim (dimindex (:N)) source_e /\
     candle_q_dim_taylor_model_fixed_outer_certified_accept
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
     candle_q_dim_taylor_model_fixed_outer_certified_accept_sound]);;

print_endline "CANDLE_CV_COMPACT_STACK_PROOF_PHASE job-sound";;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_glue_sound = prove
 (`!source_e (type_witness:real^N) axis parent left right.
     LENGTH parent = dimindex (:N) /\
     1 <= axis /\ axis <= dimindex (:N) /\
     candle_q_boxes_split_exact_from 1 axis parent left right /\
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector left:real^N),
        (candle_q_box_upper_vector left:real^N)) /\
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector right:real^N),
        (candle_q_box_upper_vector right:real^N))
     ==>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector parent:real^N),
        (candle_q_box_upper_vector parent:real^N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (ISPECL
      [`source_e:candle_analytic_expr`;`type_witness:real^N`;`axis:num`;
       `parent:(((num#num)#num)#((num#num)#num))list`;
       `left:(((num#num)#num)#((num#num)#num))list`;
       `right:(((num#num)#num)#((num#num)#num))list`]
      candle_q_dim_taylor_model_fixed_outer_variable_tree_glue) THEN
  MP_TAC
    (ISPECL
      [`parent:(((num#num)#num)#((num#num)#num))list`;`axis:num`;
       `left:(((num#num)#num)#((num#num)#num))list`;
       `right:(((num#num)#num)#((num#num)#num))list`;
       `type_witness:real^N`]
      candle_q_boxes_split_exact_vectors) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

print_endline "CANDLE_CV_COMPACT_STACK_PROOF_PHASE glue-sound";;

let candle_q_dim_taylor_model_fixed_outer_variable_compact_run_sound = prove
 (`!tokens source_e (type_witness:real^N) jobs stack remaining_jobs
      final_stack.
     candle_analytic_valid_dim (dimindex (:N)) source_e /\
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept source_e jobs /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass
       type_witness source_e stack /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_run
       (dimindex (:N)) tokens jobs stack =
       (T,(remaining_jobs,final_stack))
     ==>
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
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
           candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept_def] THEN
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[PAIR_EQ;distinctness "bool"] THEN
        REPEAT STRIP_TAC THEN
        USE_THEN "tokens_ih"
          (fun tokens_ih ->
            ASM_MESON_TAC
              [tokens_ih;
               candle_q_dim_taylor_model_fixed_outer_variable_compact_job_sound;
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

let candle_q_dim_taylor_model_fixed_outer_variable_compact_sound = prove
 (`!source_e (type_witness:real^N) tokens jobs root_boxes.
     candle_analytic_valid_dim (dimindex (:N)) source_e /\
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept source_e jobs /\
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
      candle_q_dim_taylor_model_fixed_outer_variable_compact_run_sound) THEN
  ASM_REWRITE_TAC
    [candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def;
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept_def]);;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_COMPACT_STACK_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
