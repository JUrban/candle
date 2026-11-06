(* ========================================================================== *)
(* End-to-end semantic composition for the packed-object whole call.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This unit makes the remaining semantic seam   *)
(* explicit.  The executable whole call and its component decomposition are  *)
(* proved below.  The compact-stack invariant is generalized from the legacy *)
(* numerical job predicate to exactly the per-leaf [m_cell_pass] facts        *)
(* produced by the packed object entries.                                     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_whole_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_whole_skeleton_sound = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;
open Candle_cv_analytic_expr_packed_source_object_whole_compute;;

let candle_q_packed_object_whole_jobs_pass_def = define
 `(candle_q_packed_object_whole_jobs_pass
      (type_witness:real^N) (source_e:candle_analytic_expr) [] <=> T) /\
  (candle_q_packed_object_whole_jobs_pass
      (type_witness:real^N) source_e
      (CONS
        (job:
          (((num#num)#num)#((num#num)#num))list#
          ((((num#num)#num)#((num#num)#num))list#
           (((num#num)#num)#((num#num)#num))list))
        jobs) <=>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector (SND (SND job)):real^N),
        (candle_q_box_upper_vector (SND (SND job)):real^N)) /\
     candle_q_packed_object_whole_jobs_pass type_witness source_e jobs)`;;

(* Public shape of the topology obligation.  It is discharged below from a   *)
(* generalized compact-stack invariant; it is not an assumption or axiom.     *)
let candle_q_packed_object_whole_topology_contract_def = new_definition
 `candle_q_packed_object_whole_topology_contract
      (type_witness:real^N) source_e tokens jobs root_boxes <=>
    candle_q_packed_object_whole_jobs_pass type_witness source_e jobs /\
    candle_q_dim_taylor_model_fixed_outer_variable_compact_run
      (dimindex (:N)) tokens jobs [] = (T,([],[root_boxes]))
    ==>
    m_cell_pass
      (candle_analytic_denote_dim source_e)
      ((candle_q_box_lower_vector root_boxes:real^N),
       (candle_q_box_upper_vector root_boxes:real^N))`;;

let candle_q_packed_object_whole_compact_run_sound = prove
 (`!tokens source_e (type_witness:real^N) jobs stack remaining_jobs
      final_stack.
     candle_q_packed_object_whole_jobs_pass type_witness source_e jobs /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass
       type_witness source_e stack /\
     candle_q_dim_taylor_model_fixed_outer_variable_compact_run
       (dimindex (:N)) tokens jobs stack =
       (T,(remaining_jobs,final_stack))
     ==>
     candle_q_packed_object_whole_jobs_pass
       type_witness source_e remaining_jobs /\
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
           candle_q_packed_object_whole_jobs_pass_def] THEN
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

let candle_q_packed_object_whole_topology_sound = prove
 (`!source_e (type_witness:real^N) tokens jobs root_boxes.
     candle_q_packed_object_whole_jobs_pass type_witness source_e jobs /\
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
      candle_q_packed_object_whole_compact_run_sound) THEN
  ASM_REWRITE_TAC
    [candle_q_packed_object_whole_jobs_pass_def;
     candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def]);;

let candle_q_packed_object_whole_topology_contract_sound = prove
 (`!source_e (type_witness:real^N) tokens jobs root_boxes.
     candle_q_packed_object_whole_topology_contract
       type_witness source_e tokens jobs root_boxes`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_whole_topology_contract_def] THEN
  MESON_TAC[candle_q_packed_object_whole_topology_sound]);;

let candle_cv_q_packed_object_whole_components = prove
 (`!source_descriptor tree_dim tokens encoded_jobs encoded_root.
     candle_cv_q_packed_object_whole_check
       source_descriptor tree_dim tokens encoded_jobs =
     Cexp_pair (Cexp_num 1)
       (Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 0)
           (Cexp_pair encoded_root (Cexp_num 0))))
     ==>
     candle_cv_q_packed_object_whole_jobs_check
       (Cexp_fst source_descriptor)
       (Cexp_fst (Cexp_snd source_descriptor))
       (Cexp_snd (Cexp_snd source_descriptor)) encoded_jobs = Cexp_num 1 /\
     candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
       tree_dim tokens encoded_jobs (Cexp_num 0) =
     Cexp_pair (Cexp_num 1)
       (Cexp_pair (Cexp_num 0)
         (Cexp_pair encoded_root (Cexp_num 0)))`,
  REWRITE_TAC
    [candle_cv_q_packed_object_whole_check_def;LET_DEF;LET_END_DEF;
     injectivity "cval"]);;

(* Exact current Candle-side skeleton.  The hypotheses name the remaining    *)
(* gates: canonical job representation, lockstep entry-to-leaf semantics, and *)
(* the generalized topology contract.  The encoded/logical run conversion and *)
(* final root handoff are proved here against the real whole-call definition. *)
let candle_cv_q_packed_object_whole_conditional_accept = prove
 (`!source_e (type_witness:real^N) source_descriptor tokens encoded_jobs
      encoded_root.
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
       (candle_cv_fso_variable_jobs_decode encoded_jobs) = encoded_jobs /\
     candle_q_packed_object_whole_jobs_pass type_witness source_e
       (candle_cv_fso_variable_jobs_decode encoded_jobs) /\
     candle_q_packed_object_whole_topology_contract type_witness source_e
       tokens (candle_cv_fso_variable_jobs_decode encoded_jobs)
       (candle_cv_q_interval_list_decode encoded_root) /\
     candle_cv_q_packed_object_whole_check source_descriptor
       (Cexp_num (dimindex (:N)))
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
         tokens)
       encoded_jobs =
     Cexp_pair (Cexp_num 1)
       (Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 0)
           (Cexp_pair encoded_root (Cexp_num 0))))
     ==>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector
          (candle_cv_q_interval_list_decode encoded_root):real^N),
        (candle_q_box_upper_vector
          (candle_cv_q_interval_list_decode encoded_root):real^N))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "representation")
      (CONJUNCTS_THEN2 (LABEL_TAC "jobs_pass")
        (CONJUNCTS_THEN2 (LABEL_TAC "topology_contract")
          (LABEL_TAC "whole")))) THEN
  USE_THEN "whole"
    (fun whole ->
      MP_TAC
        (MATCH_MP
          (SPECL
            [`source_descriptor:cval`;`Cexp_num (dimindex (:N))`;
             `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
                tokens`;
             `encoded_jobs:cval`;`encoded_root:cval`]
            candle_cv_q_packed_object_whole_components)
          whole)) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "numerical") (LABEL_TAC "topology")) THEN
  SUBGOAL_THEN
   `candle_q_dim_taylor_model_fixed_outer_variable_compact_run
      (dimindex (:N)) tokens
      (candle_cv_fso_variable_jobs_decode encoded_jobs) [] =
    (T,([],[candle_cv_q_interval_list_decode encoded_root]))`
    (LABEL_TAC "logical_run") THENL
   [MP_TAC
      (SPECL
        [`tokens:candle_q_dim_taylor_model_fixed_outer_variable_compact_token list`;
         `dimindex (:N)`;
         `candle_cv_fso_variable_jobs_decode encoded_jobs`;
         `[]:((((num#num)#num)#((num#num)#num))list)list`]
        candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_correct)
    THEN
    ASM_REWRITE_TAC[candle_cv_q_boxes_stack_def] THEN
    DISCH_THEN
      (fun correspondence ->
        MP_TAC
          (AP_TERM
            `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode`
            (SYM correspondence))) THEN
    REWRITE_TAC
      [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_roundtrip;
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_def;
       candle_cv_fso_variable_jobs_decode_def;
       candle_cv_q_boxes_stack_decode_def;
       cexp_fst_def;cexp_snd_def;injectivity "cval"];
    ALL_TAC] THEN
  USE_THEN "topology_contract" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_whole_topology_contract_def] THEN
  ASM_MESON_TAC[]);;

(* The topology premise of the historical skeleton is now an internal       *)
(* theorem.  Callers need only supply the canonical job representation, the  *)
(* lockstep entry-to-leaf facts, and the successful whole reflected call.    *)
let candle_cv_q_packed_object_whole_accept = prove
 (`!source_e (type_witness:real^N) source_descriptor tokens encoded_jobs
      encoded_root.
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
       (candle_cv_fso_variable_jobs_decode encoded_jobs) = encoded_jobs /\
     candle_q_packed_object_whole_jobs_pass type_witness source_e
       (candle_cv_fso_variable_jobs_decode encoded_jobs) /\
     candle_cv_q_packed_object_whole_check source_descriptor
       (Cexp_num (dimindex (:N)))
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
         tokens)
       encoded_jobs =
     Cexp_pair (Cexp_num 1)
       (Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 0)
           (Cexp_pair encoded_root (Cexp_num 0))))
     ==>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector
          (candle_cv_q_interval_list_decode encoded_root):real^N),
        (candle_q_box_upper_vector
          (candle_cv_q_interval_list_decode encoded_root):real^N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (SPECL
      [`source_e:candle_analytic_expr`;`type_witness:real^N`;
       `source_descriptor:cval`;
       `tokens:candle_q_dim_taylor_model_fixed_outer_variable_compact_token list`;
       `encoded_jobs:cval`;`encoded_root:cval`]
      candle_cv_q_packed_object_whole_conditional_accept) THEN
  ASM_REWRITE_TAC[candle_q_packed_object_whole_topology_contract_sound]);;

print_endline
  "CANDLE_CV_PACKED_OBJECT_WHOLE_SKELETON_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
