(* ========================================================================== *)
(* Semantic bridge for compact checked exact centered-Taylor split trees.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file is intentionally separate from the *)
(* executable checker and its representation proof, so the stable compact   *)
(* core can be checkpointed while the analytic bridge is developed.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_tree_compact_correct.ml";;

module Candle_cv_analytic_expr_taylor_model_tree_compact_sound = struct

open M_verifier;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_correct;;

let _ = print_endline "CANDLE_COMPACT_TREE_PROOF split-semantics begin";;
let candle_q_boxes_split_exact_from_lengths = prove
 (`!roots current axis lefts rights.
     candle_q_boxes_split_exact_from current axis roots lefts rights
     ==> LENGTH roots = LENGTH lefts /\ LENGTH roots = LENGTH rights`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `lefts:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    STRUCT_CASES_TAC
      (ISPEC
        `rights:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    REWRITE_TAC[candle_q_boxes_split_exact_from_def; LENGTH];
    MAP_EVERY X_GEN_TAC
      [`root_box:(((num#num)#num)#((num#num)#num))`;
       `root_boxes:(((num#num)#num)#((num#num)#num))list`] THEN
    DISCH_THEN (LABEL_TAC "root_boxes_length_ih") THEN
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `lefts:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    STRUCT_CASES_TAC
      (ISPEC
        `rights:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    ASM_REWRITE_TAC[candle_q_boxes_split_exact_from_def; LENGTH] THEN
    ASM_MESON_TAC[]]);;

let candle_q_boxes_split_exact_from_element = prove
 (`!roots current axis lefts rights.
     candle_q_boxes_split_exact_from current axis roots lefts rights
     ==> !k. k < LENGTH roots
         ==> FST (EL k lefts) = FST (EL k roots) /\
             SND (EL k rights) = SND (EL k roots) /\
             (current + k = axis
              ==> SND (EL k lefts) = FST (EL k rights)) /\
             (~(current + k = axis)
              ==> EL k lefts = EL k roots /\
                  EL k rights = EL k roots)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_boxes_split_exact_from_def; LENGTH; LT];
    MAP_EVERY X_GEN_TAC
      [`root_box:(((num#num)#num)#((num#num)#num))`;
       `root_boxes:(((num#num)#num)#((num#num)#num))list`] THEN
    DISCH_THEN (LABEL_TAC "root_boxes_element_ih") THEN
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `lefts:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    STRUCT_CASES_TAC
      (ISPEC
        `rights:(((num#num)#num)#((num#num)#num))list` list_CASES) THEN
    ASM_REWRITE_TAC[candle_q_boxes_split_exact_from_def] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2
        (LABEL_TAC "head_exact") (LABEL_TAC "tail_exact")) THEN
    X_GEN_TAC `k:num` THEN
    MP_TAC (SPEC `k:num` num_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST1_TAC
     (X_CHOOSE_THEN `tail_index:num` SUBST1_TAC)) THENL
     [DISCH_TAC THEN
      REMOVE_THEN "root_boxes_element_ih" (fun _ -> ALL_TAC) THEN
      REMOVE_THEN "tail_exact" (fun _ -> ALL_TAC) THEN
      ASM_CASES_TAC `(current:num) = axis` THEN
      ASM_REWRITE_TAC[EL; HD; ADD_CLAUSES] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      REMOVE_THEN "head_exact" (fun _ -> ALL_TAC) THEN
      USE_THEN "root_boxes_element_ih"
        (fun ih ->
          USE_THEN "tail_exact"
            (fun tail_exact ->
              let tail_elements =
                MATCH_MP
                  (SPECL
                    [`SUC current`; `axis:num`;
                     `t:(((num#num)#num)#((num#num)#num))list`;
                     `t':(((num#num)#num)#((num#num)#num))list`]
                    ih)
                  tail_exact in
              REWRITE_TAC
                [EL; TL;
                 ARITH_RULE `current + SUC tail_index =
                             SUC current + tail_index`] THEN
              MATCH_MP_TAC (SPEC `tail_index:num` tail_elements) THEN
              RULE_ASSUM_TAC (REWRITE_RULE[LENGTH]) THEN
              ASM_ARITH_TAC))]]);;
let _ = print_endline "CANDLE_COMPACT_TREE_PROOF split-semantics end";;

let _ = print_endline "CANDLE_COMPACT_TREE_PROOF split-components begin";;
let candle_q_boxes_split_exact_components = prove
 (`!roots axis lefts rights (type_witness:real^N).
     LENGTH roots = dimindex (:N) /\
     candle_q_boxes_split_exact_from 1 axis roots lefts rights
     ==> !i. 1 <= i /\ i <= dimindex (:N)
         ==> FST (EL (i - 1) lefts) = FST (EL (i - 1) roots) /\
             SND (EL (i - 1) rights) = SND (EL (i - 1) roots) /\
             (i = axis
              ==> SND (EL (i - 1) lefts) =
                  FST (EL (i - 1) rights)) /\
             (~(i = axis)
              ==> EL (i - 1) lefts = EL (i - 1) roots /\
                  EL (i - 1) rights = EL (i - 1) roots)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`roots:(((num#num)#num)#((num#num)#num))list`;
       `1`; `axis:num`;
       `lefts:(((num#num)#num)#((num#num)#num))list`;
       `rights:(((num#num)#num)#((num#num)#num))list`]
      candle_q_boxes_split_exact_from_element) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MP_TAC o SPEC `i - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> 1 + (i - 1) = i`]);;
let _ = print_endline "CANDLE_COMPACT_TREE_PROOF split-components end";;

let _ = print_endline "CANDLE_COMPACT_TREE_PROOF split-vectors begin";;
let candle_q_boxes_split_exact_vectors = prove
 (`!roots axis lefts rights (type_witness:real^N).
     LENGTH roots = dimindex (:N) /\
     1 <= axis /\ axis <= dimindex (:N) /\
     candle_q_boxes_split_exact_from 1 axis roots lefts rights
     ==>
     (candle_q_box_lower_vector roots:real^N) =
       candle_q_box_lower_vector lefts /\
     (candle_q_box_upper_vector roots:real^N) =
       candle_q_box_upper_vector rights /\
     (!i. 1 <= i /\ i <= dimindex (:N) /\ ~(i = axis)
          ==> (candle_q_box_lower_vector rights:real^N)$i =
                (candle_q_box_lower_vector roots:real^N)$i /\
              (candle_q_box_upper_vector lefts:real^N)$i =
                (candle_q_box_upper_vector roots:real^N)$i) /\
     (candle_q_box_upper_vector lefts:real^N)$axis =
       (candle_q_box_lower_vector rights:real^N)$axis`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`roots:(((num#num)#num)#((num#num)#num))list`;
       `axis:num`;
       `lefts:(((num#num)#num)#((num#num)#num))list`;
       `rights:(((num#num)#num)#((num#num)#num))list`;
       `type_witness:real^N`]
      candle_q_boxes_split_exact_components) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "components") THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CART_EQ] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "components" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    ASM_SIMP_TAC[candle_q_box_lower_vector_component; IN_NUMSEG];
    REWRITE_TAC[CART_EQ] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "components" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    ASM_SIMP_TAC[candle_q_box_upper_vector_component; IN_NUMSEG];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "components" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    ASM_SIMP_TAC
      [candle_q_box_lower_vector_component;
       candle_q_box_upper_vector_component; IN_NUMSEG];
    USE_THEN "components" (MP_TAC o SPEC `axis:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    ASM_SIMP_TAC
      [candle_q_box_lower_vector_component;
       candle_q_box_upper_vector_component; IN_NUMSEG]]);;
let _ = print_endline "CANDLE_COMPACT_TREE_PROOF split-vectors end";;

let _ = print_endline "CANDLE_COMPACT_TREE_PROOF exact-tree-sound begin";;
let candle_q_dim_taylor_model_tree_exact_well_formed_sound = prove
 (`!tree (type_witness:real^N).
     candle_q_dim_taylor_model_tree_exact_well_formed
       (dimindex (:N)) tree
     ==> candle_q_dim_taylor_model_tree_well_formed type_witness tree`,
  MATCH_MP_TAC candle_q_dim_taylor_model_tree_INDUCT THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_dim_taylor_model_tree_exact_well_formed_def;
       candle_q_dim_taylor_model_tree_well_formed_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_dim_taylor_model_tree_exact_well_formed_def;
       candle_q_dim_taylor_model_tree_well_formed_def;
       candle_q_dim_taylor_model_tree_root_boxes_def] THEN
    MESON_TAC[candle_q_boxes_split_exact_vectors]]);;
let _ = print_endline "CANDLE_COMPACT_TREE_PROOF exact-tree-sound end";;

let _ = print_endline "CANDLE_COMPACT_TREE_PROOF compact-tree-sound begin";;
let candle_cv_q_dim_taylor_model_tree_topology_accept_sound = prove
 (`!tree (type_witness:real^N).
     candle_cv_q_dim_taylor_model_tree_topology_check
       (Cexp_num (dimindex (:N)))
       (candle_cv_q_dim_taylor_model_tree_topology tree) = Cexp_num 1
     ==> candle_q_dim_taylor_model_tree_well_formed type_witness tree`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_tree_topology_check_correct;
     candle_cv_bool_def] THEN
  ASM_CASES_TAC
    `candle_q_dim_taylor_model_tree_exact_well_formed
       (dimindex (:N)) tree` THEN
  ASM_REWRITE_TAC[injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_MESON_TAC[candle_q_dim_taylor_model_tree_exact_well_formed_sound]);;

let candle_cv_q_dim_taylor_model_tree_compact_sound = prove
 (`!box_e (type_witness:real^N) tree.
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_q_dim_taylor_model_batch_accept box_e
       (candle_q_dim_taylor_model_tree_jobs tree) /\
     candle_cv_q_dim_taylor_model_tree_topology_check
       (Cexp_num (dimindex (:N)))
       (candle_cv_q_dim_taylor_model_tree_topology tree) = Cexp_num 1
     ==> m_cell_pass
          (candle_analytic_denote_dim box_e)
          ((candle_q_box_lower_vector
             (candle_q_dim_taylor_model_tree_root_boxes tree):real^N),
           (candle_q_box_upper_vector
             (candle_q_dim_taylor_model_tree_root_boxes tree):real^N))`,
  MESON_TAC
    [candle_cv_q_dim_taylor_model_tree_topology_accept_sound;
     candle_q_dim_taylor_model_tree_sound]);;

let _ = print_endline "CANDLE_COMPACT_TREE_PROOF compact-tree-sound end";;

print_endline "CANDLE_CV_COMPACT_TREE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
