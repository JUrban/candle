(* ========================================================================== *)
(* Exact split-tree composition for one-verdict centered Taylor batches.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Every node records its exact rational root    *)
(* box.  Well-formedness says that its children share one face at the stated *)
(* coordinate and reproduce the other root faces.  The general theorem below *)
(* turns one accepted batch plus that topology fact into one root theorem;   *)
(* no per-leaf source theorem is part of its public interface.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_batch.ml";;

module Candle_cv_analytic_expr_taylor_model_tree = struct

open Candle_cv_analytic_expr_taylor_model_batch;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;

let candle_q_dim_taylor_model_tree_INDUCT,
    candle_q_dim_taylor_model_tree_RECURSION =
  define_type
    "candle_q_dim_taylor_model_tree =
       Candle_q_dim_taylor_model_tree_leaf
         candle_analytic_expr
         (((num#num)#num)#((num#num)#num))list
     | Candle_q_dim_taylor_model_tree_node
         num
         (((num#num)#num)#((num#num)#num))list
         candle_q_dim_taylor_model_tree
         candle_q_dim_taylor_model_tree";;

let candle_q_dim_taylor_model_tree_root_boxes_def = define
 `(candle_q_dim_taylor_model_tree_root_boxes
      (Candle_q_dim_taylor_model_tree_leaf center_e boxes) = boxes) /\
  (candle_q_dim_taylor_model_tree_root_boxes
      (Candle_q_dim_taylor_model_tree_node split_index boxes left right) =
     boxes)`;;

let candle_q_dim_taylor_model_tree_jobs_def = define
 `(candle_q_dim_taylor_model_tree_jobs
      (Candle_q_dim_taylor_model_tree_leaf center_e boxes) =
     [(center_e,boxes)]) /\
  (candle_q_dim_taylor_model_tree_jobs
      (Candle_q_dim_taylor_model_tree_node split_index boxes left right) =
     APPEND
       (candle_q_dim_taylor_model_tree_jobs left)
       (candle_q_dim_taylor_model_tree_jobs right))`;;

let candle_q_dim_taylor_model_tree_leaf_count_def = define
 `(candle_q_dim_taylor_model_tree_leaf_count
      (Candle_q_dim_taylor_model_tree_leaf center_e boxes) = 1) /\
  (candle_q_dim_taylor_model_tree_leaf_count
      (Candle_q_dim_taylor_model_tree_node split_index boxes left right) =
     candle_q_dim_taylor_model_tree_leaf_count left +
     candle_q_dim_taylor_model_tree_leaf_count right)`;;

let candle_q_dim_taylor_model_tree_well_formed_def = define
 `(candle_q_dim_taylor_model_tree_well_formed (type_witness:real^N)
      (Candle_q_dim_taylor_model_tree_leaf center_e boxes) <=>
     LENGTH boxes = dimindex (:N)) /\
  (candle_q_dim_taylor_model_tree_well_formed (type_witness:real^N)
      (Candle_q_dim_taylor_model_tree_node split_index boxes left right) <=>
     LENGTH boxes = dimindex (:N) /\
     1 <= split_index /\ split_index <= dimindex (:N) /\
     (candle_q_box_lower_vector boxes:real^N) =
       candle_q_box_lower_vector
         (candle_q_dim_taylor_model_tree_root_boxes left) /\
     (candle_q_box_upper_vector boxes:real^N) =
       candle_q_box_upper_vector
         (candle_q_dim_taylor_model_tree_root_boxes right) /\
     (!i. 1 <= i /\ i <= dimindex (:N) /\ ~(i = split_index)
          ==> (candle_q_box_lower_vector
                 (candle_q_dim_taylor_model_tree_root_boxes right):real^N)$i =
                (candle_q_box_lower_vector boxes:real^N)$i /\
              (candle_q_box_upper_vector
                 (candle_q_dim_taylor_model_tree_root_boxes left):real^N)$i =
                (candle_q_box_upper_vector boxes:real^N)$i) /\
     (candle_q_box_upper_vector
        (candle_q_dim_taylor_model_tree_root_boxes left):real^N)$split_index =
       (candle_q_box_lower_vector
        (candle_q_dim_taylor_model_tree_root_boxes right):real^N)$split_index /\
     candle_q_dim_taylor_model_tree_well_formed type_witness left /\
     candle_q_dim_taylor_model_tree_well_formed type_witness right)`;;

let candle_q_dim_taylor_model_batch_accept_append = prove
 (`!left right box_e.
     candle_q_dim_taylor_model_batch_accept box_e (APPEND left right) <=>
     candle_q_dim_taylor_model_batch_accept box_e left /\
     candle_q_dim_taylor_model_batch_accept box_e right`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND;candle_q_dim_taylor_model_batch_accept_def] THEN
  MESON_TAC[]);;

let candle_q_dim_taylor_model_tree_glue = prove
 (`!box_e (type_witness:real^N) split_index boxes left right.
     (!i. 1 <= i /\ i <= dimindex (:N) /\ ~(i = split_index)
          ==> (candle_q_box_lower_vector
                 (candle_q_dim_taylor_model_tree_root_boxes right):real^N)$i =
                (candle_q_box_lower_vector boxes:real^N)$i /\
              (candle_q_box_upper_vector
                 (candle_q_dim_taylor_model_tree_root_boxes left):real^N)$i =
                (candle_q_box_upper_vector boxes:real^N)$i) /\
     (candle_q_box_upper_vector
        (candle_q_dim_taylor_model_tree_root_boxes left):real^N)$split_index =
       (candle_q_box_lower_vector
        (candle_q_dim_taylor_model_tree_root_boxes right):real^N)$split_index /\
     m_cell_pass
       (candle_analytic_denote_dim box_e)
       ((candle_q_box_lower_vector boxes:real^N),
        (candle_q_box_upper_vector
          (candle_q_dim_taylor_model_tree_root_boxes left):real^N)) /\
     m_cell_pass
       (candle_analytic_denote_dim box_e)
       ((candle_q_box_lower_vector
          (candle_q_dim_taylor_model_tree_root_boxes right):real^N),
        (candle_q_box_upper_vector boxes:real^N))
     ==> m_cell_pass
          (candle_analytic_denote_dim box_e)
          ((candle_q_box_lower_vector boxes:real^N),
           (candle_q_box_upper_vector boxes:real^N))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (fun whole ->
      let non_split,rest = CONJ_PAIR whole in
      let split_face,rest = CONJ_PAIR rest in
      let left_pass,right_pass = CONJ_PAIR rest in
      let glue = ISPECL
        [`split_index:num`;
         `candle_q_box_lower_vector boxes:real^N`;
         `candle_q_box_upper_vector boxes:real^N`;
         `candle_q_box_upper_vector
            (candle_q_dim_taylor_model_tree_root_boxes left):real^N`;
         `candle_q_box_lower_vector
            (candle_q_dim_taylor_model_tree_root_boxes right):real^N`;
         `candle_analytic_denote_dim box_e:real^N->real`]
        M_verifier.M_CELL_PASS_GLUE_LEMMA in
      SUBGOAL_THEN
       `!i. 1 <= i /\ i <= dimindex (:N)
            ==> ~(i = split_index)
            ==> (candle_q_box_lower_vector
                   (candle_q_dim_taylor_model_tree_root_boxes right):real^N)$i =
                  (candle_q_box_lower_vector boxes:real^N)$i /\
                (candle_q_box_upper_vector
                   (candle_q_dim_taylor_model_tree_root_boxes left):real^N)$i =
                  (candle_q_box_upper_vector boxes:real^N)$i`
       (fun non_split_curried ->
          ACCEPT_TAC
            (MATCH_MP
              (MATCH_MP
                (MATCH_MP
                  (MATCH_MP glue non_split_curried)
                  split_face)
                left_pass)
              right_pass)) THEN
      MESON_TAC[non_split]));;

let candle_q_dim_taylor_model_tree_sound = prove
 (`!box_e (type_witness:real^N) tree.
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_q_dim_taylor_model_batch_accept box_e
       (candle_q_dim_taylor_model_tree_jobs tree) /\
     candle_q_dim_taylor_model_tree_well_formed type_witness tree
     ==> m_cell_pass
          (candle_analytic_denote_dim box_e)
          ((candle_q_box_lower_vector
             (candle_q_dim_taylor_model_tree_root_boxes tree):real^N),
           (candle_q_box_upper_vector
             (candle_q_dim_taylor_model_tree_root_boxes tree):real^N))`,
  GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_tree_INDUCT THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_tree_jobs_def;
                candle_q_dim_taylor_model_tree_root_boxes_def;
                candle_q_dim_taylor_model_tree_well_formed_def;
                candle_q_dim_taylor_model_batch_accept_def] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[m_cell_pass] THEN
    MATCH_MP_TAC
      (ISPECL
        [`a0:candle_analytic_expr`;
         `box_e:candle_analytic_expr`;
         `a1:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_taylor_model_certified_accept_sound) THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_tree_jobs_def;
                candle_q_dim_taylor_model_tree_root_boxes_def;
                candle_q_dim_taylor_model_tree_well_formed_def;
                candle_q_dim_taylor_model_batch_accept_append] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC
      (ISPECL
        [`box_e:candle_analytic_expr`;
         `type_witness:real^N`;
         `a0:num`;
         `a1:(((num#num)#num)#((num#num)#num))list`;
         `a2:candle_q_dim_taylor_model_tree`;
         `a3:candle_q_dim_taylor_model_tree`]
        candle_q_dim_taylor_model_tree_glue) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

end;;
