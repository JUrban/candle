(* ========================================================================== *)
(* One-root soundness for per-job fixed-outer certificate split trees.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Leaves retain their changing whole-box and   *)
(* center hints as data.  The theorem consumes one accepted job list and one *)
(* exact split tree and returns a single source-level m_cell_pass theorem.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_batch.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_tree_compact_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound = struct

open Candle_cv_analytic_expr_stable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_certified_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_sound;;

let candle_q_dim_taylor_model_fixed_outer_variable_tree_INDUCT,
    candle_q_dim_taylor_model_fixed_outer_variable_tree_RECURSION =
  define_type
    "candle_q_dim_taylor_model_fixed_outer_variable_tree =
       Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
         (((num#num)#num)#((num#num)#num))list
         (((num#num)#num)#((num#num)#num))list
         (((num#num)#num)#((num#num)#num))list
     | Candle_q_dim_taylor_model_fixed_outer_variable_tree_node
         num
         (((num#num)#num)#((num#num)#num))list
         candle_q_dim_taylor_model_fixed_outer_variable_tree
         candle_q_dim_taylor_model_fixed_outer_variable_tree";;

let candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes_def =
  define
 `(candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes
      (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
        box_intervals center_intervals boxes) = boxes) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes
      (Candle_q_dim_taylor_model_fixed_outer_variable_tree_node
        axis boxes left right) = boxes)`;;

let candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs_def = define
 `(candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs
      (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
        box_intervals center_intervals boxes) =
     [(box_intervals,(center_intervals,boxes))]) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs
      (Candle_q_dim_taylor_model_fixed_outer_variable_tree_node
        axis boxes left right) =
     APPEND
       (candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs left)
       (candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs right))`;;

let candle_q_dim_taylor_model_fixed_outer_variable_tree_exact_def = define
 `(candle_q_dim_taylor_model_fixed_outer_variable_tree_exact tree_dim
      (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
        box_intervals center_intervals boxes) <=>
     LENGTH boxes = tree_dim) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_tree_exact tree_dim
      (Candle_q_dim_taylor_model_fixed_outer_variable_tree_node
        axis boxes left right) <=>
     LENGTH boxes = tree_dim /\
     1 <= axis /\ axis <= tree_dim /\
     candle_q_boxes_split_exact_from 1 axis boxes
       (candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes left)
       (candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes right) /\
     candle_q_dim_taylor_model_fixed_outer_variable_tree_exact tree_dim left /\
     candle_q_dim_taylor_model_fixed_outer_variable_tree_exact
       tree_dim right)`;;

let candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept_append = prove
 (`!left right source_e.
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
       source_e (APPEND left right) <=>
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
       source_e left /\
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
       source_e right`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [APPEND;
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept_def] THEN
  MESON_TAC[]);;

let candle_q_dim_taylor_model_fixed_outer_variable_tree_glue = prove
 (`!source_e (type_witness:real^N) axis boxes left right.
     (!i. 1 <= i /\ i <= dimindex (:N) /\ ~(i = axis)
          ==> (candle_q_box_lower_vector right:real^N)$i =
                (candle_q_box_lower_vector boxes:real^N)$i /\
              (candle_q_box_upper_vector left:real^N)$i =
                (candle_q_box_upper_vector boxes:real^N)$i) /\
     (candle_q_box_upper_vector left:real^N)$axis =
       (candle_q_box_lower_vector right:real^N)$axis /\
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector boxes:real^N),
        (candle_q_box_upper_vector left:real^N)) /\
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector right:real^N),
        (candle_q_box_upper_vector boxes:real^N))
     ==> m_cell_pass
          (candle_analytic_denote_dim source_e)
          ((candle_q_box_lower_vector boxes:real^N),
           (candle_q_box_upper_vector boxes:real^N))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (fun whole ->
      let non_split,rest = CONJ_PAIR whole in
      let split_face,rest = CONJ_PAIR rest in
      let left_pass,right_pass = CONJ_PAIR rest in
      let glue = ISPECL
        [`axis:num`;
         `candle_q_box_lower_vector boxes:real^N`;
         `candle_q_box_upper_vector boxes:real^N`;
         `candle_q_box_upper_vector left:real^N`;
         `candle_q_box_lower_vector right:real^N`;
         `candle_analytic_denote_dim source_e:real^N->real`]
        M_verifier.M_CELL_PASS_GLUE_LEMMA in
      SUBGOAL_THEN
       `!i. 1 <= i /\ i <= dimindex (:N)
            ==> ~(i = axis)
            ==> (candle_q_box_lower_vector right:real^N)$i =
                  (candle_q_box_lower_vector boxes:real^N)$i /\
                (candle_q_box_upper_vector left:real^N)$i =
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

let candle_q_dim_taylor_model_fixed_outer_variable_tree_sound = prove
 (`!source_e (type_witness:real^N) tree.
     candle_analytic_valid_dim (dimindex (:N)) source_e /\
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
       source_e
       (candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs tree) /\
     candle_q_dim_taylor_model_fixed_outer_variable_tree_exact
       (dimindex (:N)) tree
     ==> m_cell_pass
          (candle_analytic_denote_dim source_e)
          ((candle_q_box_lower_vector
             (candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes
               tree):real^N),
           (candle_q_box_upper_vector
             (candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes
               tree):real^N))`,
  GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_fixed_outer_variable_tree_INDUCT THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs_def;
       candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes_def;
       candle_q_dim_taylor_model_fixed_outer_variable_tree_exact_def;
       candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept_def;
       m_cell_pass] THEN
    MESON_TAC
      [candle_analytic_patch_sqrt_certificates_valid_dim;
       candle_analytic_patch_sqrt_certificates_denote_dim;
       candle_q_dim_taylor_model_fixed_outer_certified_accept_sound];
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs_def;
       candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes_def;
       candle_q_dim_taylor_model_fixed_outer_variable_tree_exact_def;
       candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept_append] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC
      (ISPECL
        [`source_e:candle_analytic_expr`;
         `type_witness:real^N`; `a0:num`;
         `a1:(((num#num)#num)#((num#num)#num))list`;
         `candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes a2`;
         `candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes a3`]
        candle_q_dim_taylor_model_fixed_outer_variable_tree_glue) THEN
    MP_TAC
      (ISPECL
        [`a1:(((num#num)#num)#((num#num)#num))list`; `a0:num`;
         `candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes a2`;
         `candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes a3`;
         `type_witness:real^N`]
        candle_q_boxes_split_exact_vectors) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_TREE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
