(* ========================================================================== *)
(* Exact split-tree composition for fixed-hybrid one-verdict batches.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_tree.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_batch.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_tree = struct

open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_certified_sound;;

let candle_q_dim_taylor_model_fixed_batch_accept_append = prove
 (`!left right box_e.
     candle_q_dim_taylor_model_fixed_batch_accept
       box_e (APPEND left right) <=>
     candle_q_dim_taylor_model_fixed_batch_accept box_e left /\
     candle_q_dim_taylor_model_fixed_batch_accept box_e right`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND;
                  candle_q_dim_taylor_model_fixed_batch_accept_def] THEN
  MESON_TAC[]);;

let candle_q_dim_taylor_model_fixed_tree_sound = prove
 (`!box_e (type_witness:real^N) tree.
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_q_dim_taylor_model_fixed_batch_accept box_e
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
                candle_q_dim_taylor_model_fixed_batch_accept_def] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[m_cell_pass] THEN
    MATCH_MP_TAC
      (ISPECL
        [`a0:candle_analytic_expr`;
         `box_e:candle_analytic_expr`;
         `a1:(((num#num)#num)#((num#num)#num))list`]
        candle_q_dim_taylor_model_fixed_certified_accept_sound) THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_tree_jobs_def;
                candle_q_dim_taylor_model_tree_root_boxes_def;
                candle_q_dim_taylor_model_tree_well_formed_def;
                candle_q_dim_taylor_model_fixed_batch_accept_append] THEN
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
