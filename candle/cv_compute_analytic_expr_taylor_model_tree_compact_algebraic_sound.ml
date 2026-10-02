(* ========================================================================== *)
(* Fixed-algebraic corollary of the generic compact-tree topology theorem.    *)
(*                                                                            *)
(* This extension is separate so variable/raw certificate checking need not  *)
(* load the unrelated fixed-algebraic batch proof stack.                      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_tree_compact_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_tree.ml";;

module Candle_cv_analytic_expr_taylor_model_tree_compact_algebraic_sound = struct

open Candle_cv_analytic_expr_taylor_model_tree;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_tree;;

let candle_cv_q_dim_taylor_model_fixed_algebraic_tree_compact_sound = prove
 (`!box_e (type_witness:real^N) tree.
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_q_dim_taylor_model_fixed_algebraic_batch_accept box_e
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
     candle_q_dim_taylor_model_fixed_algebraic_tree_sound]);;

print_endline
  "CANDLE_CV_COMPACT_TREE_ALGEBRAIC_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
