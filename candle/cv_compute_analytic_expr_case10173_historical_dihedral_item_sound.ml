(* ========================================================================== *)
(* Case-10173 historical item: exact reflected/ordinary correspondence.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_program_compute.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_first_order_sound.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_item_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_item_sound = struct

open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_first_order_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_compute;;

let candle_case10173_hist_result_def = new_definition
 `candle_case10173_hist_result center_boxes boxes radii
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0 =
    candle_fs_result_complete_rounded
      (candle_fs_list_of_q radii) T
      (candle_fs_hist_first_order_direct
        (candle_fs_interval_list_of_q center_boxes)
        center_root_delta center_root_four_x0)
      (candle_fs_hist_second_hessian
        (candle_fs_hist_second_order
          (candle_fs_interval_list_of_q boxes)
          box_root_delta box_root_four_x0))`;;

let candle_cv_case10173_hist_item_correct = prove
 (`!center_boxes boxes radii
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     candle_cv_case10173_hist_item
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_fs_interval_list
         [center_root_delta;center_root_four_x0;
          box_root_delta;box_root_four_x0]) =
     candle_cv_fsa_item_fixed
       (candle_cv_fs_result
       (candle_case10173_hist_result center_boxes boxes radii
         center_root_delta center_root_four_x0
         box_root_delta box_root_four_x0))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_case10173_hist_item_def;
              candle_case10173_hist_result_def;
              candle_cv_fs_interval_list_of_q_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fs_interval_lookup_correct;
              candle_fs_interval_lookup_def;
              candle_cv_fs_hist_first_order_direct_correct;
              candle_cv_fs_hist_second_order_correct;
              candle_cv_fs_hist_second_hessian_correct;
              candle_cv_fs_result_complete_true_correct;
              LET_DEF; LET_END_DEF] THEN
  MP_TAC (ARITH_RULE `1 = SUC 0`) THEN
  MP_TAC (ARITH_RULE `2 = SUC (SUC 0)`) THEN
  MP_TAC (ARITH_RULE `3 = SUC (SUC (SUC 0))`) THEN
  REPEAT (DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[candle_fs_interval_lookup_def]);;

let candle_cv_case10173_hist_item_encode_correct = prove
 (`!center_boxes boxes radii
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     candle_cv_case10173_hist_item
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_fs_interval_list
         [center_root_delta;center_root_four_x0;
          box_root_delta;box_root_four_x0]) =
     candle_cv_fsa_item_encode T
       (candle_case10173_hist_result center_boxes boxes radii
         center_root_delta center_root_four_x0
         box_root_delta box_root_four_x0)
       (candle_fs_result_to_q
         (candle_case10173_hist_result center_boxes boxes radii
           center_root_delta center_root_four_x0
           box_root_delta box_root_four_x0))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsa_item_encode_def;
              candle_cv_case10173_hist_item_correct]);;

end;;
