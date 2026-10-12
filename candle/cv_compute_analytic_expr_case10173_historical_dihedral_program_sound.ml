(* ========================================================================== *)
(* Case-10173 historical splice: exact program/result correspondence.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_item_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_program_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_item_sound;;

(* Encode an ordinary prefix followed by the private historical instruction.
   The source-specific structural theorem below authenticates that this is
   exactly what replacing the final eight instructions produces. *)

let candle_cv_case10173_hist_final_program_def = define
 `(candle_cv_case10173_hist_final_program [] =
     Cexp_pair (Cexp_num 9) (Cexp_num 0)) /\
  (candle_cv_case10173_hist_final_program (CONS h t) =
     Cexp_pair (candle_cv_analytic_instruction h)
       (candle_cv_case10173_hist_final_program t))`;;

let candle_cv_case10173_hist_splice_final_eight = prove
 (`!prefix i0 i1 i2 i3 i4 i5 i6 i7.
     candle_cv_case10173_hist_splice_aux (Cexp_num (LENGTH prefix))
       (candle_cv_analytic_instruction_list
         (APPEND prefix [i0;i1;i2;i3;i4;i5;i6;i7])) =
     candle_cv_case10173_hist_final_program prefix`,
  LIST_INDUCT_TAC THEN
  REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[LENGTH; APPEND;
                  candle_cv_analytic_instruction_list_def;
                  candle_cv_case10173_hist_final_program_def;
                  candle_cv_case10173_hist_splice_aux_def;
                  candle_cv_case10173_hist_drop_eight_def;
                  cexp_snd_def; cexp_sub_def] THEN
  REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`]);;

(* Whatever the ordinary prefix computes, the aligned final tag-9 pair pushes
   the historical item above that stack.  This is the key reason the exact
   top-level result can be proved without trusting or decoding the prefix. *)

let candle_cv_case10173_hist_program_run_final = prove
 (`!center_prefix box_prefix center_boxes boxes radii roots stack.
     LENGTH center_prefix = LENGTH box_prefix
     ==>
     ?tail.
       candle_cv_case10173_hist_program_run center_boxes boxes radii roots
         (candle_cv_case10173_hist_final_program center_prefix)
         (candle_cv_case10173_hist_final_program box_prefix) stack =
       Cexp_pair
         (candle_cv_case10173_hist_item center_boxes boxes radii roots)
         tail`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LENGTH] THENL
     [EXISTS_TAC `stack:cval` THEN
      REWRITE_TAC[candle_cv_case10173_hist_final_program_def;
                  candle_cv_case10173_hist_program_run_def;
                  candle_cv_case10173_hist_step_def;
                  cexp_eq_def; cexp_if_def; injectivity "cval"; NOT_SUC] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ARITH_TAC];
    LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LENGTH] THENL
     [ARITH_TAC;
      REWRITE_TAC[SUC_INJ;
                  candle_cv_case10173_hist_final_program_def;
                  candle_cv_case10173_hist_program_run_def] THEN
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* Once both authenticated source programs splice to aligned final-tag forms,
   the executable program exposes exactly the rational view of the ordinary
   historical result. *)

let candle_cv_case10173_hist_program_correct = prove
 (`!center_program box_program center_prefix box_prefix boxes
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     LENGTH center_prefix = LENGTH box_prefix /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) center_program =
       candle_cv_case10173_hist_final_program center_prefix /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) box_program =
       candle_cv_case10173_hist_final_program box_prefix
     ==>
     candle_cv_case10173_hist_program center_program box_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_fs_interval_list
         [center_root_delta;center_root_four_x0;
          box_root_delta;box_root_four_x0]) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_fs_result_to_q
         (candle_case10173_hist_result
           (candle_q_center_environment_list boxes) boxes
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
           center_root_delta center_root_four_x0
           box_root_delta box_root_four_x0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_cv_case10173_hist_program_def;
              candle_cv_q_center_environment_list_correct;
              candle_cv_q_radius_list_correct;
              candle_cv_q_fixed_list_round_upper_correct;
              LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `?tail.
      candle_cv_case10173_hist_program_run
        (candle_cv_q_interval_list
          (candle_q_center_environment_list boxes))
        (candle_cv_q_interval_list boxes)
        (candle_cv_q_list
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)))
        (candle_cv_fs_interval_list
          [center_root_delta;center_root_four_x0;
           box_root_delta;box_root_four_x0])
        (candle_cv_case10173_hist_final_program center_prefix)
        (candle_cv_case10173_hist_final_program box_prefix)
        (Cexp_num 0) =
      Cexp_pair
        (candle_cv_case10173_hist_item
          (candle_cv_q_interval_list
            (candle_q_center_environment_list boxes))
          (candle_cv_q_interval_list boxes)
          (candle_cv_q_list
            (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)))
          (candle_cv_fs_interval_list
            [center_root_delta;center_root_four_x0;
             box_root_delta;box_root_four_x0]))
        tail`
   (X_CHOOSE_THEN `tail:cval` SUBST1_TAC) THENL
   [MATCH_MP_TAC candle_cv_case10173_hist_program_run_final THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_cv_fsa_item_head_def;
              cexp_ispair_def; cexp_if_def; cexp_fst_def] THEN
  REWRITE_TAC[candle_cv_case10173_hist_item_encode_correct;
              candle_cv_fsa_item_to_q_correct;
              candle_fsa_item_q_view_def]);;

end;;
