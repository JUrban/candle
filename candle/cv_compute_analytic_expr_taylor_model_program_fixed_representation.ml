(* ========================================================================== *)
(* Computed-value representation of the fixed-polynomial hybrid program.    *)
(*                                                                            *)
(* These theorems connect the executable cval interpreter to the ordinary   *)
(* hybrid semantics used by the analytic soundness proof.                    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_compile_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_representation = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_sound;;

let candle_cv_fs_q_dim_taylor_model_program_step_correct = prove
 (`!center_instruction box_instruction center_boxes boxes radii stack.
     candle_cv_fs_q_dim_taylor_model_program_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction center_instruction)
       (candle_cv_analytic_instruction box_instruction)
       (candle_cv_q_dim_taylor_model_result_list_encode stack) =
     candle_cv_q_dim_taylor_model_result_list_encode
       (candle_q_dim_taylor_model_program_fixed_step
         center_boxes boxes radii center_instruction box_instruction stack)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC
    (SPEC `center_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  STRUCT_CASES_TAC
    (SPEC `box_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  REWRITE_TAC[candle_cv_fs_q_dim_taylor_model_program_step_def;
              candle_cv_fs_q_dim_taylor_model_is_poly_pair_def;
              candle_q_dim_taylor_model_program_fixed_step_def;
              candle_cv_analytic_instruction_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_analytic_instruction_poly_def;
              candle_cv_bool_and_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def;
              cexp_eq_def; distinctness "cval"; injectivity "cval";
              candle_cv_fs_poly_program_to_q_correct;
              candle_cv_q_dim_taylor_model_program_step_correct] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def;
              candle_cv_q_dim_taylor_model_result_list_encode_def]);;

let candle_cv_fs_q_dim_taylor_model_program_run_correct = prove
 (`!center_program box_program center_boxes boxes radii stack.
     candle_cv_fs_q_dim_taylor_model_program_run
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction_list center_program)
       (candle_cv_analytic_instruction_list box_program)
       (candle_cv_q_dim_taylor_model_result_list_encode stack) =
     candle_cv_q_dim_taylor_model_result_list_encode
       (candle_q_dim_taylor_model_program_fixed_run
         center_boxes boxes radii center_program box_program stack)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                candle_cv_fs_q_dim_taylor_model_program_run_def;
                candle_q_dim_taylor_model_program_fixed_run_def];
    LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                    candle_cv_fs_q_dim_taylor_model_program_run_def;
                    candle_q_dim_taylor_model_program_fixed_run_def;
                    candle_cv_fs_q_dim_taylor_model_program_step_correct]]);;

let candle_cv_fs_q_dim_taylor_model_program_correct = prove
 (`!center_program box_program boxes.
     candle_cv_fs_q_dim_taylor_model_program
       (candle_cv_analytic_instruction_list center_program)
       (candle_cv_analytic_instruction_list box_program)
       (candle_cv_q_interval_list boxes) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_program_fixed
         center_program box_program boxes)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_q_dim_taylor_model_program_def;
              candle_q_dim_taylor_model_program_fixed_def;
              candle_cv_q_center_environment_list_correct;
              candle_cv_q_radius_list_correct;
              candle_cv_q_fixed_list_round_upper_correct;
              GSYM candle_cv_q_dim_taylor_model_result_list_encode_def;
              candle_cv_fs_q_dim_taylor_model_program_run_correct;
              candle_cv_q_dim_taylor_model_result_head_correct]);;

end;;
