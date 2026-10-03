(* ========================================================================== *)
(* Logical representation of the complete fixed nonlinear postfix machine.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_item_invariant.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_program_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_program_sound = struct

open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_item_invariant;;

let candle_fsn_logical_program_step_def = new_definition
 `candle_fsn_logical_program_step
      center_boxes boxes radii center_instruction box_instruction stack =
    if candle_q_analytic_instruction_tag center_instruction = 0 then
      if candle_q_analytic_instruction_tag box_instruction = 0 then
        CONS
          (candle_fsa_logical_poly_item center_boxes radii
            (candle_q_analytic_instruction_poly center_instruction)) stack
      else CONS (candle_fsa_logical_item_default center_boxes boxes) stack
    else if candle_q_analytic_instruction_tag center_instruction = 1 then
      if candle_q_analytic_instruction_tag box_instruction = 1 then
        CONS
          (candle_fsn_logical_item_sqrt radii
            (candle_q_analytic_instruction_sqrt center_instruction)
            (candle_q_analytic_instruction_sqrt box_instruction)
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail stack)
      else CONS (candle_fsa_logical_item_default center_boxes boxes) stack
    else if candle_q_analytic_instruction_tag box_instruction < 2 then
      CONS (candle_fsa_logical_item_default center_boxes boxes) stack
    else if candle_q_analytic_instruction_tag center_instruction =
            candle_q_analytic_instruction_tag box_instruction then
      if candle_q_analytic_instruction_tag center_instruction = 2 then
        CONS
          (candle_fsa_logical_item_neg T radii
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail stack)
      else if candle_q_analytic_instruction_tag center_instruction = 3 then
        CONS
          (candle_fsa_logical_item_add T radii
            (candle_fsa_logical_item_head center_boxes boxes
              (candle_fsa_logical_item_tail stack))
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail
            (candle_fsa_logical_item_tail stack))
      else if candle_q_analytic_instruction_tag center_instruction = 4 then
        CONS
          (candle_fso_logical_item_mul radii
            (candle_fsa_logical_item_head center_boxes boxes
              (candle_fsa_logical_item_tail stack))
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail
            (candle_fsa_logical_item_tail stack))
      else if candle_q_analytic_instruction_tag center_instruction = 5 then
        CONS
          (candle_fso_logical_item_square radii
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail stack)
      else if candle_q_analytic_instruction_tag center_instruction = 6 then
        CONS
          (candle_fsn_logical_item_inv radii
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail stack)
      else if candle_q_analytic_instruction_tag center_instruction = 7 then
        CONS
          (candle_fsn_logical_item_atn radii
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail stack)
      else if candle_q_analytic_instruction_tag center_instruction = 8 then
        CONS (candle_fsn_logical_item_pi_half radii boxes) stack
      else CONS (candle_fsa_logical_item_default center_boxes boxes) stack
    else CONS (candle_fsa_logical_item_default center_boxes boxes) stack`;;

let candle_fsn_logical_program_run_def = define
 `(candle_fsn_logical_program_run center_boxes boxes radii
      [] box_program stack = stack) /\
  (candle_fsn_logical_program_run center_boxes boxes radii
      (CONS ch ct) [] stack = stack) /\
  (candle_fsn_logical_program_run center_boxes boxes radii
      (CONS ch ct) (CONS bh bt) stack =
     candle_fsn_logical_program_run center_boxes boxes radii ct bt
       (candle_fsn_logical_program_step center_boxes boxes radii
         ch bh stack))`;;

let candle_cv_fsn_logical_program_step_correct = prove
 (`!center_instruction box_instruction center_boxes boxes radii stack.
     candle_cv_fso_program_step_fixed_nonlinear
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction center_instruction)
       (candle_cv_analytic_instruction box_instruction)
       (candle_cv_fsa_logical_stack_encode stack) =
     candle_cv_fsa_logical_stack_encode
       (candle_fsn_logical_program_step center_boxes boxes radii
         center_instruction box_instruction stack)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC
    (SPEC `center_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  STRUCT_CASES_TAC
    (SPEC `box_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  REWRITE_TAC[candle_cv_fso_program_step_fixed_nonlinear_def;
              candle_fsn_logical_program_step_def;
              candle_cv_analytic_instruction_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_analytic_instruction_poly_def;
              candle_q_analytic_instruction_sqrt_def;
              candle_cv_fsa_logical_stack_encode_def;
              candle_fsa_logical_poly_item_def;
              candle_fsa_logical_item_neg_def;
              candle_fsa_logical_item_add_def;
              cexp_fst_def; cexp_snd_def; cexp_eq_def; cexp_if_def;
              cexp_ispair_def; distinctness "cval"; injectivity "cval";
              NOT_SUC; candle_one_ne_zero; candle_four_ne_two;
              candle_four_ne_three; candle_three_ne_two;
              candle_five_ne_two; candle_five_ne_three;
              candle_five_ne_four; candle_six_ne_two;
              candle_six_ne_three; candle_six_ne_four;
              candle_six_ne_five;
              candle_seven_ne_two; candle_seven_ne_three;
              candle_seven_ne_four; candle_seven_ne_five;
              candle_seven_ne_six;
              candle_eight_ne_two; candle_eight_ne_three;
              candle_eight_ne_four; candle_eight_ne_five;
              candle_eight_ne_six; candle_eight_ne_seven;
              candle_cv_fsa_poly_item_correct;
              candle_cv_fsa_logical_item_default_correct;
              candle_cv_fsa_logical_item_head_correct;
              candle_cv_fsa_logical_item_tail_correct;
              candle_cv_fso_logical_item_mul_correct;
              candle_cv_fso_logical_item_square_correct;
              candle_cv_fsn_logical_item_inv_correct;
              candle_cv_fsn_logical_item_sqrt_correct;
              candle_cv_fsn_logical_item_atn_correct;
              candle_cv_fsn_logical_item_pi_half_correct] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[candle_cv_fsa_logical_stack_encode_def;
              candle_cv_fsa_logical_item_encode_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              candle_cv_fso_item_neg_correct;
              candle_cv_fso_item_add_correct;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fsn_logical_program_run_correct = prove
 (`!center_program box_program center_boxes boxes radii stack.
     candle_cv_fsn_program_run
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction_list center_program)
       (candle_cv_analytic_instruction_list box_program)
       (candle_cv_fsa_logical_stack_encode stack) =
     candle_cv_fsa_logical_stack_encode
       (candle_fsn_logical_program_run center_boxes boxes radii
         center_program box_program stack)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                candle_cv_fsn_program_run_def;
                candle_fsn_logical_program_run_def];
    LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                    candle_cv_fsn_program_run_def;
                    candle_fsn_logical_program_run_def;
                    candle_cv_fsn_logical_program_step_correct]]);;

end;;
