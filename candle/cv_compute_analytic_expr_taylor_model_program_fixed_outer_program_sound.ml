(* ========================================================================== *)
(* Logical representation of the fixed-outer tagged postfix evaluator.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_item_invariant.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_program_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_program_sound = struct

open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_item_invariant;;

let candle_fso_logical_item_mul_def = new_definition
 `candle_fso_logical_item_mul radii left right =
    let result =
      candle_fs_result_mul (candle_fs_list_of_q radii)
        (candle_fsa_item_fixed_view
          (candle_fsa_logical_item_tag left)
          (candle_fsa_logical_item_fixed left)
          (candle_fsa_logical_item_q left))
        (candle_fsa_item_fixed_view
          (candle_fsa_logical_item_tag right)
          (candle_fsa_logical_item_fixed right)
          (candle_fsa_logical_item_q right)) in
    candle_fsa_logical_item_make T result (candle_fs_result_to_q result)`;;

let candle_fso_logical_item_square_def = new_definition
 `candle_fso_logical_item_square radii item =
    let result =
      candle_fs_result_square (candle_fs_list_of_q radii)
        (candle_fsa_item_fixed_view
          (candle_fsa_logical_item_tag item)
          (candle_fsa_logical_item_fixed item)
          (candle_fsa_logical_item_q item)) in
    candle_fsa_logical_item_make T result (candle_fs_result_to_q result)`;;

(* Unlike the earlier algebraic evaluator, every algebraic operation here is
   fixed.  There is consequently no suffix-dependent mode in this machine. *)

let candle_fso_logical_program_step_def = new_definition
 `candle_fso_logical_program_step
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
          (candle_fsa_logical_item_sqrt radii
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
          (candle_fsa_logical_item_inv radii
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail stack)
      else if candle_q_analytic_instruction_tag center_instruction = 7 then
        CONS
          (candle_fsa_logical_item_atn radii
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail stack)
      else if candle_q_analytic_instruction_tag center_instruction = 8 then
        CONS
          (candle_fsa_logical_item_pi_half radii center_boxes boxes) stack
      else CONS (candle_fsa_logical_item_default center_boxes boxes) stack
    else CONS (candle_fsa_logical_item_default center_boxes boxes) stack`;;

let candle_fso_logical_program_run_def = define
 `(candle_fso_logical_program_run center_boxes boxes radii
      [] box_program stack = stack) /\
  (candle_fso_logical_program_run center_boxes boxes radii
      (CONS ch ct) [] stack = stack) /\
  (candle_fso_logical_program_run center_boxes boxes radii
      (CONS ch ct) (CONS bh bt) stack =
     candle_fso_logical_program_run center_boxes boxes radii ct bt
       (candle_fso_logical_program_step center_boxes boxes radii
         ch bh stack))`;;

let candle_cv_bool_true = prove
 (`candle_cv_bool T = Cexp_num 1`,
  REWRITE_TAC[candle_cv_bool_def] THEN CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_fso_item_neg_correct = prove
 (`!radii tag fixed q_result.
     candle_cv_fsa_item_neg (Cexp_num 1)
       (candle_cv_q_list radii)
       (candle_cv_fsa_item_encode tag fixed q_result) =
     candle_cv_fsa_item_encode T
       (candle_fs_result_neg (candle_fs_list_of_q radii)
         (candle_fsa_item_fixed_view tag fixed q_result))
       (candle_q_dim_taylor_model_result_neg radii
         (candle_fsa_item_q_view tag fixed q_result))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM candle_cv_bool_true] THEN
  MATCH_ACCEPT_TAC (SPEC `T` candle_cv_fsa_item_neg_correct));;

let candle_cv_fso_item_add_correct = prove
 (`!radii left_tag left_fixed left_q right_tag right_fixed right_q.
     candle_cv_fsa_item_add (Cexp_num 1)
       (candle_cv_q_list radii)
       (candle_cv_fsa_item_encode left_tag left_fixed left_q)
       (candle_cv_fsa_item_encode right_tag right_fixed right_q) =
     candle_cv_fsa_item_encode T
       (candle_fs_result_add (candle_fs_list_of_q radii)
         (candle_fsa_item_fixed_view left_tag left_fixed left_q)
         (candle_fsa_item_fixed_view right_tag right_fixed right_q))
       (candle_q_dim_taylor_model_result_add radii
         (candle_fsa_item_q_view left_tag left_fixed left_q)
         (candle_fsa_item_q_view right_tag right_fixed right_q))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM candle_cv_bool_true] THEN
  MATCH_ACCEPT_TAC (SPEC `T` candle_cv_fsa_item_add_correct));;

let candle_cv_fso_logical_item_mul_correct = prove
 (`!radii left right.
     candle_cv_fso_item_mul (candle_cv_q_list radii)
       (candle_cv_fsa_logical_item_encode left)
       (candle_cv_fsa_logical_item_encode right) =
     candle_cv_fsa_logical_item_encode
       (candle_fso_logical_item_mul radii left right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsa_logical_item_encode_def;
              candle_fso_logical_item_mul_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_cv_fso_item_mul_correct));;

let candle_cv_fso_logical_item_square_correct = prove
 (`!radii item.
     candle_cv_fso_item_square (candle_cv_q_list radii)
       (candle_cv_fsa_logical_item_encode item) =
     candle_cv_fsa_logical_item_encode
       (candle_fso_logical_item_square radii item)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsa_logical_item_encode_def;
              candle_fso_logical_item_square_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_cv_fso_item_square_correct));;

let candle_cv_fso_logical_program_step_correct = prove
 (`!center_instruction box_instruction center_boxes boxes radii stack.
     candle_cv_fso_program_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction center_instruction)
       (candle_cv_analytic_instruction box_instruction)
       (candle_cv_fsa_logical_stack_encode stack) =
     candle_cv_fsa_logical_stack_encode
       (candle_fso_logical_program_step center_boxes boxes radii
         center_instruction box_instruction stack)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC
    (SPEC `center_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  STRUCT_CASES_TAC
    (SPEC `box_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  REWRITE_TAC[candle_cv_fso_program_step_def;
              candle_fso_logical_program_step_def;
              candle_cv_analytic_instruction_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_analytic_instruction_poly_def;
              candle_q_analytic_instruction_sqrt_def;
              candle_cv_fsa_logical_stack_encode_def;
              candle_fsa_logical_poly_item_def;
              candle_fsa_logical_item_neg_def;
              candle_fsa_logical_item_add_def;
              candle_fso_logical_item_mul_def;
              candle_fso_logical_item_square_def;
              candle_fsa_logical_item_inv_def;
              candle_fsa_logical_item_sqrt_def;
              candle_fsa_logical_item_atn_def;
              candle_fsa_logical_item_pi_half_def;
              candle_fsa_logical_item_q_result_def;
              candle_cv_fsa_logical_item_encode_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
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
              candle_cv_fso_item_neg_correct;
              candle_cv_fso_item_add_correct;
              candle_cv_fso_item_mul_correct;
              candle_cv_fso_item_square_correct;
              candle_cv_fsa_item_inv_correct;
              candle_cv_fsa_item_sqrt_correct;
              candle_cv_fsa_item_atn_correct;
              candle_cv_fsa_item_pi_half_correct] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[candle_cv_fsa_logical_stack_encode_def;
              candle_cv_fsa_logical_item_encode_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fso_logical_program_run_correct = prove
 (`!center_program box_program center_boxes boxes radii stack.
     candle_cv_fso_program_run
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction_list center_program)
       (candle_cv_analytic_instruction_list box_program)
       (candle_cv_fsa_logical_stack_encode stack) =
     candle_cv_fsa_logical_stack_encode
       (candle_fso_logical_program_run center_boxes boxes radii
         center_program box_program stack)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                candle_cv_fso_program_run_def;
                candle_fso_logical_program_run_def];
    LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                    candle_cv_fso_program_run_def;
                    candle_fso_logical_program_run_def;
                    candle_cv_fso_logical_program_step_correct]]);;

end;;
