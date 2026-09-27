(* ========================================================================== *)
(* Logical representation of the tagged fixed/rational postfix evaluator.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound = struct

open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant;;

(* A logical stack item keeps both theorem-level payloads.  The tag selects *)
(* the only payload represented by the executable cval.                     *)

let candle_fsa_logical_item_make_def = new_definition
 `candle_fsa_logical_item_make tag fixed q_result =
    (tag,(fixed,q_result))`;;

let candle_fsa_logical_item_tag_def = new_definition
 `candle_fsa_logical_item_tag item = FST item`;;

let candle_fsa_logical_item_fixed_def = new_definition
 `candle_fsa_logical_item_fixed item = FST (SND item)`;;

let candle_fsa_logical_item_q_def = new_definition
 `candle_fsa_logical_item_q item = SND (SND item)`;;

let candle_cv_fsa_logical_item_encode_def = new_definition
 `candle_cv_fsa_logical_item_encode item =
    candle_cv_fsa_item_encode
      (candle_fsa_logical_item_tag item)
      (candle_fsa_logical_item_fixed item)
      (candle_fsa_logical_item_q item)`;;

let candle_cv_fsa_logical_stack_encode_def = define
 `(candle_cv_fsa_logical_stack_encode [] = Cexp_num 0) /\
  (candle_cv_fsa_logical_stack_encode (CONS h t) =
     Cexp_pair (candle_cv_fsa_logical_item_encode h)
       (candle_cv_fsa_logical_stack_encode t))`;;

let candle_fsa_logical_item_default_def = new_definition
 `candle_fsa_logical_item_default center_boxes boxes =
    let q_result =
      candle_q_dim_taylor_model_result_default center_boxes boxes in
    candle_fsa_logical_item_make F
      (candle_fsa_result_of_q q_result) q_result`;;

let candle_fsa_logical_item_head_def = define
 `(candle_fsa_logical_item_head center_boxes boxes [] =
     candle_fsa_logical_item_default center_boxes boxes) /\
  (candle_fsa_logical_item_head center_boxes boxes (CONS h t) = h)`;;

let candle_fsa_logical_item_tail_def = define
 `(candle_fsa_logical_item_tail [] = []) /\
  (candle_fsa_logical_item_tail (CONS h t) = t)`;;

let candle_fsa_logical_item_neg_def = new_definition
 `candle_fsa_logical_item_neg use_fixed radii item =
    candle_fsa_logical_item_make use_fixed
      (candle_fs_result_neg (candle_fs_list_of_q radii)
        (candle_fsa_item_fixed_view
          (candle_fsa_logical_item_tag item)
          (candle_fsa_logical_item_fixed item)
          (candle_fsa_logical_item_q item)))
      (candle_q_dim_taylor_model_result_neg radii
        (candle_fsa_item_q_view
          (candle_fsa_logical_item_tag item)
          (candle_fsa_logical_item_fixed item)
          (candle_fsa_logical_item_q item)))`;;

let candle_fsa_logical_item_add_def = new_definition
 `candle_fsa_logical_item_add use_fixed radii left right =
    candle_fsa_logical_item_make use_fixed
      (candle_fs_result_add (candle_fs_list_of_q radii)
        (candle_fsa_item_fixed_view
          (candle_fsa_logical_item_tag left)
          (candle_fsa_logical_item_fixed left)
          (candle_fsa_logical_item_q left))
        (candle_fsa_item_fixed_view
          (candle_fsa_logical_item_tag right)
          (candle_fsa_logical_item_fixed right)
          (candle_fsa_logical_item_q right)))
      (candle_q_dim_taylor_model_result_add radii
        (candle_fsa_item_q_view
          (candle_fsa_logical_item_tag left)
          (candle_fsa_logical_item_fixed left)
          (candle_fsa_logical_item_q left))
        (candle_fsa_item_q_view
          (candle_fsa_logical_item_tag right)
          (candle_fsa_logical_item_fixed right)
          (candle_fsa_logical_item_q right)))`;;

let candle_fsa_logical_item_q_result_def = new_definition
 `candle_fsa_logical_item_q_result q_result =
    candle_fsa_logical_item_make F
      (candle_fsa_result_of_q q_result) q_result`;;

let candle_fsa_logical_item_mul_def = new_definition
 `candle_fsa_logical_item_mul radii left right =
    candle_fsa_logical_item_q_result
      (candle_q_dim_taylor_model_result_mul radii
        (candle_fsa_item_q_view
          (candle_fsa_logical_item_tag left)
          (candle_fsa_logical_item_fixed left)
          (candle_fsa_logical_item_q left))
        (candle_fsa_item_q_view
          (candle_fsa_logical_item_tag right)
          (candle_fsa_logical_item_fixed right)
          (candle_fsa_logical_item_q right)))`;;

let candle_fsa_logical_item_square_def = new_definition
 `candle_fsa_logical_item_square radii item =
    candle_fsa_logical_item_q_result
      (candle_q_dim_taylor_model_result_square radii
        (candle_fsa_item_q_view
          (candle_fsa_logical_item_tag item)
          (candle_fsa_logical_item_fixed item)
          (candle_fsa_logical_item_q item)))`;;

let candle_fsa_logical_item_inv_def = new_definition
 `candle_fsa_logical_item_inv radii item =
    candle_fsa_logical_item_q_result
      (candle_q_dim_taylor_model_result_inv radii
        (candle_fsa_item_q_view
          (candle_fsa_logical_item_tag item)
          (candle_fsa_logical_item_fixed item)
          (candle_fsa_logical_item_q item)))`;;

let candle_fsa_logical_item_sqrt_def = new_definition
 `candle_fsa_logical_item_sqrt radii center_s box_s item =
    candle_fsa_logical_item_q_result
      (candle_q_dim_taylor_model_result_sqrt radii center_s box_s
        (candle_fsa_item_q_view
          (candle_fsa_logical_item_tag item)
          (candle_fsa_logical_item_fixed item)
          (candle_fsa_logical_item_q item)))`;;

let candle_fsa_logical_item_atn_def = new_definition
 `candle_fsa_logical_item_atn radii item =
    candle_fsa_logical_item_q_result
      (candle_q_dim_taylor_model_result_atn radii
        (candle_fsa_item_q_view
          (candle_fsa_logical_item_tag item)
          (candle_fsa_logical_item_fixed item)
          (candle_fsa_logical_item_q item)))`;;

let candle_fsa_logical_item_pi_half_def = new_definition
 `candle_fsa_logical_item_pi_half radii center_boxes boxes =
    candle_fsa_logical_item_q_result
      (candle_q_dim_taylor_model_result_pi_half
        radii center_boxes boxes)`;;

let candle_fsa_logical_poly_item_def = new_definition
 `candle_fsa_logical_poly_item center_boxes radii program =
    candle_fsa_logical_item_make T
      (candle_fs_poly_program center_boxes radii program)
      (candle_fs_poly_program_to_q center_boxes radii program)`;;

let candle_fsa_instruction_is_nonlinear_def = define
 `(candle_fsa_instruction_is_nonlinear
     (Candle_analytic_push_poly program) = F) /\
  (candle_fsa_instruction_is_nonlinear Candle_analytic_program_neg = F) /\
  (candle_fsa_instruction_is_nonlinear Candle_analytic_program_add = F) /\
  (candle_fsa_instruction_is_nonlinear Candle_analytic_program_mul = F) /\
  (candle_fsa_instruction_is_nonlinear Candle_analytic_program_square = F) /\
  (candle_fsa_instruction_is_nonlinear Candle_analytic_program_inv = T) /\
  (candle_fsa_instruction_is_nonlinear
     (Candle_analytic_program_sqrt s) = T) /\
  (candle_fsa_instruction_is_nonlinear Candle_analytic_program_atn = T) /\
  (candle_fsa_instruction_is_nonlinear
     Candle_analytic_program_pi_half = T)`;;

let candle_fsa_program_has_nonlinear_def = define
 `(candle_fsa_program_has_nonlinear [] = F) /\
  (candle_fsa_program_has_nonlinear (CONS h t) =
     (candle_fsa_instruction_is_nonlinear h \/
      candle_fsa_program_has_nonlinear t))`;;

let candle_fsa_logical_program_step_def = new_definition
 `candle_fsa_logical_program_step
      center_boxes boxes radii use_fixed
      center_instruction box_instruction stack =
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
          (candle_fsa_logical_item_neg use_fixed radii
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail stack)
      else if candle_q_analytic_instruction_tag center_instruction = 3 then
        CONS
          (candle_fsa_logical_item_add use_fixed radii
            (candle_fsa_logical_item_head center_boxes boxes
              (candle_fsa_logical_item_tail stack))
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail
            (candle_fsa_logical_item_tail stack))
      else if candle_q_analytic_instruction_tag center_instruction = 4 then
        CONS
          (candle_fsa_logical_item_mul radii
            (candle_fsa_logical_item_head center_boxes boxes
              (candle_fsa_logical_item_tail stack))
            (candle_fsa_logical_item_head center_boxes boxes stack))
          (candle_fsa_logical_item_tail
            (candle_fsa_logical_item_tail stack))
      else if candle_q_analytic_instruction_tag center_instruction = 5 then
        CONS
          (candle_fsa_logical_item_square radii
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

let candle_fsa_logical_program_run_def = define
 `(candle_fsa_logical_program_run center_boxes boxes radii
      [] box_program stack = stack) /\
  (candle_fsa_logical_program_run center_boxes boxes radii
      (CONS ch ct) [] stack = stack) /\
  (candle_fsa_logical_program_run center_boxes boxes radii
      (CONS ch ct) (CONS bh bt) stack =
     candle_fsa_logical_program_run center_boxes boxes radii ct bt
       (candle_fsa_logical_program_step center_boxes boxes radii
         (~(candle_fsa_program_has_nonlinear ct)) ch bh stack))`;;

let candle_cv_fsa_logical_item_default_correct = prove
 (`!center_boxes boxes.
     candle_cv_fsa_item_default
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes) =
     candle_cv_fsa_logical_item_encode
       (candle_fsa_logical_item_default center_boxes boxes)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsa_logical_item_encode_def;
              candle_fsa_logical_item_default_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF;
              candle_cv_fsa_item_default_def;
              candle_cv_fsa_item_encode_def;
              candle_cv_q_dim_taylor_model_result_default_correct]);;

let candle_cv_fsa_logical_item_head_correct = prove
 (`!center_boxes boxes stack.
     candle_cv_fsa_item_head
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_fsa_logical_stack_encode stack) =
     candle_cv_fsa_logical_item_encode
       (candle_fsa_logical_item_head center_boxes boxes stack)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_fsa_logical_stack_encode_def;
              candle_fsa_logical_item_head_def;
              candle_cv_fsa_item_head_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def;
              candle_cv_fsa_logical_item_default_correct]);;

let candle_cv_fsa_logical_item_tail_correct = prove
 (`!stack.
     candle_cv_fsa_item_tail
       (candle_cv_fsa_logical_stack_encode stack) =
     candle_cv_fsa_logical_stack_encode
       (candle_fsa_logical_item_tail stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_fsa_logical_stack_encode_def;
              candle_fsa_logical_item_tail_def;
              candle_cv_fsa_item_tail_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_fsa_instruction_is_nonlinear_correct = prove
 (`!instruction.
     candle_cv_fsa_instruction_is_nonlinear
       (candle_cv_analytic_instruction instruction) =
     candle_cv_bool (candle_fsa_instruction_is_nonlinear instruction)`,
  MATCH_MP_TAC candle_analytic_instruction_INDUCT THEN
  REWRITE_TAC[candle_cv_fsa_instruction_is_nonlinear_def;
              candle_cv_analytic_instruction_def;
              candle_fsa_instruction_is_nonlinear_def;
              candle_cv_bool_def; cexp_if_def; cexp_ispair_def;
              cexp_fst_def; cexp_eq_def; distinctness "cval";
              injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def]);;

let candle_cv_fsa_program_has_nonlinear_correct = prove
 (`!program.
     candle_cv_fsa_program_has_nonlinear
       (candle_cv_analytic_instruction_list program) =
     candle_cv_bool (candle_fsa_program_has_nonlinear program)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                  candle_cv_fsa_program_has_nonlinear_def;
                  candle_fsa_program_has_nonlinear_def;
                  candle_cv_fsa_instruction_is_nonlinear_correct;
                  candle_cv_bool_def; cexp_if_def] THEN
  BOOL_CASES_TAC `candle_fsa_instruction_is_nonlinear h` THEN
  BOOL_CASES_TAC `candle_fsa_program_has_nonlinear t` THEN
  REWRITE_TAC[cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_bool_not = prove
 (`!b.
     Cexp_if (candle_cv_bool b) (Cexp_num 0) (Cexp_num 1) =
     candle_cv_bool (~b)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_bool_def] THEN
  BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_fsa_logical_program_step_correct = prove
 (`!center_instruction box_instruction center_boxes boxes radii
      use_fixed stack.
     candle_cv_fsa_program_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_bool use_fixed)
       (candle_cv_analytic_instruction center_instruction)
       (candle_cv_analytic_instruction box_instruction)
       (candle_cv_fsa_logical_stack_encode stack) =
     candle_cv_fsa_logical_stack_encode
       (candle_fsa_logical_program_step center_boxes boxes radii
         use_fixed center_instruction box_instruction stack)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC
    (SPEC `center_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  STRUCT_CASES_TAC
    (SPEC `box_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  REWRITE_TAC[candle_cv_fsa_program_step_def;
              candle_fsa_logical_program_step_def;
              candle_cv_analytic_instruction_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_analytic_instruction_poly_def;
              candle_q_analytic_instruction_sqrt_def;
              candle_cv_fsa_logical_stack_encode_def;
              candle_fsa_logical_poly_item_def;
              candle_fsa_logical_item_neg_def;
              candle_fsa_logical_item_add_def;
              candle_fsa_logical_item_mul_def;
              candle_fsa_logical_item_square_def;
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
              candle_cv_fsa_item_neg_correct;
              candle_cv_fsa_item_add_correct;
              candle_cv_fsa_item_mul_correct;
              candle_cv_fsa_item_square_correct;
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

let candle_cv_fsa_logical_program_run_correct = prove
 (`!center_program box_program center_boxes boxes radii stack.
     candle_cv_fsa_program_run
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction_list center_program)
       (candle_cv_analytic_instruction_list box_program)
       (candle_cv_fsa_logical_stack_encode stack) =
     candle_cv_fsa_logical_stack_encode
       (candle_fsa_logical_program_run center_boxes boxes radii
         center_program box_program stack)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                candle_cv_fsa_program_run_def;
                candle_fsa_logical_program_run_def];
    LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                    candle_cv_fsa_program_run_def;
                    candle_fsa_logical_program_run_def;
                    candle_cv_fsa_program_has_nonlinear_correct;
                    candle_cv_bool_not;
                    candle_cv_fsa_logical_program_step_correct]]);;

end;;
