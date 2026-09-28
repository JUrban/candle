(* ========================================================================== *)
(* Compiler substrate for the fixed-outer tagged Taylor evaluator.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_program_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_compile_sound = struct

open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_item_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_program_sound;;

let candle_fso_logical_item_mul_analytic_invariant = prove
 (`!center_a center_b box_a box_b boxes left right
      (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_a /\
     candle_analytic_valid_dim (dimindex (:N)) box_b /\
     candle_analytic_erase_sqrt_certificates center_a =
       candle_analytic_erase_sqrt_certificates box_a /\
     candle_analytic_erase_sqrt_certificates center_b =
       candle_analytic_erase_sqrt_certificates box_b /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_logical_item_analytic_invariant
       type_witness boxes left center_a box_a /\
     candle_fsa_logical_item_analytic_invariant
       type_witness boxes right center_b box_b
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_fso_logical_item_mul
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         left right)
       (Candle_analytic_mul center_a center_b)
       (Candle_analytic_mul box_a box_b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fso_logical_item_mul_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fso_item_mul_analytic_invariant));;

let candle_fso_logical_item_square_analytic_invariant = prove
 (`!center_e box_e boxes item (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_logical_item_analytic_invariant
       type_witness boxes item center_e box_e
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_fso_logical_item_square
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) item)
       (Candle_analytic_square center_e) (Candle_analytic_square box_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fso_logical_item_square_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fso_item_square_analytic_invariant));;

(* Concrete stack effects for instructions emitted by the compiler. *)

let candle_fso_logical_program_step_poly = prove
 (`!center_boxes boxes radii center_program box_program stack.
     candle_fso_logical_program_step center_boxes boxes radii
       (Candle_analytic_push_poly center_program)
       (Candle_analytic_push_poly box_program) stack =
     CONS
       (candle_fsa_logical_poly_item center_boxes radii center_program)
       stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fso_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_analytic_instruction_poly_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fso_logical_program_step_sqrt = prove
 (`!center_boxes boxes radii center_s box_s item stack.
     candle_fso_logical_program_step center_boxes boxes radii
       (Candle_analytic_program_sqrt center_s)
       (Candle_analytic_program_sqrt box_s) (CONS item stack) =
     CONS (candle_fsa_logical_item_sqrt radii center_s box_s item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fso_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_analytic_instruction_sqrt_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fso_logical_program_step_neg = prove
 (`!center_boxes boxes radii item stack.
     candle_fso_logical_program_step center_boxes boxes radii
       Candle_analytic_program_neg Candle_analytic_program_neg
       (CONS item stack) =
     CONS (candle_fsa_logical_item_neg T radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fso_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fso_logical_program_step_add = prove
 (`!center_boxes boxes radii left right stack.
     candle_fso_logical_program_step center_boxes boxes radii
       Candle_analytic_program_add Candle_analytic_program_add
       (CONS right (CONS left stack)) =
     CONS (candle_fsa_logical_item_add T radii left right) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fso_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fso_logical_program_step_mul = prove
 (`!center_boxes boxes radii left right stack.
     candle_fso_logical_program_step center_boxes boxes radii
       Candle_analytic_program_mul Candle_analytic_program_mul
       (CONS right (CONS left stack)) =
     CONS (candle_fso_logical_item_mul radii left right) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fso_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fso_logical_program_step_square = prove
 (`!center_boxes boxes radii item stack.
     candle_fso_logical_program_step center_boxes boxes radii
       Candle_analytic_program_square Candle_analytic_program_square
       (CONS item stack) =
     CONS (candle_fso_logical_item_square radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fso_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fso_logical_program_step_inv = prove
 (`!center_boxes boxes radii item stack.
     candle_fso_logical_program_step center_boxes boxes radii
       Candle_analytic_program_inv Candle_analytic_program_inv
       (CONS item stack) =
     CONS (candle_fsa_logical_item_inv radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fso_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fso_logical_program_step_atn = prove
 (`!center_boxes boxes radii item stack.
     candle_fso_logical_program_step center_boxes boxes radii
       Candle_analytic_program_atn Candle_analytic_program_atn
       (CONS item stack) =
     CONS (candle_fsa_logical_item_atn radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fso_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fso_logical_program_step_pi_half = prove
 (`!center_boxes boxes radii stack.
     candle_fso_logical_program_step center_boxes boxes radii
       Candle_analytic_program_pi_half Candle_analytic_program_pi_half stack =
     CONS
       (candle_fsa_logical_item_pi_half radii center_boxes boxes) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fso_logical_program_step_def;
              candle_q_analytic_instruction_tag_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fso_logical_program_run_append = prove
 (`!center_left box_left center_right box_right center_boxes boxes radii
      stack.
     LENGTH center_left = LENGTH box_left
     ==>
     candle_fso_logical_program_run center_boxes boxes radii
       (APPEND center_left center_right) (APPEND box_left box_right) stack =
     candle_fso_logical_program_run center_boxes boxes radii
       center_right box_right
       (candle_fso_logical_program_run center_boxes boxes radii
         center_left box_left stack)`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LENGTH; APPEND; candle_fso_logical_program_run_def] THEN
    ARITH_TAC;
    LIST_INDUCT_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REPEAT GEN_TAC THEN
      REWRITE_TAC[LENGTH; SUC_INJ; APPEND;
                  candle_fso_logical_program_run_def] THEN
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let candle_fso_logical_program_run_append_single = prove
 (`!center_program box_program center_instruction box_instruction
      center_boxes boxes radii stack inner result.
     LENGTH center_program = LENGTH box_program /\
     candle_fso_logical_program_run center_boxes boxes radii
       center_program box_program stack = CONS inner stack /\
     candle_fso_logical_program_step center_boxes boxes radii
       center_instruction box_instruction (CONS inner stack) =
       CONS result stack
     ==>
     candle_fso_logical_program_run center_boxes boxes radii
       (APPEND center_program [center_instruction])
       (APPEND box_program [box_instruction]) stack = CONS result stack`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fso_logical_program_run center_boxes boxes radii
      (APPEND center_program [center_instruction])
      (APPEND box_program [box_instruction]) stack =
    candle_fso_logical_program_run center_boxes boxes radii
      [center_instruction] [box_instruction]
      (candle_fso_logical_program_run center_boxes boxes radii
        center_program box_program stack)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fso_logical_program_run_append THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[candle_fso_logical_program_run_def]]);;

let candle_fso_logical_program_run_append_binary = prove
 (`!center_left box_left center_right box_right
      center_instruction box_instruction center_boxes boxes radii stack
      left right result.
     LENGTH center_left = LENGTH box_left /\
     LENGTH center_right = LENGTH box_right /\
     candle_fso_logical_program_run center_boxes boxes radii
       center_left box_left stack = CONS left stack /\
     candle_fso_logical_program_run center_boxes boxes radii
       center_right box_right (CONS left stack) =
       CONS right (CONS left stack) /\
     candle_fso_logical_program_step center_boxes boxes radii
       center_instruction box_instruction (CONS right (CONS left stack)) =
       CONS result stack
     ==>
     candle_fso_logical_program_run center_boxes boxes radii
       (APPEND center_left (APPEND center_right [center_instruction]))
       (APPEND box_left (APPEND box_right [box_instruction])) stack =
       CONS result stack`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fso_logical_program_run center_boxes boxes radii
      (APPEND center_left (APPEND center_right [center_instruction]))
      (APPEND box_left (APPEND box_right [box_instruction])) stack =
    candle_fso_logical_program_run center_boxes boxes radii
      (APPEND center_right [center_instruction])
      (APPEND box_right [box_instruction])
      (candle_fso_logical_program_run center_boxes boxes radii
        center_left box_left stack)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fso_logical_program_run_append THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fso_logical_program_run center_boxes boxes radii
      (APPEND center_right [center_instruction])
      (APPEND box_right [box_instruction]) (CONS left stack) =
    candle_fso_logical_program_run center_boxes boxes radii
      [center_instruction] [box_instruction]
      (candle_fso_logical_program_run center_boxes boxes radii
        center_right box_right (CONS left stack))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fso_logical_program_run_append THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[candle_fso_logical_program_run_def]]);;

end;;
