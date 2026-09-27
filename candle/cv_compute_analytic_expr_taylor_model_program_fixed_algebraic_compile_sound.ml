(* ========================================================================== *)
(* Suffix-aware logical execution for the fixed/rational analytic program.   *)
(*                                                                            *)
(* A prefix cannot choose its fixed-scale tail from the prefix alone: later  *)
(* instructions may still contain a nonlinear operation.  The explicit      *)
(* future flag below makes that dependency compositional, so compiled source *)
(* expressions can be proved correct by structural induction.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_program_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound = struct

open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;

let candle_fsa_program_has_nonlinear_append = prove
 (`!left right.
     candle_fsa_program_has_nonlinear (APPEND left right) =
     (candle_fsa_program_has_nonlinear left \/
      candle_fsa_program_has_nonlinear right)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; candle_fsa_program_has_nonlinear_def;
                  OR_CLAUSES; DISJ_ASSOC]);;

let candle_fsa_logical_program_run_with_future_def = define
 `(candle_fsa_logical_program_run_with_future future_nonlinear
      center_boxes boxes radii [] box_program stack = stack) /\
  (candle_fsa_logical_program_run_with_future future_nonlinear
      center_boxes boxes radii (CONS ch ct) [] stack = stack) /\
  (candle_fsa_logical_program_run_with_future future_nonlinear
      center_boxes boxes radii (CONS ch ct) (CONS bh bt) stack =
     candle_fsa_logical_program_run_with_future future_nonlinear
       center_boxes boxes radii ct bt
       (candle_fsa_logical_program_step center_boxes boxes radii
         (~(candle_fsa_program_has_nonlinear ct \/ future_nonlinear))
         ch bh stack))`;;

let candle_fsa_logical_program_run_with_future_false = prove
 (`!center_program box_program center_boxes boxes radii stack.
     candle_fsa_logical_program_run_with_future F
       center_boxes boxes radii center_program box_program stack =
     candle_fsa_logical_program_run center_boxes boxes radii
       center_program box_program stack`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_fsa_logical_program_run_with_future_def;
                candle_fsa_logical_program_run_def];
    LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[candle_fsa_logical_program_run_with_future_def;
                    candle_fsa_logical_program_run_def; OR_CLAUSES]]);;

let candle_fsa_logical_program_run_with_future_append = prove
 (`!center_left box_left center_right box_right center_boxes boxes radii
      stack future_nonlinear.
     LENGTH center_left = LENGTH box_left
     ==>
     candle_fsa_logical_program_run_with_future future_nonlinear
       center_boxes boxes radii
       (APPEND center_left center_right) (APPEND box_left box_right) stack =
     candle_fsa_logical_program_run_with_future future_nonlinear
       center_boxes boxes radii center_right box_right
       (candle_fsa_logical_program_run_with_future
         (candle_fsa_program_has_nonlinear center_right \/
          future_nonlinear)
         center_boxes boxes radii center_left box_left stack)`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LENGTH; APPEND;
                candle_fsa_logical_program_run_with_future_def] THEN
    ARITH_TAC;
    LIST_INDUCT_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REPEAT GEN_TAC THEN
      REWRITE_TAC[LENGTH; SUC_INJ; APPEND;
                  candle_fsa_logical_program_run_with_future_def;
                  candle_fsa_program_has_nonlinear_append; DISJ_ASSOC] THEN
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* Package the item invariant through the logical tagged representation. *)

let candle_fsa_logical_item_analytic_invariant_def = new_definition
 `candle_fsa_logical_item_analytic_invariant
      (type_witness:real^N) boxes item center_e box_e <=>
    candle_fsa_item_analytic_invariant type_witness boxes
      (candle_fsa_logical_item_tag item)
      (candle_fsa_logical_item_fixed item)
      (candle_fsa_logical_item_q item) center_e box_e`;;

let candle_fsa_logical_item_neg_analytic_invariant = prove
 (`!center_e box_e boxes use_fixed item (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_logical_item_analytic_invariant
       type_witness boxes item center_e box_e
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_fsa_logical_item_neg use_fixed
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) item)
       (Candle_analytic_neg center_e) (Candle_analytic_neg box_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsa_logical_item_neg_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def] THEN
  MATCH_ACCEPT_TAC candle_fsa_item_neg_analytic_invariant);;

let candle_fsa_logical_item_add_analytic_invariant = prove
 (`!center_a center_b box_a box_b boxes use_fixed left right
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
       (candle_fsa_logical_item_add use_fixed
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         left right)
       (Candle_analytic_add center_a center_b)
       (Candle_analytic_add box_a box_b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsa_logical_item_add_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def] THEN
  MATCH_ACCEPT_TAC candle_fsa_item_add_analytic_invariant);;

let candle_fsa_logical_item_mul_analytic_invariant = prove
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
       (candle_fsa_logical_item_mul
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         left right)
       (Candle_analytic_mul center_a center_b)
       (Candle_analytic_mul box_a box_b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsa_logical_item_mul_def;
              candle_fsa_logical_item_q_result_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fsa_item_mul_analytic_invariant));;

let candle_fsa_logical_item_square_analytic_invariant = prove
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
       (candle_fsa_logical_item_square
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) item)
       (Candle_analytic_square center_e) (Candle_analytic_square box_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsa_logical_item_square_def;
              candle_fsa_logical_item_q_result_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fsa_item_square_analytic_invariant));;

let candle_fsa_logical_item_inv_analytic_invariant = prove
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
       (candle_fsa_logical_item_inv
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) item)
       (Candle_analytic_inv center_e) (Candle_analytic_inv box_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsa_logical_item_inv_def;
              candle_fsa_logical_item_q_result_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fsa_item_inv_analytic_invariant));;

let candle_fsa_logical_item_sqrt_analytic_invariant = prove
 (`!clp cln cld cup cun cud blp bln bld bup bun bud
      center_e box_e boxes item (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_logical_item_analytic_invariant
       type_witness boxes item center_e box_e
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_fsa_logical_item_sqrt
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_analytic_sqrt_interval clp cln cld cup cun cud)
         (candle_analytic_sqrt_interval blp bln bld bup bun bud) item)
       (Candle_analytic_sqrt clp cln cld cup cun cud center_e)
       (Candle_analytic_sqrt blp bln bld bup bun bud box_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsa_logical_item_sqrt_def;
              candle_fsa_logical_item_q_result_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fsa_item_sqrt_analytic_invariant));;

let candle_fsa_logical_item_atn_analytic_invariant = prove
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
       (candle_fsa_logical_item_atn
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) item)
       (Candle_analytic_atn center_e) (Candle_analytic_atn box_e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsa_logical_item_atn_def;
              candle_fsa_logical_item_q_result_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fsa_item_atn_analytic_invariant));;

let candle_fsa_logical_item_pi_half_analytic_invariant = prove
 (`!boxes (type_witness:real^N).
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_fsa_logical_item_pi_half
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_q_center_environment_list boxes) boxes)
       Candle_analytic_pi_half Candle_analytic_pi_half`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsa_logical_item_pi_half_def;
              candle_fsa_logical_item_q_result_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_ACCEPT_TAC
    (REWRITE_RULE[LET_DEF; LET_END_DEF]
      candle_fsa_item_pi_half_analytic_invariant));;

let candle_fsa_logical_poly_item_analytic_invariant = prove
 (`!e boxes (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_fsa_logical_item_analytic_invariant type_witness boxes
       (candle_fsa_logical_poly_item
         (candle_q_center_environment_list boxes)
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_poly_compile e))
       (Candle_analytic_poly e) (Candle_analytic_poly e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_item_analytic_invariant_def;
              candle_fsa_logical_poly_item_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def] THEN
  MATCH_ACCEPT_TAC candle_fsa_poly_item_analytic_invariant);;

(* Concrete stack effects for instructions emitted by the compiler.  These
   deliberately state the nonempty stack shapes used by the structural
   proof, so the evaluator's fail-closed default cases disappear here. *)

let candle_fsa_logical_program_step_poly = prove
 (`!center_boxes boxes radii use_fixed center_program box_program stack.
     candle_fsa_logical_program_step center_boxes boxes radii use_fixed
       (Candle_analytic_push_poly center_program)
       (Candle_analytic_push_poly box_program) stack =
     CONS
       (candle_fsa_logical_poly_item center_boxes radii center_program)
       stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_analytic_instruction_poly_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsa_logical_program_step_sqrt = prove
 (`!center_boxes boxes radii use_fixed center_s box_s item stack.
     candle_fsa_logical_program_step center_boxes boxes radii use_fixed
       (Candle_analytic_program_sqrt center_s)
       (Candle_analytic_program_sqrt box_s) (CONS item stack) =
     CONS (candle_fsa_logical_item_sqrt radii center_s box_s item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_analytic_instruction_sqrt_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsa_logical_program_step_neg = prove
 (`!center_boxes boxes radii use_fixed item stack.
     candle_fsa_logical_program_step center_boxes boxes radii use_fixed
       Candle_analytic_program_neg Candle_analytic_program_neg
       (CONS item stack) =
     CONS (candle_fsa_logical_item_neg use_fixed radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsa_logical_program_step_add = prove
 (`!center_boxes boxes radii use_fixed left right stack.
     candle_fsa_logical_program_step center_boxes boxes radii use_fixed
       Candle_analytic_program_add Candle_analytic_program_add
       (CONS right (CONS left stack)) =
     CONS (candle_fsa_logical_item_add use_fixed radii left right) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsa_logical_program_step_mul = prove
 (`!center_boxes boxes radii use_fixed left right stack.
     candle_fsa_logical_program_step center_boxes boxes radii use_fixed
       Candle_analytic_program_mul Candle_analytic_program_mul
       (CONS right (CONS left stack)) =
     CONS (candle_fsa_logical_item_mul radii left right) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsa_logical_program_step_square = prove
 (`!center_boxes boxes radii use_fixed item stack.
     candle_fsa_logical_program_step center_boxes boxes radii use_fixed
       Candle_analytic_program_square Candle_analytic_program_square
       (CONS item stack) =
     CONS (candle_fsa_logical_item_square radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsa_logical_program_step_inv = prove
 (`!center_boxes boxes radii use_fixed item stack.
     candle_fsa_logical_program_step center_boxes boxes radii use_fixed
       Candle_analytic_program_inv Candle_analytic_program_inv
       (CONS item stack) =
     CONS (candle_fsa_logical_item_inv radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsa_logical_program_step_atn = prove
 (`!center_boxes boxes radii use_fixed item stack.
     candle_fsa_logical_program_step center_boxes boxes radii use_fixed
       Candle_analytic_program_atn Candle_analytic_program_atn
       (CONS item stack) =
     CONS (candle_fsa_logical_item_atn radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsa_logical_program_step_pi_half = prove
 (`!center_boxes boxes radii use_fixed stack.
     candle_fsa_logical_program_step center_boxes boxes radii use_fixed
       Candle_analytic_program_pi_half Candle_analytic_program_pi_half stack =
     CONS
       (candle_fsa_logical_item_pi_half radii center_boxes boxes) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_logical_program_step_def;
              candle_q_analytic_instruction_tag_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

end;;
