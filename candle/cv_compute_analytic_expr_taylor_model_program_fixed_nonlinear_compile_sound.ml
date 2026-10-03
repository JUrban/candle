(* ========================================================================== *)
(* Compiler substrate for the complete fixed nonlinear Taylor evaluator.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_program_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_compile_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_compile_sound = struct

open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_item_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_program_sound;;

(* Concrete stack effects for instructions emitted by the compiler. *)

let candle_fsn_logical_program_step_poly = prove
 (`!center_boxes boxes radii center_program box_program stack.
     candle_fsn_logical_program_step center_boxes boxes radii
       (Candle_analytic_push_poly center_program)
       (Candle_analytic_push_poly box_program) stack =
     CONS
       (candle_fsa_logical_poly_item center_boxes radii center_program)
       stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_analytic_instruction_poly_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsn_logical_program_step_sqrt = prove
 (`!center_boxes boxes radii center_s box_s item stack.
     candle_fsn_logical_program_step center_boxes boxes radii
       (Candle_analytic_program_sqrt center_s)
       (Candle_analytic_program_sqrt box_s) (CONS item stack) =
     CONS (candle_fsn_logical_item_sqrt radii center_s box_s item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_q_analytic_instruction_sqrt_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsn_logical_program_step_neg = prove
 (`!center_boxes boxes radii item stack.
     candle_fsn_logical_program_step center_boxes boxes radii
       Candle_analytic_program_neg Candle_analytic_program_neg
       (CONS item stack) =
     CONS (candle_fsa_logical_item_neg T radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsn_logical_program_step_add = prove
 (`!center_boxes boxes radii left right stack.
     candle_fsn_logical_program_step center_boxes boxes radii
       Candle_analytic_program_add Candle_analytic_program_add
       (CONS right (CONS left stack)) =
     CONS (candle_fsa_logical_item_add T radii left right) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsn_logical_program_step_mul = prove
 (`!center_boxes boxes radii left right stack.
     candle_fsn_logical_program_step center_boxes boxes radii
       Candle_analytic_program_mul Candle_analytic_program_mul
       (CONS right (CONS left stack)) =
     CONS (candle_fso_logical_item_mul radii left right) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsn_logical_program_step_square = prove
 (`!center_boxes boxes radii item stack.
     candle_fsn_logical_program_step center_boxes boxes radii
       Candle_analytic_program_square Candle_analytic_program_square
       (CONS item stack) =
     CONS (candle_fso_logical_item_square radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsn_logical_program_step_inv = prove
 (`!center_boxes boxes radii item stack.
     candle_fsn_logical_program_step center_boxes boxes radii
       Candle_analytic_program_inv Candle_analytic_program_inv
       (CONS item stack) =
     CONS (candle_fsn_logical_item_inv radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsn_logical_program_step_atn = prove
 (`!center_boxes boxes radii item stack.
     candle_fsn_logical_program_step center_boxes boxes radii
       Candle_analytic_program_atn Candle_analytic_program_atn
       (CONS item stack) =
     CONS (candle_fsn_logical_item_atn radii item) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_logical_program_step_def;
              candle_q_analytic_instruction_tag_def;
              candle_fsa_logical_item_head_def;
              candle_fsa_logical_item_tail_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsn_logical_program_step_pi_half = prove
 (`!center_boxes boxes radii stack.
     candle_fsn_logical_program_step center_boxes boxes radii
       Candle_analytic_program_pi_half Candle_analytic_program_pi_half stack =
     CONS
       (candle_fsn_logical_item_pi_half radii boxes) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_logical_program_step_def;
              candle_q_analytic_instruction_tag_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fsn_logical_program_run_append = prove
 (`!center_left box_left center_right box_right center_boxes boxes radii
      stack.
     LENGTH center_left = LENGTH box_left
     ==>
     candle_fsn_logical_program_run center_boxes boxes radii
       (APPEND center_left center_right) (APPEND box_left box_right) stack =
     candle_fsn_logical_program_run center_boxes boxes radii
       center_right box_right
       (candle_fsn_logical_program_run center_boxes boxes radii
         center_left box_left stack)`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LENGTH; APPEND; candle_fsn_logical_program_run_def] THEN
    ARITH_TAC;
    LIST_INDUCT_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REPEAT GEN_TAC THEN
      REWRITE_TAC[LENGTH; SUC_INJ; APPEND;
                  candle_fsn_logical_program_run_def] THEN
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let candle_fsn_logical_program_run_append_single = prove
 (`!center_program box_program center_instruction box_instruction
      center_boxes boxes radii stack inner result.
     LENGTH center_program = LENGTH box_program /\
     candle_fsn_logical_program_run center_boxes boxes radii
       center_program box_program stack = CONS inner stack /\
     candle_fsn_logical_program_step center_boxes boxes radii
       center_instruction box_instruction (CONS inner stack) =
       CONS result stack
     ==>
     candle_fsn_logical_program_run center_boxes boxes radii
       (APPEND center_program [center_instruction])
       (APPEND box_program [box_instruction]) stack = CONS result stack`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fsn_logical_program_run center_boxes boxes radii
      (APPEND center_program [center_instruction])
      (APPEND box_program [box_instruction]) stack =
    candle_fsn_logical_program_run center_boxes boxes radii
      [center_instruction] [box_instruction]
      (candle_fsn_logical_program_run center_boxes boxes radii
        center_program box_program stack)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fsn_logical_program_run_append THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[candle_fsn_logical_program_run_def]]);;

let candle_fsn_logical_program_run_append_binary = prove
 (`!center_left box_left center_right box_right
      center_instruction box_instruction center_boxes boxes radii stack
      left right result.
     LENGTH center_left = LENGTH box_left /\
     LENGTH center_right = LENGTH box_right /\
     candle_fsn_logical_program_run center_boxes boxes radii
       center_left box_left stack = CONS left stack /\
     candle_fsn_logical_program_run center_boxes boxes radii
       center_right box_right (CONS left stack) =
       CONS right (CONS left stack) /\
     candle_fsn_logical_program_step center_boxes boxes radii
       center_instruction box_instruction (CONS right (CONS left stack)) =
       CONS result stack
     ==>
     candle_fsn_logical_program_run center_boxes boxes radii
       (APPEND center_left (APPEND center_right [center_instruction]))
       (APPEND box_left (APPEND box_right [box_instruction])) stack =
       CONS result stack`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fsn_logical_program_run center_boxes boxes radii
      (APPEND center_left (APPEND center_right [center_instruction]))
      (APPEND box_left (APPEND box_right [box_instruction])) stack =
    candle_fsn_logical_program_run center_boxes boxes radii
      (APPEND center_right [center_instruction])
      (APPEND box_right [box_instruction])
      (candle_fsn_logical_program_run center_boxes boxes radii
        center_left box_left stack)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fsn_logical_program_run_append THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fsn_logical_program_run center_boxes boxes radii
      (APPEND center_right [center_instruction])
      (APPEND box_right [box_instruction]) (CONS left stack) =
    candle_fsn_logical_program_run center_boxes boxes radii
      [center_instruction] [box_instruction]
      (candle_fsn_logical_program_run center_boxes boxes radii
        center_right box_right (CONS left stack))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fsn_logical_program_run_append THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[candle_fsn_logical_program_run_def]]);;

(* Every well-formed analytic expression compiles to exactly one packed item
   and preserves the universal analytic invariant. *)

let candle_fsn_logical_compile_run_analytic_invariant = prove
 (`!box_e center_e boxes stack (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     ?result.
       candle_fsn_logical_program_run
         (candle_q_center_environment_list boxes) boxes
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_analytic_compile center_e)
         (candle_analytic_compile box_e) stack = CONS result stack /\
       candle_fsa_logical_item_analytic_invariant
         type_witness boxes result center_e box_e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `p:candle_poly_expr` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN `center_e = Candle_analytic_poly p` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL [`center_e:candle_analytic_expr`; `p:candle_poly_expr`]
             candle_analytic_erase_poly_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_fsa_logical_poly_item
       (candle_q_center_environment_list boxes)
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (candle_poly_compile p)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def;
                  candle_fsn_logical_program_run_def;
                  candle_fsn_logical_program_step_poly];
      MATCH_MP_TAC candle_fsa_logical_poly_item_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];

    X_GEN_TAC `a:candle_analytic_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a.
        center_e = Candle_analytic_neg center_a /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`]
             candle_analytic_erase_neg_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?inner:candle_fsa_logical_item_type.
        candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS inner stack /\
        candle_fsa_logical_item_analytic_invariant
          (type_witness:real^N) boxes inner center_a a`
     (X_CHOOSE_THEN `inner:candle_fsa_logical_item_type`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_fsa_logical_item_neg T
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (inner:candle_fsa_logical_item_type)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_fsn_logical_program_run_append_single THEN
      EXISTS_TAC `inner:candle_fsa_logical_item_type` THEN
      ASM_REWRITE_TAC
       [candle_analytic_compile_length_certificate_equivalent;
        candle_fsn_logical_program_step_neg] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_fsa_logical_item_neg_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];

    MAP_EVERY X_GEN_TAC
      [`a:candle_analytic_expr`; `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a center_b.
        center_e = Candle_analytic_add center_a center_b /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a /\
        candle_analytic_erase_sqrt_certificates center_b =
          candle_analytic_erase_sqrt_certificates b`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (X_CHOOSE_THEN `center_b:candle_analytic_expr`
         (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`;
              `b:candle_analytic_expr`]
             candle_analytic_erase_add_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?left:candle_fsa_logical_item_type.
        candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS left stack /\
        candle_fsa_logical_item_analytic_invariant
          (type_witness:real^N) boxes left center_a a`
     (X_CHOOSE_THEN `left:candle_fsa_logical_item_type`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "iha" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?right:candle_fsa_logical_item_type.
        candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_b)
          (candle_analytic_compile b) (CONS left stack) =
            CONS right (CONS left stack) /\
        candle_fsa_logical_item_analytic_invariant
          (type_witness:real^N) boxes right center_b b`
     (X_CHOOSE_THEN `right:candle_fsa_logical_item_type`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ihb" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_fsa_logical_item_add T
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (left:candle_fsa_logical_item_type)
       (right:candle_fsa_logical_item_type)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_fsn_logical_program_run_append_binary THEN
      MAP_EVERY EXISTS_TAC
       [`left:candle_fsa_logical_item_type`;
        `right:candle_fsa_logical_item_type`] THEN
      ASM_REWRITE_TAC
       [candle_analytic_compile_length_certificate_equivalent;
        candle_fsn_logical_program_step_add] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_fsa_logical_item_add_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];

    MAP_EVERY X_GEN_TAC
      [`a:candle_analytic_expr`; `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a center_b.
        center_e = Candle_analytic_mul center_a center_b /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a /\
        candle_analytic_erase_sqrt_certificates center_b =
          candle_analytic_erase_sqrt_certificates b`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (X_CHOOSE_THEN `center_b:candle_analytic_expr`
         (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`;
              `b:candle_analytic_expr`]
             candle_analytic_erase_mul_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?left:candle_fsa_logical_item_type.
        candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS left stack /\
        candle_fsa_logical_item_analytic_invariant
          (type_witness:real^N) boxes left center_a a`
     (X_CHOOSE_THEN `left:candle_fsa_logical_item_type`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "iha" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?right:candle_fsa_logical_item_type.
        candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_b)
          (candle_analytic_compile b) (CONS left stack) =
            CONS right (CONS left stack) /\
        candle_fsa_logical_item_analytic_invariant
          (type_witness:real^N) boxes right center_b b`
     (X_CHOOSE_THEN `right:candle_fsa_logical_item_type`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ihb" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_fso_logical_item_mul
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (left:candle_fsa_logical_item_type)
       (right:candle_fsa_logical_item_type)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_fsn_logical_program_run_append_binary THEN
      MAP_EVERY EXISTS_TAC
       [`left:candle_fsa_logical_item_type`;
        `right:candle_fsa_logical_item_type`] THEN
      ASM_REWRITE_TAC
       [candle_analytic_compile_length_certificate_equivalent;
        candle_fsn_logical_program_step_mul] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_fso_logical_item_mul_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];

    X_GEN_TAC `a:candle_analytic_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a.
        center_e = Candle_analytic_square center_a /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`]
             candle_analytic_erase_square_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?inner:candle_fsa_logical_item_type.
        candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS inner stack /\
        candle_fsa_logical_item_analytic_invariant
          (type_witness:real^N) boxes inner center_a a`
     (X_CHOOSE_THEN `inner:candle_fsa_logical_item_type`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_fso_logical_item_square
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (inner:candle_fsa_logical_item_type)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_fsn_logical_program_run_append_single THEN
      EXISTS_TAC `inner:candle_fsa_logical_item_type` THEN
      ASM_REWRITE_TAC
       [candle_analytic_compile_length_certificate_equivalent;
        candle_fsn_logical_program_step_square] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_fso_logical_item_square_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];

    X_GEN_TAC `a:candle_analytic_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a.
        center_e = Candle_analytic_inv center_a /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`]
             candle_analytic_erase_inv_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?inner:candle_fsa_logical_item_type.
        candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS inner stack /\
        candle_fsa_logical_item_analytic_invariant
          (type_witness:real^N) boxes inner center_a a`
     (X_CHOOSE_THEN `inner:candle_fsa_logical_item_type`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_fsn_logical_item_inv
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (inner:candle_fsa_logical_item_type)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_fsn_logical_program_run_append_single THEN
      EXISTS_TAC `inner:candle_fsa_logical_item_type` THEN
      ASM_REWRITE_TAC
       [candle_analytic_compile_length_certificate_equivalent;
        candle_fsn_logical_program_step_inv] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_fsn_logical_item_inv_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];

    MAP_EVERY X_GEN_TAC
      [`blp:num`; `bln:num`; `bld:num`; `bup:num`; `bun:num`; `bud:num`;
       `a:candle_analytic_expr`] THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?clp cln cld cup cun cud center_a.
        center_e = Candle_analytic_sqrt clp cln cld cup cun cud center_a /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a`
     (X_CHOOSE_THEN `clp:num`
       (X_CHOOSE_THEN `cln:num`
        (X_CHOOSE_THEN `cld:num`
         (X_CHOOSE_THEN `cup:num`
          (X_CHOOSE_THEN `cun:num`
           (X_CHOOSE_THEN `cud:num`
            (X_CHOOSE_THEN `center_a:candle_analytic_expr`
              (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))))))) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`]
             candle_analytic_erase_sqrt_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?inner:candle_fsa_logical_item_type.
        candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS inner stack /\
        candle_fsa_logical_item_analytic_invariant
          (type_witness:real^N) boxes inner center_a a`
     (X_CHOOSE_THEN `inner:candle_fsa_logical_item_type`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_fsn_logical_item_sqrt
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (candle_analytic_sqrt_interval clp cln cld cup cun cud)
       (candle_analytic_sqrt_interval blp bln bld bup bun bud)
       (inner:candle_fsa_logical_item_type)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_fsn_logical_program_run_append_single THEN
      EXISTS_TAC `inner:candle_fsa_logical_item_type` THEN
      ASM_REWRITE_TAC
       [candle_analytic_compile_length_certificate_equivalent;
        candle_fsn_logical_program_step_sqrt] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_fsn_logical_item_sqrt_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def;
                      candle_analytic_erase_sqrt_certificates_def]];

    X_GEN_TAC `a:candle_analytic_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a.
        center_e = Candle_analytic_atn center_a /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`]
             candle_analytic_erase_atn_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?inner:candle_fsa_logical_item_type.
        candle_fsn_logical_program_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS inner stack /\
        candle_fsa_logical_item_analytic_invariant
          (type_witness:real^N) boxes inner center_a a`
     (X_CHOOSE_THEN `inner:candle_fsa_logical_item_type`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_fsn_logical_item_atn
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (inner:candle_fsa_logical_item_type)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_fsn_logical_program_run_append_single THEN
      EXISTS_TAC `inner:candle_fsa_logical_item_type` THEN
      ASM_REWRITE_TAC
       [candle_analytic_compile_length_certificate_equivalent;
        candle_fsn_logical_program_step_atn] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_fsn_logical_item_atn_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];

    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN `center_e = Candle_analytic_pi_half` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPEC `center_e:candle_analytic_expr`
             candle_analytic_erase_pi_half_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_fsn_logical_item_pi_half
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       boxes` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def;
                  candle_fsn_logical_program_run_def;
                  candle_fsn_logical_program_step_pi_half];
      MATCH_MP_TAC candle_fsn_logical_item_pi_half_analytic_invariant THEN
      ASM_REWRITE_TAC[]]]);;

end;;
