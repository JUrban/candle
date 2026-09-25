(* ========================================================================== *)
(* Source compilation soundness for the centered Taylor-model checker.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_nonlinear_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_compile_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_sound;;
open Candle_cv_analytic_poly_inv;;
open Candle_cv_analytic_dim_jet_pi_half;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_nonlinear_sound;;
open Candle_cv_whole_box_dim_taylor_sound;;

let candle_q_dim_taylor_model_result_poly_analytic_invariant = prove
 (`!e boxes (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_complete
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) T
         (candle_q_dim_poly_jet_normalized
           (candle_q_center_environment_list boxes) e)
         (candle_q_dim_jet_hessian
           (candle_q_dim_poly_jet_normalized boxes e)))
       (Candle_analytic_poly e) (Candle_analytic_poly e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_regular_at_def];
      REWRITE_TAC[candle_analytic_regular_at_def];
      MATCH_MP_TAC candle_q_dim_poly_jet_normalized_center_shape THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def;
                  GSYM candle_q_dim_poly_contains_components] THEN
      MATCH_MP_TAC candle_q_dim_poly_jet_normalized_center_sound THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_dim_poly_jet_normalized_box_shape THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def;
                  GSYM candle_q_dim_poly_contains_components] THEN
      MP_TAC
        (ISPECL
          [`e:candle_poly_expr`;
           `boxes:(((num#num)#num)#((num#num)#num))list`]
          candle_q_dim_poly_jet_normalized_box_sound) THEN
      ASM_MESON_TAC[]]]);;

let candle_q_dim_taylor_model_poly_neg_invariant = prove
 (`!e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       result
       (Candle_analytic_neg (Candle_analytic_poly e))
       (Candle_analytic_neg (Candle_analytic_poly e)) <=>
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       result
       (Candle_analytic_poly (Candle_poly_neg e))
       (Candle_analytic_poly (Candle_poly_neg e))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_analytic_regular_at_def;
              candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def]);;

let candle_q_dim_taylor_model_poly_add_invariant = prove
 (`!a b boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       result
       (Candle_analytic_add
         (Candle_analytic_poly a) (Candle_analytic_poly b))
       (Candle_analytic_add
         (Candle_analytic_poly a) (Candle_analytic_poly b)) <=>
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       result
       (Candle_analytic_poly (Candle_poly_add a b))
       (Candle_analytic_poly (Candle_poly_add a b))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_analytic_regular_at_def;
              candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def]);;

let candle_q_dim_taylor_model_poly_mul_invariant = prove
 (`!a b boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       result
       (Candle_analytic_mul
         (Candle_analytic_poly a) (Candle_analytic_poly b))
       (Candle_analytic_mul
         (Candle_analytic_poly a) (Candle_analytic_poly b)) <=>
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       result
       (Candle_analytic_poly (Candle_poly_mul a b))
       (Candle_analytic_poly (Candle_poly_mul a b))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_analytic_regular_at_def;
              candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def;
              REAL_MUL_SYM]);;

let candle_q_dim_taylor_model_poly_square_invariant = prove
 (`!a boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       result (Candle_analytic_square (Candle_analytic_poly a))
       (Candle_analytic_square (Candle_analytic_poly a)) <=>
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       result
       (Candle_analytic_poly (Candle_poly_square a))
       (Candle_analytic_poly (Candle_poly_square a))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_analytic_regular_at_def;
              candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def;
              REAL_MUL_SYM]);;

let candle_q_dim_taylor_model_poly_constant_analytic_invariant = prove
 (`!p n d boxes (type_witness:real^N).
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_poly_constant
         (candle_q_center_environment_list boxes) boxes
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         ((p,n),d))
       (Candle_analytic_poly (Candle_poly_const p n d))
       (Candle_analytic_poly (Candle_poly_const p n d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`Candle_poly_const p n d`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `type_witness:real^N`]
      candle_q_dim_taylor_model_result_poly_analytic_invariant) THEN
  ASM_REWRITE_TAC[candle_poly_valid_dim_def;
                  candle_q_dim_taylor_model_poly_constant_def;
                  candle_q_dim_poly_jet_normalized_def;
                  candle_q_dim_jet_normalized_constant_def;
                  candle_q_dim_jet_hessian_def;
                  candle_q_dim_jet_make_def; FST; SND]);;

let candle_q_dim_taylor_model_poly_variable_analytic_invariant = prove
 (`!variable boxes (type_witness:real^N).
     variable < dimindex (:N) /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_poly_variable
         (candle_q_center_environment_list boxes) boxes
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         variable)
       (Candle_analytic_poly (Candle_poly_var variable))
       (Candle_analytic_poly (Candle_poly_var variable))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`Candle_poly_var variable`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `type_witness:real^N`]
      candle_q_dim_taylor_model_result_poly_analytic_invariant) THEN
  ASM_REWRITE_TAC[candle_poly_valid_dim_def;
                  candle_q_dim_taylor_model_poly_variable_def;
                  candle_q_dim_poly_jet_normalized_def;
                  candle_q_dim_jet_normalized_variable_def;
                  candle_q_dim_jet_hessian_def;
                  candle_q_dim_jet_make_def; FST; SND]);;

let candle_q_dim_taylor_model_poly_run_append = prove
 (`!left right center_boxes boxes radii stack.
     candle_q_dim_taylor_model_poly_run center_boxes boxes radii
       (APPEND left right) stack =
     candle_q_dim_taylor_model_poly_run center_boxes boxes radii right
       (candle_q_dim_taylor_model_poly_run
         center_boxes boxes radii left stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; candle_q_dim_taylor_model_poly_run_def]);;

let candle_q_dim_taylor_model_poly_compile_run_analytic_invariant = prove
 (`!e boxes stack (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     ?result.
       candle_q_dim_taylor_model_poly_run
         (candle_q_center_environment_list boxes) boxes
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_poly_compile e) stack = CONS result stack /\
       candle_q_dim_taylor_model_result_analytic_invariant
         type_witness boxes result
         (Candle_analytic_poly e) (Candle_analytic_poly e)`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:num`; `n:num`; `d:num`] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_poly_constant
       (candle_q_center_environment_list boxes) boxes
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       ((p,n),d)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_poly_compile_def;
                  candle_q_dim_taylor_model_poly_run_def;
                  candle_q_dim_taylor_model_poly_step_def];
      MATCH_MP_TAC
        candle_q_dim_taylor_model_poly_constant_analytic_invariant THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `i:num` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_poly_variable
       (candle_q_center_environment_list boxes) boxes
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)) i` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_poly_compile_def;
                  candle_q_dim_taylor_model_poly_run_def;
                  candle_q_dim_taylor_model_poly_step_def];
      MATCH_MP_TAC
        candle_q_dim_taylor_model_poly_variable_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_poly_valid_dim_def]];
    X_GEN_TAC `a:candle_poly_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?inner.
        candle_q_dim_taylor_model_poly_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_poly_compile a) stack = CONS inner stack /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes inner
          (Candle_analytic_poly a) (Candle_analytic_poly a)`
     (X_CHOOSE_THEN
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
     STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_MESON_TAC[candle_poly_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_neg
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_poly_compile_def;
                      candle_q_dim_taylor_model_poly_run_append;
                      candle_q_dim_taylor_model_poly_run_def;
                      candle_q_dim_taylor_model_poly_step_def;
                      candle_q_dim_taylor_model_result_head_def;
                      candle_q_dim_taylor_model_result_tail_def; APPEND];
      ONCE_REWRITE_TAC
       [GSYM candle_q_dim_taylor_model_poly_neg_invariant] THEN
      MATCH_MP_TAC
        candle_q_dim_taylor_model_result_neg_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_poly_valid_dim_def;
                      candle_analytic_valid_dim_def;
                      candle_analytic_erase_sqrt_certificates_def]];
    MAP_EVERY X_GEN_TAC [`a:candle_poly_expr`; `b:candle_poly_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?left.
        candle_q_dim_taylor_model_poly_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_poly_compile a) stack = CONS left stack /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes left
          (Candle_analytic_poly a) (Candle_analytic_poly a)`
     (X_CHOOSE_THEN
       `left:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "iha" MATCH_MP_TAC THEN
      ASM_MESON_TAC[candle_poly_valid_dim_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?right.
        candle_q_dim_taylor_model_poly_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_poly_compile b) (CONS left stack) =
            CONS right (CONS left stack) /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes right
          (Candle_analytic_poly b) (Candle_analytic_poly b)`
     (X_CHOOSE_THEN
       `right:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ihb" MATCH_MP_TAC THEN
      ASM_MESON_TAC[candle_poly_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_add
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (left:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)
       (right:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_poly_compile_def;
                      candle_q_dim_taylor_model_poly_run_append;
                      candle_q_dim_taylor_model_poly_run_def;
                      candle_q_dim_taylor_model_poly_step_def;
                      candle_q_dim_taylor_model_result_head_def;
                      candle_q_dim_taylor_model_result_tail_def; APPEND];
      ONCE_REWRITE_TAC
       [GSYM candle_q_dim_taylor_model_poly_add_invariant] THEN
      MATCH_MP_TAC
        candle_q_dim_taylor_model_result_add_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_poly_valid_dim_def;
                      candle_analytic_valid_dim_def;
                      candle_analytic_erase_sqrt_certificates_def]];
    MAP_EVERY X_GEN_TAC [`a:candle_poly_expr`; `b:candle_poly_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?left.
        candle_q_dim_taylor_model_poly_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_poly_compile a) stack = CONS left stack /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes left
          (Candle_analytic_poly a) (Candle_analytic_poly a)`
     (X_CHOOSE_THEN
       `left:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "iha" MATCH_MP_TAC THEN
      ASM_MESON_TAC[candle_poly_valid_dim_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?right.
        candle_q_dim_taylor_model_poly_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_poly_compile b) (CONS left stack) =
            CONS right (CONS left stack) /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes right
          (Candle_analytic_poly b) (Candle_analytic_poly b)`
     (X_CHOOSE_THEN
       `right:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ihb" MATCH_MP_TAC THEN
      ASM_MESON_TAC[candle_poly_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_mul
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (left:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)
       (right:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_poly_compile_def;
                      candle_q_dim_taylor_model_poly_run_append;
                      candle_q_dim_taylor_model_poly_run_def;
                      candle_q_dim_taylor_model_poly_step_def;
                      candle_q_dim_taylor_model_result_head_def;
                      candle_q_dim_taylor_model_result_tail_def; APPEND];
      ONCE_REWRITE_TAC
       [GSYM candle_q_dim_taylor_model_poly_mul_invariant] THEN
      MATCH_MP_TAC
        candle_q_dim_taylor_model_result_mul_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_poly_valid_dim_def;
                      candle_analytic_valid_dim_def;
                      candle_analytic_erase_sqrt_certificates_def]];
    X_GEN_TAC `a:candle_poly_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?inner.
        candle_q_dim_taylor_model_poly_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_poly_compile a) stack = CONS inner stack /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes inner
          (Candle_analytic_poly a) (Candle_analytic_poly a)`
     (X_CHOOSE_THEN
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_MESON_TAC[candle_poly_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_square
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_poly_compile_def;
                      candle_q_dim_taylor_model_poly_run_append;
                      candle_q_dim_taylor_model_poly_run_def;
                      candle_q_dim_taylor_model_poly_step_def;
                      candle_q_dim_taylor_model_result_head_def;
                      candle_q_dim_taylor_model_result_tail_def; APPEND];
      ONCE_REWRITE_TAC
       [GSYM candle_q_dim_taylor_model_poly_square_invariant] THEN
      MATCH_MP_TAC
        candle_q_dim_taylor_model_result_square_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_poly_valid_dim_def;
                      candle_analytic_valid_dim_def;
                      candle_analytic_erase_sqrt_certificates_def]]] THEN
  ASM_MESON_TAC[candle_poly_valid_dim_def]);;

let candle_q_dim_taylor_model_poly_compile_analytic_invariant = prove
 (`!e boxes (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_poly_program
         (candle_q_center_environment_list boxes) boxes
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_poly_compile e))
       (Candle_analytic_poly e) (Candle_analytic_poly e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`e:candle_poly_expr`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `[]:
          (bool#
           ((((num#num)#num)#(num#num)#num)#
            (((num#num)#num)#(num#num)#num)list#
            ((((num#num)#num)#(num#num)#num)list)list)#
           (((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)list`;
       `type_witness:real^N`]
      candle_q_dim_taylor_model_poly_compile_run_analytic_invariant) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (X_CHOOSE_THEN
      `result:
         bool#
         ((((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)#
         (((num#num)#num)#(num#num)#num)#
         (((num#num)#num)#(num#num)#num)list#
         ((((num#num)#num)#(num#num)#num)list)list`
      STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[candle_q_dim_taylor_model_poly_program_def;
                  candle_q_dim_taylor_model_result_head_def]);;

let candle_q_dim_taylor_model_program_run_append = prove
 (`!center_left box_left center_right box_right center_boxes boxes radii stack.
     LENGTH center_left = LENGTH box_left
     ==>
     candle_q_dim_taylor_model_program_run center_boxes boxes radii
       (APPEND center_left center_right) (APPEND box_left box_right) stack =
     candle_q_dim_taylor_model_program_run center_boxes boxes radii
       center_right box_right
       (candle_q_dim_taylor_model_program_run center_boxes boxes radii
         center_left box_left stack)`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LENGTH; APPEND; candle_q_dim_taylor_model_program_run_def] THEN
    ARITH_TAC;
    LIST_INDUCT_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REPEAT GEN_TAC THEN
      REWRITE_TAC[LENGTH; SUC_INJ; APPEND;
                  candle_q_dim_taylor_model_program_run_def] THEN
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let candle_q_dim_taylor_model_pi_half_hessian = prove
 (`!boxes.
     candle_q_dim_interval_zero_matrix_like boxes boxes =
     candle_q_dim_jet_hessian (candle_q_dim_jet_pi_half boxes)`,
  REWRITE_TAC[candle_q_dim_jet_pi_half_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND]);;

let candle_q_dim_taylor_model_result_pi_half_analytic_invariant = prove
 (`!boxes (type_witness:real^N).
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_pi_half
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_q_center_environment_list boxes) boxes)
       Candle_analytic_pi_half Candle_analytic_pi_half`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_pi_half_def;
              candle_q_dim_taylor_model_pi_half_hessian] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  ASM_REWRITE_TAC[candle_analytic_valid_dim_def;
                  candle_analytic_erase_sqrt_certificates_def] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_analytic_regular_at_def];
    REWRITE_TAC[candle_analytic_regular_at_def];
    ASM_MESON_TAC[candle_q_dim_jet_pi_half_shape;
                  candle_q_center_environment_list_length];
    REWRITE_TAC[candle_q_dim_analytic_contains_def;
                candle_analytic_value_def;
                candle_analytic_d_def;
                candle_analytic_dd_def] THEN
    ASM_MESON_TAC[candle_q_dim_jet_pi_half_components_sound;
                  candle_q_center_environment_list_length];
    ASM_MESON_TAC[candle_q_dim_jet_pi_half_shape];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[candle_q_dim_analytic_contains_def;
                candle_analytic_value_def;
                candle_analytic_d_def;
                candle_analytic_dd_def] THEN
    ASM_MESON_TAC[candle_q_dim_jet_pi_half_components_sound]]);;

end;;
