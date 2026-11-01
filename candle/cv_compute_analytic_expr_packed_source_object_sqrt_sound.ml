(* ========================================================================== *)
(* Exact object-q certified square-root operation.                           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file connects the exact root and        *)
(* positive-reciprocal certificates produced by the verified word evaluator *)
(* to the production packed object-q unary constructor.                     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_inverse_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certified_sqrt_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_sqrt_sound = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_sqrt_certificate;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_domain;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_core;;
open Candle_cv_analytic_expr_packed_source_certified_sqrt_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_recomplete_sound;;
open Candle_cv_analytic_expr_packed_source_object_mul_sound;;
open Candle_cv_analytic_expr_packed_source_object_unary_sound;;

let candle_q_packed_object_sqrt_derivative_sound = prove
 (`!input root_interval derivative_interval x.
     candle_q_interval_sqrt_certificate input root_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add root_interval root_interval)
       derivative_interval /\
     candle_q_interval_contains input x
     ==>
     candle_q_interval_contains derivative_interval
       (inv (sqrt x + sqrt x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_interval_contains root_interval (sqrt x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`input:((num#num)#num)#((num#num)#num)`;
         `root_interval:((num#num)#num)#((num#num)#num)`; `x:real`]
        candle_q_interval_sqrt_certificate_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_interval_add root_interval root_interval)
      (sqrt x + sqrt x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`candle_q_interval_add root_interval root_interval`;
         `derivative_interval:((num#num)#num)#((num#num)#num)`;
         `sqrt x + sqrt x`]
        candle_q_interval_inv_certificate_sound) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_sqrt_second_reciprocal_sound = prove
 (`!input root_interval second_reciprocal x.
     candle_q_interval_sqrt_certificate input root_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_mul
         (candle_q_interval_add root_interval root_interval)
         (candle_q_interval_add input input))
       second_reciprocal /\
     candle_q_interval_contains input x
     ==>
     candle_q_interval_contains second_reciprocal
       (inv ((sqrt x + sqrt x) * (x + x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_interval_contains root_interval (sqrt x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`input:((num#num)#num)#((num#num)#num)`;
         `root_interval:((num#num)#num)#((num#num)#num)`; `x:real`]
        candle_q_interval_sqrt_certificate_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_interval_add root_interval root_interval)
      (sqrt x + sqrt x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_interval_add input input) (x + x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_interval_mul
        (candle_q_interval_add root_interval root_interval)
        (candle_q_interval_add input input))
      ((sqrt x + sqrt x) * (x + x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_interval_mul_sound THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`candle_q_interval_mul
           (candle_q_interval_add root_interval root_interval)
           (candle_q_interval_add input input)`;
         `second_reciprocal:((num#num)#num)#((num#num)#num)`;
         `(sqrt x + sqrt x) * (x + x)`]
        candle_q_interval_inv_certificate_sound) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_sqrt_second_sound = prove
 (`!input root_interval second_reciprocal x.
     candle_q_interval_sqrt_certificate input root_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_mul
         (candle_q_interval_add root_interval root_interval)
         (candle_q_interval_add input input))
       second_reciprocal /\
     candle_q_interval_contains input x
     ==>
     candle_q_interval_contains
       (candle_q_interval_neg second_reciprocal)
       (--inv ((sqrt x + sqrt x) * (x + x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_interval_neg_sound THEN
  MATCH_MP_TAC
    (SPECL
      [`input:((num#num)#num)#((num#num)#num)`;
       `root_interval:((num#num)#num)#((num#num)#num)`;
       `second_reciprocal:((num#num)#num)#((num#num)#num)`; `x:real`]
      candle_q_packed_object_sqrt_second_reciprocal_sound) THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_sqrt_certificates_value_positive = prove
 (`!input root_interval derivative_interval value.
     candle_q_interval_sqrt_certificate input root_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add root_interval root_interval)
       derivative_interval /\
     candle_q_interval_contains input value
     ==> &0 < value`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= value` ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_interval_sqrt_certificate_input_nonnegative];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains root_interval (sqrt value)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`input:((num#num)#num)#((num#num)#num)`;
         `root_interval:((num#num)#num)#((num#num)#num)`; `value:real`]
        candle_q_interval_sqrt_certificate_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_interval_add root_interval root_interval)
      (sqrt value + sqrt value)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(sqrt value + sqrt value = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_interval_not_zero_contains_nonzero THEN
    EXISTS_TAC
      `candle_q_interval_add root_interval root_interval:
        ((num#num)#num)#((num#num)#num)` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[candle_q_interval_inv_certificate_def];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt value` ASSUME_TAC THENL
   [MP_TAC (SPEC `value:real` SQRT_POS_LE) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC (SPEC `value:real` SQRT_LT_0) THEN ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_center_first_sqrt_contains = prove
 (`!source_value source_gradient source_e root_interval
       derivative_interval environment.
     LENGTH source_gradient = 6 /\
     candle_q_interval_sqrt_certificate source_value root_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add root_interval root_interval)
       derivative_interval /\
     candle_q_packed_object_center_first_contains
       source_value source_gradient environment source_e
     ==>
     candle_q_packed_object_center_first_contains root_interval
       (candle_q_packed_object_interval_list_scale
         derivative_interval source_gradient)
       environment
       (candle_packed_analytic_sqrt_with_interval root_interval source_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_object_center_first_contains_def]) THEN
  REWRITE_TAC[candle_q_packed_object_center_first_contains_def;
              candle_packed_analytic_sqrt_with_interval_def;
              candle_analytic_value_def; candle_analytic_d_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `root_interval:((num#num)#num)#((num#num)#num)`;
         `candle_analytic_value environment source_e`]
        candle_q_interval_sqrt_certificate_sound) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_interval_list_scale_lookup] THEN
    MATCH_MP_TAC candle_q_interval_mul_sound THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`source_value:((num#num)#num)#((num#num)#num)`;
           `root_interval:((num#num)#num)#((num#num)#num)`;
           `derivative_interval:((num#num)#num)#((num#num)#num)`;
           `candle_analytic_value environment source_e`]
          candle_q_packed_object_sqrt_derivative_sound) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

let candle_q_packed_object_sqrt_hessian6_contains = prove
 (`!source_value source_gradient source_hessian source_e root_interval
       derivative_interval second_reciprocal environment.
     LENGTH source_gradient = 6 /\ LENGTH source_hessian = 21 /\
     candle_q_interval_sqrt_certificate source_value root_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add root_interval root_interval)
       derivative_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_mul
         (candle_q_interval_add root_interval root_interval)
         (candle_q_interval_add source_value source_value))
       second_reciprocal /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         source_value source_gradient source_hessian)
       environment source_e
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_unary_hessian6 derivative_interval
         (candle_q_interval_neg second_reciprocal)
         source_gradient source_hessian)
       (candle_q_packed_hessian6_values
         (\i j. candle_analytic_dd i j environment
           (candle_packed_analytic_sqrt_with_interval
             root_interval source_e)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let source_components =
    REWRITE_RULE
      [candle_q_dim_analytic_contains_def;
       candle_q_dim_jet_contains_components_def;
       candle_q_packed_object_box_jet_def;
       candle_q_dim_jet_f_def;
       candle_q_dim_jet_make_def; FST; SND]
      (ASSUME
        `candle_q_dim_analytic_contains 6
          (candle_q_packed_object_box_jet
            source_value source_gradient source_hessian)
          environment source_e`) in
  let value_contains,_ = CONJ_PAIR source_components in
  ASSUME_TAC value_contains THEN
  let source_stacks =
    MATCH_MP
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `source_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `source_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `environment:real list`; `source_e:candle_analytic_expr`]
        candle_q_packed_object_box_source_stacks)
      (end_itlist CONJ
        [ASSUME
           `LENGTH
             (source_gradient:
               (((num#num)#num)#((num#num)#num))list) = 6`;
         ASSUME
           `LENGTH
             (source_hessian:
               (((num#num)#num)#((num#num)#num))list) = 21`;
         ASSUME
           `candle_q_dim_analytic_contains 6
             (candle_q_packed_object_box_jet
               source_value source_gradient source_hessian)
             environment source_e`]) in
  let gradient_stack,hessian_stack = CONJ_PAIR source_stacks in
  ASSUME_TAC gradient_stack THEN ASSUME_TAC hessian_stack THEN
  SUBGOAL_THEN
   `candle_q_interval_contains derivative_interval
      (inv
        (sqrt (candle_analytic_value environment source_e) +
         sqrt (candle_analytic_value environment source_e)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `root_interval:((num#num)#num)#((num#num)#num)`;
         `derivative_interval:((num#num)#num)#((num#num)#num)`;
         `candle_analytic_value environment source_e`]
        candle_q_packed_object_sqrt_derivative_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_interval_neg second_reciprocal)
      (--inv
        ((sqrt (candle_analytic_value environment source_e) +
          sqrt (candle_analytic_value environment source_e)) *
         (candle_analytic_value environment source_e +
          candle_analytic_value environment source_e)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `root_interval:((num#num)#num)#((num#num)#num)`;
         `second_reciprocal:((num#num)#num)#((num#num)#num)`;
         `candle_analytic_value environment source_e`]
        candle_q_packed_object_sqrt_second_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (SPECL
      [`derivative_interval:((num#num)#num)#((num#num)#num)`;
       `candle_q_interval_neg second_reciprocal`;
       `source_gradient:
          (((num#num)#num)#((num#num)#num))list`;
       `source_hessian:
          (((num#num)#num)#((num#num)#num))list`;
       `inv
          (sqrt (candle_analytic_value environment source_e) +
           sqrt (candle_analytic_value environment source_e))`;
       `--inv
          ((sqrt (candle_analytic_value environment source_e) +
            sqrt (candle_analytic_value environment source_e)) *
           (candle_analytic_value environment source_e +
            candle_analytic_value environment source_e))`;
       `(\i. candle_analytic_d i environment source_e):num->real`;
       `(\i j. candle_analytic_dd i j environment source_e):
          num->num->real`]
      candle_q_packed_object_unary_hessian6_sound) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN (LABEL_TAC "unary_hessian") THEN
    SUBGOAL_THEN
     `(\i j.
         (--inv
           ((sqrt (candle_analytic_value environment source_e) +
             sqrt (candle_analytic_value environment source_e)) *
            (candle_analytic_value environment source_e +
             candle_analytic_value environment source_e))) *
           (candle_analytic_d i environment source_e *
            candle_analytic_d j environment source_e) +
         inv
           (sqrt (candle_analytic_value environment source_e) +
            sqrt (candle_analytic_value environment source_e)) *
           candle_analytic_dd i j environment source_e) =
      (\i j. candle_analytic_dd i j environment
        (candle_packed_analytic_sqrt_with_interval
          root_interval source_e))`
    (LABEL_TAC "sqrt_hessian_formula") THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
      REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                  candle_analytic_dd_def] THEN CONV_TAC REAL_RING;
      USE_THEN "unary_hessian" MP_TAC THEN BETA_TAC THEN
      ASM_REWRITE_TAC[]]]);;

let candle_q_packed_object_box_sqrt_contains = prove
 (`!source_value source_gradient source_hessian source_e root_interval
       derivative_interval second_reciprocal environment.
     LENGTH source_gradient = 6 /\ LENGTH source_hessian = 21 /\
     candle_q_interval_sqrt_certificate source_value root_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add root_interval root_interval)
       derivative_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_mul
         (candle_q_interval_add root_interval root_interval)
         (candle_q_interval_add source_value source_value))
       second_reciprocal /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         source_value source_gradient source_hessian)
       environment source_e
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet root_interval
         (candle_q_packed_object_interval_list_scale
           derivative_interval source_gradient)
         (candle_q_packed_object_unary_hessian6 derivative_interval
           (candle_q_interval_neg second_reciprocal)
           source_gradient source_hessian))
       environment
       (candle_packed_analytic_sqrt_with_interval root_interval source_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let source_components =
    REWRITE_RULE
      [candle_q_dim_analytic_contains_def;
       candle_q_dim_jet_contains_components_def;
       candle_q_packed_object_box_jet_def;
       candle_q_dim_jet_f_def;
       candle_q_dim_jet_gradient_at_def;
       candle_q_dim_jet_hessian_at_def;
       candle_q_dim_jet_gradient_def;
       candle_q_dim_jet_hessian_def;
       candle_q_dim_jet_make_def; FST; SND]
      (ASSUME
        `candle_q_dim_analytic_contains 6
          (candle_q_packed_object_box_jet
            source_value source_gradient source_hessian)
          environment source_e`) in
  let value_contains,source_derivatives = CONJ_PAIR source_components in
  let gradient_contains,_ = CONJ_PAIR source_derivatives in
  ASSUME_TAC value_contains THEN ASSUME_TAC gradient_contains THEN
  SUBGOAL_THEN
   `candle_q_stack_contains
      (candle_q_packed_object_unary_hessian6 derivative_interval
        (candle_q_interval_neg second_reciprocal)
        source_gradient source_hessian)
      (candle_q_packed_hessian6_values
        (\i j. candle_analytic_dd i j environment
          (candle_packed_analytic_sqrt_with_interval
            root_interval source_e)))`
  (LABEL_TAC "output_hessian") THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `source_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `source_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `source_e:candle_analytic_expr`;
         `root_interval:((num#num)#num)#((num#num)#num)`;
         `derivative_interval:((num#num)#num)#((num#num)#num)`;
         `second_reciprocal:((num#num)#num)#((num#num)#num)`;
         `environment:real list`]
        candle_q_packed_object_sqrt_hessian6_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "output_hessian"
    (fun theorem ->
      LABEL_TAC "output_hessian_unfolded"
        (REWRITE_RULE
          [candle_packed_analytic_sqrt_with_interval_def] theorem)) THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_packed_object_box_jet_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def;
              candle_packed_analytic_sqrt_with_interval_def;
              candle_analytic_value_def;
              candle_analytic_d_def; FST; SND] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `root_interval:((num#num)#num)#((num#num)#num)`;
         `candle_analytic_value environment source_e`]
        candle_q_interval_sqrt_certificate_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_interval_list_scale_lookup] THEN
    MATCH_MP_TAC candle_q_interval_mul_sound THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`source_value:((num#num)#num)#((num#num)#num)`;
           `root_interval:((num#num)#num)#((num#num)#num)`;
           `derivative_interval:((num#num)#num)#((num#num)#num)`;
           `candle_analytic_value environment source_e`]
          candle_q_packed_object_sqrt_derivative_sound) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC candle_q_packed_object_analytic_hessian_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_box_sqrt_shape = prove
 (`!source_gradient source_hessian root_interval derivative_interval
       second_reciprocal.
     LENGTH source_gradient = 6
     ==>
     candle_q_dim_jet_shape 6
       (candle_q_packed_object_box_jet root_interval
         (candle_q_packed_object_interval_list_scale
           derivative_interval source_gradient)
         (candle_q_packed_object_unary_hessian6 derivative_interval
           (candle_q_interval_neg second_reciprocal)
           source_gradient source_hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_packed_object_box_jet_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_all] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_packed_object_interval_list_scale_length];
    REWRITE_TAC[candle_q_packed_hessian6_expand_shape]]);;

let candle_q_packed_object_center_all_sqrt_contains = prove
 (`!center_boxes source_value source_gradient source_e root_interval
       derivative_interval.
     LENGTH source_gradient = 6 /\
     candle_q_interval_sqrt_certificate source_value root_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add root_interval root_interval)
       derivative_interval /\
     (!environment.
        candle_q_stack_contains center_boxes environment
        ==> candle_analytic_regular_at environment source_e /\
            candle_q_packed_object_center_first_contains
              source_value source_gradient environment source_e)
     ==>
     (!environment.
        candle_q_stack_contains center_boxes environment
        ==> candle_analytic_regular_at environment
              (candle_packed_analytic_sqrt_with_interval
                root_interval source_e) /\
            candle_q_packed_object_center_first_contains root_interval
              (candle_q_packed_object_interval_list_scale
                derivative_interval source_gradient)
              environment
              (candle_packed_analytic_sqrt_with_interval
                root_interval source_e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
  let source_at =
    MATCH_MP
      (SPEC `environment:real list`
        (ASSUME
          `!environment.
             candle_q_stack_contains center_boxes environment
             ==> candle_analytic_regular_at environment source_e /\
                 candle_q_packed_object_center_first_contains
                   source_value source_gradient environment source_e`))
      (ASSUME `candle_q_stack_contains center_boxes environment`) in
  let source_regular,source_contains = CONJ_PAIR source_at in
  ASSUME_TAC source_regular THEN ASSUME_TAC source_contains THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                candle_analytic_regular_at_def] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC
        (SPECL
          [`source_value:((num#num)#num)#((num#num)#num)`;
           `root_interval:((num#num)#num)#((num#num)#num)`;
           `derivative_interval:((num#num)#num)#((num#num)#num)`;
           `candle_analytic_value environment source_e`]
          candle_q_packed_object_sqrt_certificates_value_positive) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC source_contains THEN
      REWRITE_TAC[candle_q_packed_object_center_first_contains_def] THEN
      MESON_TAC[]];
    MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `source_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `source_e:candle_analytic_expr`;
         `root_interval:((num#num)#num)#((num#num)#num)`;
         `derivative_interval:((num#num)#num)#((num#num)#num)`;
         `environment:real list`]
        candle_q_packed_object_center_first_sqrt_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_box_all_sqrt_contains = prove
 (`!outer_boxes source_value source_gradient source_hessian source_e
       root_interval derivative_interval second_reciprocal.
     LENGTH source_gradient = 6 /\ LENGTH source_hessian = 21 /\
     candle_q_interval_sqrt_certificate source_value root_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add root_interval root_interval)
       derivative_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_mul
         (candle_q_interval_add root_interval root_interval)
         (candle_q_interval_add source_value source_value))
       second_reciprocal /\
     (!environment.
        candle_q_stack_contains outer_boxes environment
        ==> candle_analytic_regular_at environment source_e /\
            candle_q_dim_analytic_contains 6
              (candle_q_packed_object_box_jet
                source_value source_gradient source_hessian)
              environment source_e)
     ==>
     (!environment.
        candle_q_stack_contains outer_boxes environment
        ==> candle_analytic_regular_at environment
              (candle_packed_analytic_sqrt_with_interval
                root_interval source_e) /\
            candle_q_dim_analytic_contains 6
              (candle_q_packed_object_box_jet root_interval
                (candle_q_packed_object_interval_list_scale
                  derivative_interval source_gradient)
                (candle_q_packed_object_unary_hessian6
                  derivative_interval
                  (candle_q_interval_neg second_reciprocal)
                  source_gradient source_hessian))
              environment
              (candle_packed_analytic_sqrt_with_interval
                root_interval source_e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
  let source_at =
    MATCH_MP
      (SPEC `environment:real list`
        (ASSUME
          `!environment.
             candle_q_stack_contains outer_boxes environment
             ==> candle_analytic_regular_at environment source_e /\
                 candle_q_dim_analytic_contains 6
                   (candle_q_packed_object_box_jet
                     source_value source_gradient source_hessian)
                   environment source_e`))
      (ASSUME `candle_q_stack_contains outer_boxes environment`) in
  let source_regular,source_contains = CONJ_PAIR source_at in
  ASSUME_TAC source_regular THEN ASSUME_TAC source_contains THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                candle_analytic_regular_at_def] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC
        (SPECL
          [`source_value:((num#num)#num)#((num#num)#num)`;
           `root_interval:((num#num)#num)#((num#num)#num)`;
           `derivative_interval:((num#num)#num)#((num#num)#num)`;
           `candle_analytic_value environment source_e`]
          candle_q_packed_object_sqrt_certificates_value_positive) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC source_contains THEN
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_q_dim_jet_contains_components_def;
                  candle_q_packed_object_box_jet_def;
                  candle_q_dim_jet_f_def;
                  candle_q_dim_jet_make_def; FST; SND] THEN
      MESON_TAC[]];
    MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `source_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `source_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `source_e:candle_analytic_expr`;
         `root_interval:((num#num)#num)#((num#num)#num)`;
         `derivative_interval:((num#num)#num)#((num#num)#num)`;
         `second_reciprocal:((num#num)#num)#((num#num)#num)`;
         `environment:real list`]
        candle_q_packed_object_box_sqrt_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_item_sqrt_raw_analytic_invariant = prove
 (`!center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
       center_root center_derivative box_root box_derivative
       box_second_reciprocal.
     LENGTH packed_hessian = 21 /\
     candle_q_interval_sqrt_certificate center_value center_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add center_root center_root)
       center_derivative /\
     candle_q_interval_sqrt_certificate value_bound box_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add box_root box_root) box_derivative /\
     candle_q_interval_inv_certificate
       (candle_q_interval_mul
         (candle_q_interval_add box_root box_root)
         (candle_q_interval_add value_bound value_bound))
       box_second_reciprocal /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_root
       (candle_q_packed_object_interval_list_scale
         center_derivative center_gradient)
       box_root
       (candle_q_packed_object_interval_list_scale
         box_derivative gradient_bounds)
       (candle_q_packed_object_unary_hessian6 box_derivative
         (candle_q_interval_neg box_second_reciprocal)
         gradient_bounds packed_hessian)
       (candle_packed_analytic_sqrt_with_interval center_root center_e)
       (candle_packed_analytic_sqrt_with_interval box_root box_e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "hessian_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "center_root_certificate")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_derivative_certificate")
          (CONJUNCTS_THEN2 (LABEL_TAC "box_root_certificate")
            (CONJUNCTS_THEN2 (LABEL_TAC "box_derivative_certificate")
              (CONJUNCTS_THEN2 (LABEL_TAC "box_second_certificate")
                (LABEL_TAC "input_invariant"))))))) THEN
  USE_THEN "input_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "erasure")
        (LABEL_TAC "domain_all"))) THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                candle_analytic_valid_dim_def] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                candle_analytic_erase_sqrt_certificates_def] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  USE_THEN "domain_all"
    (fun theorem -> MP_TAC (MATCH_MP theorem (ASSUME `domain:bool`))) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "box_shape")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_all")
          (LABEL_TAC "box_all")))) THEN
  SUBGOAL_THEN
   `LENGTH
      (gradient_bounds:
        (((num#num)#num)#((num#num)#num))list) = 6`
  (LABEL_TAC "box_gradient_length") THENL
   [USE_THEN "box_shape" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def;
                candle_q_packed_object_box_jet_def;
                candle_q_dim_jet_gradient_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_packed_object_interval_list_scale_length];
    MATCH_MP_TAC candle_q_packed_object_box_sqrt_shape THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`center_boxes:
            (((num#num)#num)#((num#num)#num))list`;
         `center_value:((num#num)#num)#((num#num)#num)`;
         `center_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `center_e:candle_analytic_expr`;
         `center_root:((num#num)#num)#((num#num)#num)`;
         `center_derivative:((num#num)#num)#((num#num)#num)`]
        candle_q_packed_object_center_all_sqrt_contains) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`outer_boxes:
            (((num#num)#num)#((num#num)#num))list`;
         `value_bound:((num#num)#num)#((num#num)#num)`;
         `gradient_bounds:
            (((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `box_e:candle_analytic_expr`;
         `box_root:((num#num)#num)#((num#num)#num)`;
         `box_derivative:((num#num)#num)#((num#num)#num)`;
         `box_second_reciprocal:((num#num)#num)#((num#num)#num)`]
        candle_q_packed_object_box_all_sqrt_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_item_sqrt_analytic_invariant = prove
 (`!center_boxes outer_boxes radii domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
       center_root center_derivative box_root box_derivative
       box_second_reciprocal.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     LENGTH packed_hessian = 21 /\
     candle_q_interval_sqrt_certificate center_value center_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add center_root center_root)
       center_derivative /\
     candle_q_interval_sqrt_certificate value_bound box_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add box_root box_root) box_derivative /\
     candle_q_interval_inv_certificate
       (candle_q_interval_mul
         (candle_q_interval_add box_root box_root)
         (candle_q_interval_add value_bound value_bound))
       box_second_reciprocal /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_root
       (candle_q_packed_object_interval_list_scale
         center_derivative center_gradient)
       (candle_q_packed_object_value_bound6 radii center_root
         (candle_q_packed_object_interval_list_scale
           center_derivative center_gradient)
         (candle_q_packed_object_unary_hessian6 box_derivative
           (candle_q_interval_neg box_second_reciprocal)
           gradient_bounds packed_hessian))
       (candle_q_packed_object_gradient_complete6 radii
         (candle_q_packed_object_interval_list_scale
           center_derivative center_gradient)
         (candle_q_packed_object_unary_hessian6 box_derivative
           (candle_q_interval_neg box_second_reciprocal)
           gradient_bounds packed_hessian))
       (candle_q_packed_object_unary_hessian6 box_derivative
         (candle_q_interval_neg box_second_reciprocal)
         gradient_bounds packed_hessian)
       (candle_packed_analytic_sqrt_with_interval center_root center_e)
       (candle_packed_analytic_sqrt_with_interval box_root box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (SPECL
      [`center_boxes:
          (((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:
          (((num#num)#num)#((num#num)#num))list`;
       `radii:((num#num)#num)list`; `domain:bool`;
       `center_root:((num#num)#num)#((num#num)#num)`;
       `candle_q_packed_object_interval_list_scale
          center_derivative center_gradient`;
       `box_root:((num#num)#num)#((num#num)#num)`;
       `candle_q_packed_object_interval_list_scale
          box_derivative gradient_bounds`;
       `candle_q_packed_object_unary_hessian6 box_derivative
          (candle_q_interval_neg box_second_reciprocal)
          gradient_bounds packed_hessian`;
       `candle_packed_analytic_sqrt_with_interval center_root center_e`;
       `candle_packed_analytic_sqrt_with_interval box_root box_e`]
      candle_q_packed_object_item_recomplete_analytic_invariant) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC
    (SPECL
      [`center_boxes:
          (((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:
          (((num#num)#num)#((num#num)#num))list`;
       `domain:bool`;
       `center_value:((num#num)#num)#((num#num)#num)`;
       `center_gradient:
          (((num#num)#num)#((num#num)#num))list`;
       `value_bound:((num#num)#num)#((num#num)#num)`;
       `gradient_bounds:
          (((num#num)#num)#((num#num)#num))list`;
       `packed_hessian:
          (((num#num)#num)#((num#num)#num))list`;
       `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
       `center_root:((num#num)#num)#((num#num)#num)`;
       `center_derivative:((num#num)#num)#((num#num)#num)`;
       `box_root:((num#num)#num)#((num#num)#num)`;
       `box_derivative:((num#num)#num)#((num#num)#num)`;
       `box_second_reciprocal:((num#num)#num)#((num#num)#num)`]
      candle_q_packed_object_item_sqrt_raw_analytic_invariant) THEN
  ASM_REWRITE_TAC[]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_sqrt_derivative_sound;
     candle_q_packed_object_sqrt_second_reciprocal_sound;
     candle_q_packed_object_sqrt_second_sound;
     candle_q_packed_object_sqrt_certificates_value_positive;
     candle_q_packed_object_center_first_sqrt_contains;
     candle_q_packed_object_sqrt_hessian6_contains;
     candle_q_packed_object_box_sqrt_contains;
     candle_q_packed_object_box_sqrt_shape;
     candle_q_packed_object_center_all_sqrt_contains;
     candle_q_packed_object_box_all_sqrt_contains;
     candle_q_packed_object_item_sqrt_raw_analytic_invariant;
     candle_q_packed_object_item_sqrt_analytic_invariant] then
  failwith "packed source object sqrt sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_SQRT_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
