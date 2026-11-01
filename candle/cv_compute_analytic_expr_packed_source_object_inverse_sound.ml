(* ========================================================================== *)
(* Exact object-q reciprocal operation.                                      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file connects the reciprocal             *)
(* certificates produced by the verified word evaluator to the exact         *)
(* object-q unary constructor.  The raw value, gradient and packed Hessian    *)
(* are proved analytic first; the common faithful recompletion theorem then  *)
(* gives the precise production object state.                                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_unary_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certificate_core.ml";;

module Candle_cv_analytic_expr_packed_source_object_inverse_sound = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_domain;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_core;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_recomplete_sound;;
open Candle_cv_analytic_expr_packed_source_object_mul_sound;;
open Candle_cv_analytic_expr_packed_source_object_unary_sound;;

let candle_q_packed_object_inverse_derivative_def = new_definition
 `candle_q_packed_object_inverse_derivative reciprocal =
    candle_q_interval_neg
      (candle_q_interval_mul reciprocal reciprocal)`;;

let candle_q_packed_object_inverse_second_def = new_definition
 `candle_q_packed_object_inverse_second reciprocal =
    candle_q_interval_add
      (candle_q_interval_mul
        (candle_q_interval_mul reciprocal reciprocal) reciprocal)
      (candle_q_interval_mul
        (candle_q_interval_mul reciprocal reciprocal) reciprocal)`;;

let candle_q_packed_object_inverse_derivative_sound = prove
 (`!input reciprocal x.
     candle_q_interval_inv_certificate input reciprocal /\
     candle_q_interval_contains input x
     ==>
     candle_q_interval_contains
       (candle_q_packed_object_inverse_derivative reciprocal)
       (--(inv x * inv x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_interval_contains reciprocal (inv x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`input:((num#num)#num)#((num#num)#num)`;
         `reciprocal:((num#num)#num)#((num#num)#num)`; `x:real`]
        candle_q_interval_inv_certificate_sound) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_q_packed_object_inverse_derivative_def] THEN
    MATCH_MP_TAC candle_q_interval_neg_sound THEN
    MATCH_MP_TAC candle_q_interval_mul_sound THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_inverse_second_sound = prove
 (`!input reciprocal x.
     candle_q_interval_inv_certificate input reciprocal /\
     candle_q_interval_contains input x
     ==>
     candle_q_interval_contains
       (candle_q_packed_object_inverse_second reciprocal)
       (((inv x * inv x) * inv x) +
        ((inv x * inv x) * inv x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_interval_contains reciprocal (inv x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`input:((num#num)#num)#((num#num)#num)`;
         `reciprocal:((num#num)#num)#((num#num)#num)`; `x:real`]
        candle_q_interval_inv_certificate_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_interval_mul reciprocal reciprocal)
      (inv x * inv x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_interval_mul_sound THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_interval_mul
        (candle_q_interval_mul reciprocal reciprocal) reciprocal)
      ((inv x * inv x) * inv x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_interval_mul_sound THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_q_packed_object_inverse_second_def] THEN
    MATCH_MP_TAC candle_q_interval_add_sound THEN ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_center_first_inverse_contains = prove
 (`!source_value source_gradient source_e reciprocal environment.
     LENGTH source_gradient = 6 /\
     candle_q_interval_inv_certificate source_value reciprocal /\
     candle_q_packed_object_center_first_contains
       source_value source_gradient environment source_e
     ==>
     candle_q_packed_object_center_first_contains
       reciprocal
       (candle_q_packed_object_interval_list_scale
         (candle_q_packed_object_inverse_derivative reciprocal)
         source_gradient)
       environment (Candle_analytic_inv source_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_object_center_first_contains_def]) THEN
  REWRITE_TAC[candle_q_packed_object_center_first_contains_def;
              candle_analytic_value_def; candle_analytic_d_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `reciprocal:((num#num)#num)#((num#num)#num)`;
         `candle_analytic_value environment source_e`]
        candle_q_interval_inv_certificate_sound) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_interval_list_scale_lookup] THEN
    MATCH_MP_TAC candle_q_interval_mul_sound THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`source_value:((num#num)#num)#((num#num)#num)`;
           `reciprocal:((num#num)#num)#((num#num)#num)`;
           `candle_analytic_value environment source_e`]
          candle_q_packed_object_inverse_derivative_sound) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

let candle_q_packed_object_inverse_hessian6_contains = prove
 (`!source_value source_gradient source_hessian source_e reciprocal
       environment.
     LENGTH source_gradient = 6 /\ LENGTH source_hessian = 21 /\
     candle_q_interval_inv_certificate source_value reciprocal /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         source_value source_gradient source_hessian)
       environment source_e
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_unary_hessian6
         (candle_q_packed_object_inverse_derivative reciprocal)
         (candle_q_packed_object_inverse_second reciprocal)
         source_gradient source_hessian)
       (candle_q_packed_hessian6_values
         (\i j. candle_analytic_dd i j environment
           (Candle_analytic_inv source_e)))`,
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
   `candle_q_stack_contains source_gradient
      (list_of_seq (\i. candle_analytic_d i environment source_e) 6)`
  (LABEL_TAC "gradient_stack") THENL
   [SUBGOAL_THEN
     `source_gradient =
      list_of_seq (\i. candle_q_interval_lookup i source_gradient) 6`
    SUBST1_TAC THENL
     [MATCH_MP_TAC candle_q_interval_list_eq_list_of_seq_lookup THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_stack_contains_all2;
                  candle_all2_list_of_seq] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[EL_LIST_OF_SEQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_stack_contains source_hessian
      (candle_q_packed_hessian6_values
        (\i j. candle_analytic_dd i j environment source_e))`
  (LABEL_TAC "hessian_stack") THENL
   [SUBGOAL_THEN
     `source_hessian =
      list_of_seq (\i. candle_q_interval_lookup i source_hessian) 21`
    SUBST1_TAC THENL
     [MATCH_MP_TAC candle_q_interval_list_eq_list_of_seq_lookup THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_stack_contains_all2] THEN
      ONCE_REWRITE_TAC[candle_q_packed_hessian6_values_coordinates] THEN
      REWRITE_TAC[candle_all2_list_of_seq] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
      MATCH_MP_TAC
        (SPECL
          [`source_value:((num#num)#num)#((num#num)#num)`;
           `source_gradient:
              (((num#num)#num)#((num#num)#num))list`;
           `source_hessian:
              (((num#num)#num)#((num#num)#num))list`;
           `environment:real list`; `source_e:candle_analytic_expr`; `i:num`]
          candle_q_packed_object_analytic_hessian_lookup_contains) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_packed_object_inverse_derivative reciprocal)
      (--(inv (candle_analytic_value environment source_e) *
            inv (candle_analytic_value environment source_e)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `reciprocal:((num#num)#num)#((num#num)#num)`;
         `candle_analytic_value environment source_e`]
        candle_q_packed_object_inverse_derivative_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_packed_object_inverse_second reciprocal)
      (((inv (candle_analytic_value environment source_e) *
         inv (candle_analytic_value environment source_e)) *
         inv (candle_analytic_value environment source_e)) +
       ((inv (candle_analytic_value environment source_e) *
         inv (candle_analytic_value environment source_e)) *
         inv (candle_analytic_value environment source_e)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `reciprocal:((num#num)#num)#((num#num)#num)`;
         `candle_analytic_value environment source_e`]
        candle_q_packed_object_inverse_second_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (SPECL
      [`candle_q_packed_object_inverse_derivative reciprocal`;
       `candle_q_packed_object_inverse_second reciprocal`;
       `source_gradient:
          (((num#num)#num)#((num#num)#num))list`;
       `source_hessian:
          (((num#num)#num)#((num#num)#num))list`;
       `--(inv (candle_analytic_value environment source_e) *
             inv (candle_analytic_value environment source_e))`;
       `((inv (candle_analytic_value environment source_e) *
          inv (candle_analytic_value environment source_e)) *
          inv (candle_analytic_value environment source_e)) +
        ((inv (candle_analytic_value environment source_e) *
          inv (candle_analytic_value environment source_e)) *
          inv (candle_analytic_value environment source_e))`;
       `(\i. candle_analytic_d i environment source_e):num->real`;
       `(\i j. candle_analytic_dd i j environment source_e):
          num->num->real`]
      candle_q_packed_object_unary_hessian6_sound) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN (LABEL_TAC "unary_hessian") THEN
    SUBGOAL_THEN
     `(\i j.
         (((inv (candle_analytic_value environment source_e) *
            inv (candle_analytic_value environment source_e)) *
            inv (candle_analytic_value environment source_e)) +
          ((inv (candle_analytic_value environment source_e) *
            inv (candle_analytic_value environment source_e)) *
            inv (candle_analytic_value environment source_e))) *
           (candle_analytic_d i environment source_e *
            candle_analytic_d j environment source_e) +
         (--(inv (candle_analytic_value environment source_e) *
              inv (candle_analytic_value environment source_e))) *
           candle_analytic_dd i j environment source_e) =
      (\i j. candle_analytic_dd i j environment
        (Candle_analytic_inv source_e))`
    (LABEL_TAC "inverse_hessian_formula") THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
      REWRITE_TAC[candle_analytic_dd_def] THEN CONV_TAC REAL_RING;
      USE_THEN "unary_hessian" MP_TAC THEN BETA_TAC THEN
      ASM_REWRITE_TAC[]]]);;

let candle_q_packed_object_box_inverse_contains = prove
 (`!source_value source_gradient source_hessian source_e reciprocal
       environment.
     LENGTH source_gradient = 6 /\ LENGTH source_hessian = 21 /\
     candle_q_interval_inv_certificate source_value reciprocal /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         source_value source_gradient source_hessian)
       environment source_e
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet reciprocal
         (candle_q_packed_object_interval_list_scale
           (candle_q_packed_object_inverse_derivative reciprocal)
           source_gradient)
         (candle_q_packed_object_unary_hessian6
           (candle_q_packed_object_inverse_derivative reciprocal)
           (candle_q_packed_object_inverse_second reciprocal)
           source_gradient source_hessian))
       environment (Candle_analytic_inv source_e)`,
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
      (candle_q_packed_object_unary_hessian6
        (candle_q_packed_object_inverse_derivative reciprocal)
        (candle_q_packed_object_inverse_second reciprocal)
        source_gradient source_hessian)
      (candle_q_packed_hessian6_values
        (\i j. candle_analytic_dd i j environment
          (Candle_analytic_inv source_e)))`
  (LABEL_TAC "output_hessian") THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `source_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `source_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `source_e:candle_analytic_expr`;
         `reciprocal:((num#num)#num)#((num#num)#num)`;
         `environment:real list`]
        candle_q_packed_object_inverse_hessian6_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_packed_object_box_jet_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def;
              candle_analytic_value_def;
              candle_analytic_d_def; FST; SND] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `reciprocal:((num#num)#num)#((num#num)#num)`;
         `candle_analytic_value environment source_e`]
        candle_q_interval_inv_certificate_sound) THEN
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
           `reciprocal:((num#num)#num)#((num#num)#num)`;
           `candle_analytic_value environment source_e`]
          candle_q_packed_object_inverse_derivative_sound) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC candle_q_packed_object_analytic_hessian_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_box_inverse_shape = prove
 (`!source_gradient source_hessian reciprocal.
     LENGTH source_gradient = 6
     ==>
     candle_q_dim_jet_shape 6
       (candle_q_packed_object_box_jet reciprocal
         (candle_q_packed_object_interval_list_scale
           (candle_q_packed_object_inverse_derivative reciprocal)
           source_gradient)
         (candle_q_packed_object_unary_hessian6
           (candle_q_packed_object_inverse_derivative reciprocal)
           (candle_q_packed_object_inverse_second reciprocal)
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

let candle_q_packed_object_center_all_inverse_contains = prove
 (`!center_boxes source_value source_gradient source_e reciprocal.
     LENGTH source_gradient = 6 /\
     candle_q_interval_inv_certificate source_value reciprocal /\
     (!environment.
        candle_q_stack_contains center_boxes environment
        ==> candle_analytic_regular_at environment source_e /\
            candle_q_packed_object_center_first_contains
              source_value source_gradient environment source_e)
     ==>
     (!environment.
        candle_q_stack_contains center_boxes environment
        ==> candle_analytic_regular_at environment
              (Candle_analytic_inv source_e) /\
            candle_q_packed_object_center_first_contains reciprocal
              (candle_q_packed_object_interval_list_scale
                (candle_q_packed_object_inverse_derivative reciprocal)
                source_gradient)
              environment (Candle_analytic_inv source_e))`,
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
   [REWRITE_TAC[candle_analytic_regular_at_def] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_interval_not_zero_contains_nonzero THEN
      EXISTS_TAC `source_value:((num#num)#num)#((num#num)#num)` THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[candle_q_interval_inv_certificate_def];
        MP_TAC source_contains THEN
        REWRITE_TAC[candle_q_packed_object_center_first_contains_def] THEN
        MESON_TAC[]]];
    MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `source_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `source_e:candle_analytic_expr`;
         `reciprocal:((num#num)#num)#((num#num)#num)`;
         `environment:real list`]
        candle_q_packed_object_center_first_inverse_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_box_all_inverse_contains = prove
 (`!outer_boxes source_value source_gradient source_hessian source_e
       reciprocal.
     LENGTH source_gradient = 6 /\ LENGTH source_hessian = 21 /\
     candle_q_interval_inv_certificate source_value reciprocal /\
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
              (Candle_analytic_inv source_e) /\
            candle_q_dim_analytic_contains 6
              (candle_q_packed_object_box_jet reciprocal
                (candle_q_packed_object_interval_list_scale
                  (candle_q_packed_object_inverse_derivative reciprocal)
                  source_gradient)
                (candle_q_packed_object_unary_hessian6
                  (candle_q_packed_object_inverse_derivative reciprocal)
                  (candle_q_packed_object_inverse_second reciprocal)
                  source_gradient source_hessian))
              environment (Candle_analytic_inv source_e))`,
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
   [REWRITE_TAC[candle_analytic_regular_at_def] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_interval_not_zero_contains_nonzero THEN
      EXISTS_TAC `source_value:((num#num)#num)#((num#num)#num)` THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[candle_q_interval_inv_certificate_def];
        MP_TAC source_contains THEN
        REWRITE_TAC[candle_q_dim_analytic_contains_def;
                    candle_q_dim_jet_contains_components_def;
                    candle_q_packed_object_box_jet_def;
                    candle_q_dim_jet_f_def;
                    candle_q_dim_jet_make_def; FST; SND] THEN
        MESON_TAC[]]];
    MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `source_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `source_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `source_e:candle_analytic_expr`;
         `reciprocal:((num#num)#num)#((num#num)#num)`;
         `environment:real list`]
        candle_q_packed_object_box_inverse_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_item_inverse_raw_analytic_invariant = prove
 (`!center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
       center_reciprocal box_reciprocal.
     LENGTH packed_hessian = 21 /\
     candle_q_interval_inv_certificate center_value center_reciprocal /\
     candle_q_interval_inv_certificate value_bound box_reciprocal /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_reciprocal
       (candle_q_packed_object_interval_list_scale
         (candle_q_packed_object_inverse_derivative center_reciprocal)
         center_gradient)
       box_reciprocal
       (candle_q_packed_object_interval_list_scale
         (candle_q_packed_object_inverse_derivative box_reciprocal)
         gradient_bounds)
       (candle_q_packed_object_unary_hessian6
         (candle_q_packed_object_inverse_derivative box_reciprocal)
         (candle_q_packed_object_inverse_second box_reciprocal)
         gradient_bounds packed_hessian)
       (Candle_analytic_inv center_e) (Candle_analytic_inv box_e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "hessian_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "center_certificate")
        (CONJUNCTS_THEN2 (LABEL_TAC "box_certificate")
          (LABEL_TAC "input_invariant")))) THEN
  USE_THEN "input_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "erasure")
        (LABEL_TAC "domain_all"))) THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def;
              candle_analytic_valid_dim_def;
              candle_analytic_erase_sqrt_certificates_def] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  USE_THEN "domain_all"
    (fun th -> MP_TAC (MATCH_MP th (ASSUME `domain:bool`))) THEN
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
    MATCH_MP_TAC candle_q_packed_object_box_inverse_shape THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`center_boxes:
            (((num#num)#num)#((num#num)#num))list`;
         `center_value:((num#num)#num)#((num#num)#num)`;
         `center_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `center_e:candle_analytic_expr`;
         `center_reciprocal:((num#num)#num)#((num#num)#num)`]
        candle_q_packed_object_center_all_inverse_contains) THEN
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
         `box_reciprocal:((num#num)#num)#((num#num)#num)`]
        candle_q_packed_object_box_all_inverse_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_item_inverse_analytic_invariant = prove
 (`!center_boxes outer_boxes radii domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
       center_reciprocal box_reciprocal.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     LENGTH packed_hessian = 21 /\
     candle_q_interval_inv_certificate center_value center_reciprocal /\
     candle_q_interval_inv_certificate value_bound box_reciprocal /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_reciprocal
       (candle_q_packed_object_interval_list_scale
         (candle_q_packed_object_inverse_derivative center_reciprocal)
         center_gradient)
       (candle_q_packed_object_value_bound6 radii center_reciprocal
         (candle_q_packed_object_interval_list_scale
           (candle_q_packed_object_inverse_derivative center_reciprocal)
           center_gradient)
         (candle_q_packed_object_unary_hessian6
           (candle_q_packed_object_inverse_derivative box_reciprocal)
           (candle_q_packed_object_inverse_second box_reciprocal)
           gradient_bounds packed_hessian))
       (candle_q_packed_object_gradient_complete6 radii
         (candle_q_packed_object_interval_list_scale
           (candle_q_packed_object_inverse_derivative center_reciprocal)
           center_gradient)
         (candle_q_packed_object_unary_hessian6
           (candle_q_packed_object_inverse_derivative box_reciprocal)
           (candle_q_packed_object_inverse_second box_reciprocal)
           gradient_bounds packed_hessian))
       (candle_q_packed_object_unary_hessian6
         (candle_q_packed_object_inverse_derivative box_reciprocal)
         (candle_q_packed_object_inverse_second box_reciprocal)
         gradient_bounds packed_hessian)
       (Candle_analytic_inv center_e) (Candle_analytic_inv box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (SPECL
      [`center_boxes:
          (((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:
          (((num#num)#num)#((num#num)#num))list`;
       `radii:((num#num)#num)list`; `domain:bool`;
       `center_reciprocal:((num#num)#num)#((num#num)#num)`;
       `candle_q_packed_object_interval_list_scale
          (candle_q_packed_object_inverse_derivative center_reciprocal)
          center_gradient`;
       `box_reciprocal:((num#num)#num)#((num#num)#num)`;
       `candle_q_packed_object_interval_list_scale
          (candle_q_packed_object_inverse_derivative box_reciprocal)
          gradient_bounds`;
       `candle_q_packed_object_unary_hessian6
          (candle_q_packed_object_inverse_derivative box_reciprocal)
          (candle_q_packed_object_inverse_second box_reciprocal)
          gradient_bounds packed_hessian`;
       `Candle_analytic_inv center_e`; `Candle_analytic_inv box_e`]
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
       `center_reciprocal:((num#num)#num)#((num#num)#num)`;
       `box_reciprocal:((num#num)#num)#((num#num)#num)`]
      candle_q_packed_object_item_inverse_raw_analytic_invariant) THEN
  ASM_REWRITE_TAC[]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_inverse_derivative_sound;
     candle_q_packed_object_inverse_second_sound;
     candle_q_packed_object_center_first_inverse_contains;
     candle_q_packed_object_inverse_hessian6_contains;
     candle_q_packed_object_box_inverse_contains;
     candle_q_packed_object_box_inverse_shape;
     candle_q_packed_object_center_all_inverse_contains;
     candle_q_packed_object_box_all_inverse_contains;
     candle_q_packed_object_item_inverse_raw_analytic_invariant;
     candle_q_packed_object_item_inverse_analytic_invariant] then
  failwith "packed source object inverse sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_INVERSE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
