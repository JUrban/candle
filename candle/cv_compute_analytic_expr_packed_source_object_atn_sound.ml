(* ========================================================================== *)
(* Exact object-q certified arctangent operation.                            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file connects the exact range, square   *)
(* and reciprocal certificates produced by the verified word evaluator to   *)
(* the production packed object-q unary constructor.                         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_sqrt_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certified_atn_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_atn_sound = struct

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
open Candle_cv_analytic_expr_packed_source_certified_atn_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_recomplete_sound;;
open Candle_cv_analytic_expr_packed_source_object_mul_sound;;
open Candle_cv_analytic_expr_packed_source_object_unary_sound;;

(* These two definitions are the ordinary exact-rational images of          *)
(* [bounded_object_q_atan_denominator_cv] and                                *)
(* [bounded_object_q_atan_second_cv].  In particular, no normalized          *)
(* surrogate is substituted for the production object-q operation.          *)

let candle_q_packed_object_atn_denominator_def = new_definition
 `candle_q_packed_object_atn_denominator square =
    candle_q_interval_add candle_q_atn_one_interval square`;;

let candle_q_packed_object_atn_second_def = new_definition
 `candle_q_packed_object_atn_second source derivative_square =
    candle_q_interval_neg
      (candle_q_interval_mul
        (candle_q_interval_add source source) derivative_square)`;;

let candle_q_packed_object_atn_denominator_sound = prove
 (`!source_input word_input square x.
     candle_q_interval_square_outer_certificate
       source_input word_input square /\
     candle_q_interval_contains source_input x
     ==>
     candle_q_interval_contains
       (candle_q_packed_object_atn_denominator square)
       (&1 + x * x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_atn_denominator_def] THEN
  MATCH_MP_TAC candle_q_interval_add_sound THEN
  CONJ_TAC THENL
   [ACCEPT_TAC candle_q_atn_one_interval_sound;
    MATCH_MP_TAC
      (SPECL
        [`source_input:((num#num)#num)#((num#num)#num)`;
         `word_input:((num#num)#num)#((num#num)#num)`;
         `square:((num#num)#num)#((num#num)#num)`; `x:real`]
        candle_q_interval_square_outer_certificate_sound) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_atn_derivative_sound = prove
 (`!source_input word_input square derivative_interval x.
     candle_q_interval_square_outer_certificate
       source_input word_input square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator square)
       derivative_interval /\
     candle_q_interval_contains source_input x
     ==>
     candle_q_interval_contains derivative_interval
       (inv (&1 + x * x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (SPECL
      [`candle_q_packed_object_atn_denominator square`;
       `derivative_interval:((num#num)#num)#((num#num)#num)`;
       `&1 + x * x`]
      candle_q_interval_inv_certificate_sound) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC
    (SPECL
      [`source_input:((num#num)#num)#((num#num)#num)`;
       `word_input:((num#num)#num)#((num#num)#num)`;
       `square:((num#num)#num)#((num#num)#num)`; `x:real`]
      candle_q_packed_object_atn_denominator_sound) THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_atn_second_sound = prove
 (`!source_input word_input square derivative_interval
       derivative_square x.
     candle_q_interval_square_outer_certificate
       source_input word_input square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator square)
       derivative_interval /\
     candle_q_interval_square_outer_certificate
       derivative_interval derivative_interval derivative_square /\
     candle_q_interval_contains source_input x
     ==>
     candle_q_interval_contains
       (candle_q_packed_object_atn_second source_input derivative_square)
       (--((x + x) *
            (inv (&1 + x * x) * inv (&1 + x * x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_interval_contains derivative_interval
      (inv (&1 + x * x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_input:((num#num)#num)#((num#num)#num)`;
         `word_input:((num#num)#num)#((num#num)#num)`;
         `square:((num#num)#num)#((num#num)#num)`;
         `derivative_interval:((num#num)#num)#((num#num)#num)`;
         `x:real`]
        candle_q_packed_object_atn_derivative_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains derivative_square
      (inv (&1 + x * x) * inv (&1 + x * x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`derivative_interval:((num#num)#num)#((num#num)#num)`;
         `derivative_interval:((num#num)#num)#((num#num)#num)`;
         `derivative_square:((num#num)#num)#((num#num)#num)`;
         `inv (&1 + x * x)`]
        candle_q_interval_square_outer_certificate_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_packed_object_atn_second_def] THEN
  MATCH_MP_TAC candle_q_interval_neg_sound THEN
  MATCH_MP_TAC candle_q_interval_mul_sound THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_q_interval_add_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_center_first_atn_contains = prove
 (`!source_value source_gradient source_e center_input center_result
       center_square center_derivative environment.
     LENGTH source_gradient = 6 /\
     candle_q_interval_atn_outer_certificate
       source_value center_input center_result /\
     candle_q_interval_square_outer_certificate
       source_value center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator center_square)
       center_derivative /\
     candle_q_packed_object_center_first_contains
       source_value source_gradient environment source_e
     ==>
     candle_q_packed_object_center_first_contains center_result
       (candle_q_packed_object_interval_list_scale
         center_derivative source_gradient)
       environment (Candle_analytic_atn source_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_object_center_first_contains_def]) THEN
  REWRITE_TAC[candle_q_packed_object_center_first_contains_def;
              candle_analytic_value_def; candle_analytic_d_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `center_input:((num#num)#num)#((num#num)#num)`;
         `center_result:((num#num)#num)#((num#num)#num)`;
         `candle_analytic_value environment source_e`]
        candle_q_interval_atn_outer_certificate_sound) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_interval_list_scale_lookup] THEN
    MATCH_MP_TAC candle_q_interval_mul_sound THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`source_value:((num#num)#num)#((num#num)#num)`;
           `center_input:((num#num)#num)#((num#num)#num)`;
           `center_square:((num#num)#num)#((num#num)#num)`;
           `center_derivative:((num#num)#num)#((num#num)#num)`;
           `candle_analytic_value environment source_e`]
          candle_q_packed_object_atn_derivative_sound) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

let candle_q_packed_object_atn_hessian6_contains = prove
 (`!source_value source_gradient source_hessian source_e box_input
       box_square box_derivative box_derivative_square environment.
     LENGTH source_gradient = 6 /\ LENGTH source_hessian = 21 /\
     candle_q_interval_square_outer_certificate
       source_value box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         source_value source_gradient source_hessian)
       environment source_e
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_unary_hessian6 box_derivative
         (candle_q_packed_object_atn_second
           source_value box_derivative_square)
         source_gradient source_hessian)
       (candle_q_packed_hessian6_values
         (\i j. candle_analytic_dd i j environment
           (Candle_analytic_atn source_e)))`,
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
   `candle_q_interval_contains box_derivative
      (inv (&1 +
        candle_analytic_value environment source_e *
        candle_analytic_value environment source_e))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `box_input:((num#num)#num)#((num#num)#num)`;
         `box_square:((num#num)#num)#((num#num)#num)`;
         `box_derivative:((num#num)#num)#((num#num)#num)`;
         `candle_analytic_value environment source_e`]
        candle_q_packed_object_atn_derivative_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_packed_object_atn_second
        source_value box_derivative_square)
      (--((candle_analytic_value environment source_e +
           candle_analytic_value environment source_e) *
          (inv (&1 +
             candle_analytic_value environment source_e *
             candle_analytic_value environment source_e) *
           inv (&1 +
             candle_analytic_value environment source_e *
             candle_analytic_value environment source_e))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `box_input:((num#num)#num)#((num#num)#num)`;
         `box_square:((num#num)#num)#((num#num)#num)`;
         `box_derivative:((num#num)#num)#((num#num)#num)`;
         `box_derivative_square:((num#num)#num)#((num#num)#num)`;
         `candle_analytic_value environment source_e`]
        candle_q_packed_object_atn_second_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (SPECL
      [`box_derivative:((num#num)#num)#((num#num)#num)`;
       `candle_q_packed_object_atn_second
          source_value box_derivative_square`;
       `source_gradient:
          (((num#num)#num)#((num#num)#num))list`;
       `source_hessian:
          (((num#num)#num)#((num#num)#num))list`;
       `inv (&1 +
          candle_analytic_value environment source_e *
          candle_analytic_value environment source_e)`;
       `--((candle_analytic_value environment source_e +
            candle_analytic_value environment source_e) *
           (inv (&1 +
              candle_analytic_value environment source_e *
              candle_analytic_value environment source_e) *
            inv (&1 +
              candle_analytic_value environment source_e *
              candle_analytic_value environment source_e)))`;
       `(\i. candle_analytic_d i environment source_e):num->real`;
       `(\i j. candle_analytic_dd i j environment source_e):
          num->num->real`]
      candle_q_packed_object_unary_hessian6_sound) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN (LABEL_TAC "unary_hessian") THEN
    SUBGOAL_THEN
     `(\i j.
         (--((candle_analytic_value environment source_e +
              candle_analytic_value environment source_e) *
             (inv (&1 +
                candle_analytic_value environment source_e *
                candle_analytic_value environment source_e) *
              inv (&1 +
                candle_analytic_value environment source_e *
                candle_analytic_value environment source_e)))) *
           (candle_analytic_d i environment source_e *
            candle_analytic_d j environment source_e) +
         inv (&1 +
           candle_analytic_value environment source_e *
           candle_analytic_value environment source_e) *
           candle_analytic_dd i j environment source_e) =
      (\i j. candle_analytic_dd i j environment
        (Candle_analytic_atn source_e))`
    (LABEL_TAC "atn_hessian_formula") THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
      REWRITE_TAC[candle_analytic_dd_def] THEN CONV_TAC REAL_RING;
      USE_THEN "unary_hessian" MP_TAC THEN BETA_TAC THEN
      ASM_REWRITE_TAC[]]]);;

let candle_q_packed_object_box_atn_contains = prove
 (`!source_value source_gradient source_hessian source_e box_input
       box_square box_derivative box_derivative_square environment.
     LENGTH source_gradient = 6 /\ LENGTH source_hessian = 21 /\
     candle_q_interval_square_outer_certificate
       source_value box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         source_value source_gradient source_hessian)
       environment source_e
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet candle_q_atn_universal_interval
         (candle_q_packed_object_interval_list_scale
           box_derivative source_gradient)
         (candle_q_packed_object_unary_hessian6 box_derivative
           (candle_q_packed_object_atn_second
             source_value box_derivative_square)
           source_gradient source_hessian))
       environment (Candle_analytic_atn source_e)`,
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
      (candle_q_packed_object_unary_hessian6 box_derivative
        (candle_q_packed_object_atn_second
          source_value box_derivative_square)
        source_gradient source_hessian)
      (candle_q_packed_hessian6_values
        (\i j. candle_analytic_dd i j environment
          (Candle_analytic_atn source_e)))`
  (LABEL_TAC "output_hessian") THENL
   [MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `source_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `source_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `source_e:candle_analytic_expr`;
         `box_input:((num#num)#num)#((num#num)#num)`;
         `box_square:((num#num)#num)#((num#num)#num)`;
         `box_derivative:((num#num)#num)#((num#num)#num)`;
         `box_derivative_square:((num#num)#num)#((num#num)#num)`;
         `environment:real list`]
        candle_q_packed_object_atn_hessian6_contains) THEN
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
   [MATCH_ACCEPT_TAC
      (SPEC `candle_analytic_value environment source_e`
        candle_q_atn_universal_interval_sound);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_interval_list_scale_lookup] THEN
    MATCH_MP_TAC candle_q_interval_mul_sound THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`source_value:((num#num)#num)#((num#num)#num)`;
           `box_input:((num#num)#num)#((num#num)#num)`;
           `box_square:((num#num)#num)#((num#num)#num)`;
           `box_derivative:((num#num)#num)#((num#num)#num)`;
           `candle_analytic_value environment source_e`]
          candle_q_packed_object_atn_derivative_sound) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC candle_q_packed_object_analytic_hessian_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_box_atn_shape = prove
 (`!source_gradient source_hessian box_derivative source_value
       box_derivative_square.
     LENGTH source_gradient = 6
     ==>
     candle_q_dim_jet_shape 6
       (candle_q_packed_object_box_jet candle_q_atn_universal_interval
         (candle_q_packed_object_interval_list_scale
           box_derivative source_gradient)
         (candle_q_packed_object_unary_hessian6 box_derivative
           (candle_q_packed_object_atn_second
             source_value box_derivative_square)
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

let candle_q_packed_object_center_all_atn_contains = prove
 (`!center_boxes source_value source_gradient source_e center_input
       center_result center_square center_derivative.
     LENGTH source_gradient = 6 /\
     candle_q_interval_atn_outer_certificate
       source_value center_input center_result /\
     candle_q_interval_square_outer_certificate
       source_value center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator center_square)
       center_derivative /\
     (!environment.
        candle_q_stack_contains center_boxes environment
        ==> candle_analytic_regular_at environment source_e /\
            candle_q_packed_object_center_first_contains
              source_value source_gradient environment source_e)
     ==>
     (!environment.
        candle_q_stack_contains center_boxes environment
        ==> candle_analytic_regular_at environment
              (Candle_analytic_atn source_e) /\
            candle_q_packed_object_center_first_contains center_result
              (candle_q_packed_object_interval_list_scale
                center_derivative source_gradient)
              environment (Candle_analytic_atn source_e))`,
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
   [ASM_REWRITE_TAC[candle_analytic_regular_at_def];
    MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `source_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `source_e:candle_analytic_expr`;
         `center_input:((num#num)#num)#((num#num)#num)`;
         `center_result:((num#num)#num)#((num#num)#num)`;
         `center_square:((num#num)#num)#((num#num)#num)`;
         `center_derivative:((num#num)#num)#((num#num)#num)`;
         `environment:real list`]
        candle_q_packed_object_center_first_atn_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_box_all_atn_contains = prove
 (`!outer_boxes source_value source_gradient source_hessian source_e
       box_input box_square box_derivative box_derivative_square.
     LENGTH source_gradient = 6 /\ LENGTH source_hessian = 21 /\
     candle_q_interval_square_outer_certificate
       source_value box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square /\
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
              (Candle_analytic_atn source_e) /\
            candle_q_dim_analytic_contains 6
              (candle_q_packed_object_box_jet
                candle_q_atn_universal_interval
                (candle_q_packed_object_interval_list_scale
                  box_derivative source_gradient)
                (candle_q_packed_object_unary_hessian6 box_derivative
                  (candle_q_packed_object_atn_second
                    source_value box_derivative_square)
                  source_gradient source_hessian))
              environment (Candle_analytic_atn source_e))`,
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
   [ASM_REWRITE_TAC[candle_analytic_regular_at_def];
    MATCH_MP_TAC
      (SPECL
        [`source_value:((num#num)#num)#((num#num)#num)`;
         `source_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `source_hessian:
            (((num#num)#num)#((num#num)#num))list`;
         `source_e:candle_analytic_expr`;
         `box_input:((num#num)#num)#((num#num)#num)`;
         `box_square:((num#num)#num)#((num#num)#num)`;
         `box_derivative:((num#num)#num)#((num#num)#num)`;
         `box_derivative_square:((num#num)#num)#((num#num)#num)`;
         `environment:real list`]
        candle_q_packed_object_box_atn_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_item_atn_raw_analytic_invariant = prove
 (`!center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
       center_input center_result center_square center_derivative
       box_input box_square box_derivative box_derivative_square.
     LENGTH packed_hessian = 21 /\
     candle_q_interval_atn_outer_certificate
       center_value center_input center_result /\
     candle_q_interval_square_outer_certificate
       center_value center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator center_square)
       center_derivative /\
     candle_q_interval_square_outer_certificate
       value_bound box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_result
       (candle_q_packed_object_interval_list_scale
         center_derivative center_gradient)
       candle_q_atn_universal_interval
       (candle_q_packed_object_interval_list_scale
         box_derivative gradient_bounds)
       (candle_q_packed_object_unary_hessian6 box_derivative
         (candle_q_packed_object_atn_second
           value_bound box_derivative_square)
         gradient_bounds packed_hessian)
       (Candle_analytic_atn center_e) (Candle_analytic_atn box_e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "hessian_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "center_atn_certificate")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_square_certificate")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_derivative_certificate")
            (CONJUNCTS_THEN2 (LABEL_TAC "box_square_certificate")
              (CONJUNCTS_THEN2 (LABEL_TAC "box_derivative_certificate")
                (CONJUNCTS_THEN2
                  (LABEL_TAC "box_derivative_square_certificate")
                  (LABEL_TAC "input_invariant")))))))) THEN
  USE_THEN "input_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "erasure")
        (LABEL_TAC "domain_all"))) THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_analytic_valid_dim_def] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def] THEN
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
    MATCH_MP_TAC candle_q_packed_object_box_atn_shape THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`center_boxes:
            (((num#num)#num)#((num#num)#num))list`;
         `center_value:((num#num)#num)#((num#num)#num)`;
         `center_gradient:
            (((num#num)#num)#((num#num)#num))list`;
         `center_e:candle_analytic_expr`;
         `center_input:((num#num)#num)#((num#num)#num)`;
         `center_result:((num#num)#num)#((num#num)#num)`;
         `center_square:((num#num)#num)#((num#num)#num)`;
         `center_derivative:((num#num)#num)#((num#num)#num)`]
        candle_q_packed_object_center_all_atn_contains) THEN
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
         `box_input:((num#num)#num)#((num#num)#num)`;
         `box_square:((num#num)#num)#((num#num)#num)`;
         `box_derivative:((num#num)#num)#((num#num)#num)`;
         `box_derivative_square:((num#num)#num)#((num#num)#num)`]
        candle_q_packed_object_box_all_atn_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_item_atn_analytic_invariant = prove
 (`!center_boxes outer_boxes radii domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
       center_input center_result center_square center_derivative
       box_input box_square box_derivative box_derivative_square.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     LENGTH packed_hessian = 21 /\
     candle_q_interval_atn_outer_certificate
       center_value center_input center_result /\
     candle_q_interval_square_outer_certificate
       center_value center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator center_square)
       center_derivative /\
     candle_q_interval_square_outer_certificate
       value_bound box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_result
       (candle_q_packed_object_interval_list_scale
         center_derivative center_gradient)
       (candle_q_packed_object_value_bound6 radii center_result
         (candle_q_packed_object_interval_list_scale
           center_derivative center_gradient)
         (candle_q_packed_object_unary_hessian6 box_derivative
           (candle_q_packed_object_atn_second
             value_bound box_derivative_square)
           gradient_bounds packed_hessian))
       (candle_q_packed_object_gradient_complete6 radii
         (candle_q_packed_object_interval_list_scale
           center_derivative center_gradient)
         (candle_q_packed_object_unary_hessian6 box_derivative
           (candle_q_packed_object_atn_second
             value_bound box_derivative_square)
           gradient_bounds packed_hessian))
       (candle_q_packed_object_unary_hessian6 box_derivative
         (candle_q_packed_object_atn_second
           value_bound box_derivative_square)
         gradient_bounds packed_hessian)
       (Candle_analytic_atn center_e) (Candle_analytic_atn box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (SPECL
      [`center_boxes:
          (((num#num)#num)#((num#num)#num))list`;
       `outer_boxes:
          (((num#num)#num)#((num#num)#num))list`;
       `radii:((num#num)#num)list`; `domain:bool`;
       `center_result:((num#num)#num)#((num#num)#num)`;
       `candle_q_packed_object_interval_list_scale
          center_derivative center_gradient`;
       `candle_q_atn_universal_interval`;
       `candle_q_packed_object_interval_list_scale
          box_derivative gradient_bounds`;
       `candle_q_packed_object_unary_hessian6 box_derivative
          (candle_q_packed_object_atn_second
            value_bound box_derivative_square)
          gradient_bounds packed_hessian`;
       `Candle_analytic_atn center_e`; `Candle_analytic_atn box_e`]
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
       `center_input:((num#num)#num)#((num#num)#num)`;
       `center_result:((num#num)#num)#((num#num)#num)`;
       `center_square:((num#num)#num)#((num#num)#num)`;
       `center_derivative:((num#num)#num)#((num#num)#num)`;
       `box_input:((num#num)#num)#((num#num)#num)`;
       `box_square:((num#num)#num)#((num#num)#num)`;
       `box_derivative:((num#num)#num)#((num#num)#num)`;
       `box_derivative_square:((num#num)#num)#((num#num)#num)`]
      candle_q_packed_object_item_atn_raw_analytic_invariant) THEN
  ASM_REWRITE_TAC[]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_atn_denominator_sound;
     candle_q_packed_object_atn_derivative_sound;
     candle_q_packed_object_atn_second_sound;
     candle_q_packed_object_center_first_atn_contains;
     candle_q_packed_object_atn_hessian6_contains;
     candle_q_packed_object_box_atn_contains;
     candle_q_packed_object_box_atn_shape;
     candle_q_packed_object_center_all_atn_contains;
     candle_q_packed_object_box_all_atn_contains;
     candle_q_packed_object_item_atn_raw_analytic_invariant;
     candle_q_packed_object_item_atn_analytic_invariant] then
  failwith "packed source object atan sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_ATN_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
