(* ========================================================================== *)
(* Exact object-q invariant for the shared optimized delta calculation.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The four-coordinate delta instructions first *)
(* compute delta's center gradient and whole-box Hessian, then faithfully    *)
(* complete a whole-box gradient.  This file proves that shared intermediate *)
(* object once, independently of the subsequent product instruction.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_delta_neg_derivative_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_delta_base_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_packed_source_delta_value;;
open Candle_cv_analytic_expr_packed_source_delta_gradient;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_state_sound;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_jet_sound;;
open Candle_cv_analytic_expr_packed_source_delta_specialized_result_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_object_gradient_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_recomplete_sound;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;

let candle_q_packed_delta_jet_six_def = new_definition
 `candle_q_packed_delta_jet_six x0 x1 x2 x3 x4 x5 =
    candle_q_dim_jet_make
      (candle_q_packed_delta_value_six x0 x1 x2 x3 x4 x5)
      (candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5)
      (candle_q_packed_hessian6_expand
        (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5))`;;

let candle_q_packed_delta_jet_environment_def = new_definition
 `candle_q_packed_delta_jet_environment environment =
    candle_q_packed_delta_jet_six
      (candle_q_interval_lookup 0 environment)
      (candle_q_interval_lookup 1 environment)
      (candle_q_interval_lookup 2 environment)
      (candle_q_interval_lookup 3 environment)
      (candle_q_interval_lookup 4 environment)
      (candle_q_interval_lookup 5 environment)`;;

let candle_q_packed_delta_jet_six_shape = prove
 (`!x0 x1 x2 x3 x4 x5.
     candle_q_dim_jet_shape 6
       (candle_q_packed_delta_jet_six x0 x1 x2 x3 x4 x5)`,
  REPEAT GEN_TAC THEN
  let matrix_shape =
    ISPEC
      `candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5:
        ((((num#num)#num)#((num#num)#num))list)`
      candle_q_packed_hessian6_expand_shape in
  REWRITE_TAC[candle_q_packed_delta_jet_six_def;
              candle_q_dim_jet_shape_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_q_packed_delta_gradient_six_def;
              LET_DEF; LET_END_DEF; LENGTH;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_all] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCEPT_TAC matrix_shape);;

let candle_q_packed_delta_jet_six_analytic_contains = prove
 (`!x0 x1 x2 x3 x4 x5 v0 v1 v2 v3 v4 v5.
     candle_q_interval_contains x0 v0 /\
     candle_q_interval_contains x1 v1 /\
     candle_q_interval_contains x2 v2 /\
     candle_q_interval_contains x3 v3 /\
     candle_q_interval_contains x4 v4 /\
     candle_q_interval_contains x5 v5
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_delta_jet_six x0 x1 x2 x3 x4 x5)
       [v0;v1;v2;v3;v4;v5] candle_packed_delta_expr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let input_contains =
    end_itlist CONJ
      (map ASSUME
        [`candle_q_interval_contains x0 v0`;
         `candle_q_interval_contains x1 v1`;
         `candle_q_interval_contains x2 v2`;
         `candle_q_interval_contains x3 v3`;
         `candle_q_interval_contains x4 v4`;
         `candle_q_interval_contains x5 v5`]) in
  let value_contains =
    REWRITE_RULE[GSYM candle_packed_delta_value_analytic]
      (MATCH_MP
        (SPECL
          [`x0:((num#num)#num)#((num#num)#num)`;
           `x1:((num#num)#num)#((num#num)#num)`;
           `x2:((num#num)#num)#((num#num)#num)`;
           `x3:((num#num)#num)#((num#num)#num)`;
           `x4:((num#num)#num)#((num#num)#num)`;
           `x5:((num#num)#num)#((num#num)#num)`;
           `v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`]
          candle_q_packed_delta_value_six_sound)
        input_contains) in
  let gradient_contains =
    MATCH_MP
      (SPECL
        [`x0:((num#num)#num)#((num#num)#num)`;
         `x1:((num#num)#num)#((num#num)#num)`;
         `x2:((num#num)#num)#((num#num)#num)`;
         `x3:((num#num)#num)#((num#num)#num)`;
         `x4:((num#num)#num)#((num#num)#num)`;
         `x5:((num#num)#num)#((num#num)#num)`;
         `v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`]
        candle_q_packed_delta_gradient_six_sound)
      input_contains in
  let gradient_contains =
    REWRITE_RULE
      [GSYM candle_q_stack_contains_all2;
       candle_real_packed_delta_gradient_six_analytic;
       candle_real_packed_delta_analytic_gradient_six_def]
      gradient_contains in
  let gradient_sequence =
    prove
     (`[candle_analytic_d 0 [v0;v1;v2;v3;v4;v5]
          candle_packed_delta_expr;
        candle_analytic_d 1 [v0;v1;v2;v3;v4;v5]
          candle_packed_delta_expr;
        candle_analytic_d 2 [v0;v1;v2;v3;v4;v5]
          candle_packed_delta_expr;
        candle_analytic_d 3 [v0;v1;v2;v3;v4;v5]
          candle_packed_delta_expr;
        candle_analytic_d 4 [v0;v1;v2;v3;v4;v5]
          candle_packed_delta_expr;
        candle_analytic_d 5 [v0;v1;v2;v3;v4;v5]
          candle_packed_delta_expr] =
       list_of_seq
         (\derivative_coordinate.
           candle_analytic_d derivative_coordinate
             [v0;v1;v2;v3;v4;v5] candle_packed_delta_expr) 6`,
      REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`;
                  num_CONV `3`; num_CONV `2`; num_CONV `1`;
                  list_of_seq; APPEND]) in
  let gradient_contains =
    REWRITE_RULE[gradient_sequence] gradient_contains in
  let packed_hessian_contains =
    MATCH_MP
      (SPECL
        [`x0:((num#num)#num)#((num#num)#num)`;
         `x1:((num#num)#num)#((num#num)#num)`;
         `x2:((num#num)#num)#((num#num)#num)`;
         `x3:((num#num)#num)#((num#num)#num)`;
         `x4:((num#num)#num)#((num#num)#num)`;
         `x5:((num#num)#num)#((num#num)#num)`;
         `v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`]
        candle_q_packed_delta_hessian_six_analytic_contains)
      input_contains in
  let matrix_contains =
    MATCH_MP
      (ISPECL
        [`candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5`;
         `(\i j. candle_analytic_dd i j [v0;v1;v2;v3;v4;v5]
            candle_packed_delta_expr):num->num->real`]
        candle_q_packed_hessian6_expand_contains_symmetric_values)
      packed_hessian_contains in
  let matrix_contains =
    REWRITE_RULE[candle_q_symmetric_hessian6_analytic_values]
      matrix_contains in
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_packed_delta_jet_six_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ACCEPT_TAC value_contains;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC
      (MATCH_MP
        (SPECL
          [`i:num`;
           `candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5`;
           `list_of_seq
             (\derivative_coordinate.
               candle_analytic_d derivative_coordinate
                 [v0;v1;v2;v3;v4;v5] candle_packed_delta_expr) 6`]
          candle_q_stack_lookup_contains)
        gradient_contains) THEN
    ASM_SIMP_TAC[candle_q_real_lookup_list_of_seq];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC candle_q_packed_matrix_list_of_seq_lookup_contains THEN
    EXISTS_TAC `6` THEN
    ASM_REWRITE_TAC[candle_q_packed_hessian6_expand_shape] THEN
    MP_TAC matrix_contains THEN ASM_REWRITE_TAC[]]);;

let candle_q_packed_delta_jet_environment_shape = prove
 (`!environment.
     candle_q_dim_jet_shape 6
       (candle_q_packed_delta_jet_environment environment)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_jet_environment_def] THEN
  MATCH_ACCEPT_TAC candle_q_packed_delta_jet_six_shape);;

let candle_q_packed_delta_jet_environment_contains = prove
 (`!interval_environment real_environment.
     LENGTH real_environment = 6 /\
     candle_q_stack_contains interval_environment real_environment
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_delta_jet_environment interval_environment)
       real_environment candle_packed_delta_expr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let contains index =
    MATCH_MP
      (SPECL
        [mk_small_numeral index;
         `interval_environment:
            ((((num#num)#num)#((num#num)#num))list)`;
         `real_environment:real list`]
        candle_q_stack_lookup_contains)
      (ASSUME
        `candle_q_stack_contains interval_environment real_environment`) in
  let real_environment_six =
    MATCH_MP
      (ISPEC `real_environment:real list` candle_q_six_real_lookup_list)
      (ASSUME `LENGTH (real_environment:real list) = 6`) in
  ONCE_REWRITE_TAC[real_environment_six] THEN
  REWRITE_TAC[candle_q_packed_delta_jet_environment_def] THEN
  MATCH_MP_TAC candle_q_packed_delta_jet_six_analytic_contains THEN
  REPEAT CONJ_TAC THENL
   [ACCEPT_TAC (contains 0); ACCEPT_TAC (contains 1);
    ACCEPT_TAC (contains 2); ACCEPT_TAC (contains 3);
    ACCEPT_TAC (contains 4); ACCEPT_TAC (contains 5)]);;

let candle_q_packed_object_delta_raw_item_def = new_definition
 `candle_q_packed_object_delta_raw_item center_boxes outer_boxes =
    let center_jet = candle_q_packed_delta_jet_environment center_boxes in
    let outer_jet = candle_q_packed_delta_jet_environment outer_boxes in
    let packed_hessian =
      candle_q_packed_delta_hessian_six
        (candle_q_interval_lookup 0 outer_boxes)
        (candle_q_interval_lookup 1 outer_boxes)
        (candle_q_interval_lookup 2 outer_boxes)
        (candle_q_interval_lookup 3 outer_boxes)
        (candle_q_interval_lookup 4 outer_boxes)
        (candle_q_interval_lookup 5 outer_boxes) in
    Candle_q_packed_object_item
      (Candle_q_packed_object_state T
        (candle_q_dim_jet_f center_jet)
        (candle_q_dim_jet_gradient center_jet)
        (candle_q_dim_jet_f outer_jet)
        (candle_q_dim_jet_gradient outer_jet) packed_hessian)
      candle_packed_delta_expr candle_packed_delta_expr`;;

let candle_q_packed_object_delta_item_def = new_definition
 `candle_q_packed_object_delta_item radii center_boxes outer_boxes =
    let center_jet = candle_q_packed_delta_jet_environment center_boxes in
    let packed_hessian =
      candle_q_packed_delta_hessian_six
        (candle_q_interval_lookup 0 outer_boxes)
        (candle_q_interval_lookup 1 outer_boxes)
        (candle_q_interval_lookup 2 outer_boxes)
        (candle_q_interval_lookup 3 outer_boxes)
        (candle_q_interval_lookup 4 outer_boxes)
        (candle_q_interval_lookup 5 outer_boxes) in
    Candle_q_packed_object_item
      (Candle_q_packed_object_state T
        (candle_q_dim_jet_f center_jet)
        (candle_q_dim_jet_gradient center_jet)
        (candle_q_packed_object_value_bound6 radii
          (candle_q_dim_jet_f center_jet)
          (candle_q_dim_jet_gradient center_jet) packed_hessian)
        (candle_q_packed_object_gradient_complete6 radii
          (candle_q_dim_jet_gradient center_jet) packed_hessian)
        packed_hessian)
      candle_packed_delta_expr candle_packed_delta_expr`;;

let candle_q_packed_delta_hessian_environment_length = prove
 (`!environment.
     LENGTH
       (candle_q_packed_delta_hessian_six
         (candle_q_interval_lookup 0 environment)
         (candle_q_interval_lookup 1 environment)
         (candle_q_interval_lookup 2 environment)
         (candle_q_interval_lookup 3 environment)
         (candle_q_interval_lookup 4 environment)
         (candle_q_interval_lookup 5 environment)) = 21`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_hessian_six_def;
              candle_q_packed_delta_hessian_rows_six_def;
              candle_q_packed_delta_sums_def;
              LET_DEF; LET_END_DEF; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_object_delta_raw_item_invariant = prove
 (`!center_boxes outer_boxes.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6
     ==>
     candle_q_packed_object_item_analytic_invariant center_boxes outer_boxes
       T
       (candle_q_dim_jet_f
         (candle_q_packed_delta_jet_environment center_boxes))
       (candle_q_dim_jet_gradient
         (candle_q_packed_delta_jet_environment center_boxes))
       (candle_q_dim_jet_f
         (candle_q_packed_delta_jet_environment outer_boxes))
       (candle_q_dim_jet_gradient
         (candle_q_packed_delta_jet_environment outer_boxes))
       (candle_q_packed_delta_hessian_six
         (candle_q_interval_lookup 0 outer_boxes)
         (candle_q_interval_lookup 1 outer_boxes)
         (candle_q_interval_lookup 2 outer_boxes)
         (candle_q_interval_lookup 3 outer_boxes)
         (candle_q_interval_lookup 4 outer_boxes)
         (candle_q_interval_lookup 5 outer_boxes))
       candle_packed_delta_expr candle_packed_delta_expr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let center_shape =
    SPEC
      `center_boxes:((((num#num)#num)#((num#num)#num))list)`
      candle_q_packed_delta_jet_environment_shape in
  let outer_shape =
    SPEC
      `outer_boxes:((((num#num)#num)#((num#num)#num))list)`
      candle_q_packed_delta_jet_environment_shape in
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_packed_delta_expr_def;
                candle_analytic_valid_dim_def;
                candle_packed_delta_poly_valid];
    MP_TAC center_shape THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def] THEN MESON_TAC[];
    MP_TAC outer_shape THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def;
                candle_q_packed_object_box_jet_def;
                candle_q_packed_delta_jet_environment_def;
                candle_q_packed_delta_jet_six_def;
                candle_q_dim_jet_f_def;
                candle_q_dim_jet_gradient_def;
                candle_q_dim_jet_hessian_def;
                candle_q_dim_jet_make_def; FST; SND] THEN MESON_TAC[];
    X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
    SUBGOAL_THEN `LENGTH (environment:real list) = 6` ASSUME_TAC THENL
     [MP_TAC
        (ASSUME
          `candle_q_stack_contains
            (center_boxes:
              ((((num#num)#num)#((num#num)#num))list)) environment`) THEN
      REWRITE_TAC[candle_q_stack_contains_all2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP candle_all2_length) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[candle_packed_delta_expr_def;
                candle_analytic_regular_at_def] THEN
    MP_TAC
      (MATCH_MP
        (SPECL
          [`center_boxes:
             ((((num#num)#num)#((num#num)#num))list)`;
           `environment:real list`]
          candle_q_packed_delta_jet_environment_contains)
        (CONJ (ASSUME `LENGTH (environment:real list) = 6`)
          (ASSUME
            `candle_q_stack_contains center_boxes environment`))) THEN
    REWRITE_TAC[candle_q_dim_analytic_contains_def;
                candle_q_dim_jet_contains_components_def;
                candle_q_dim_jet_gradient_at_def;
                candle_packed_delta_expr_def;
                candle_q_packed_object_center_first_contains_def] THEN
    MESON_TAC[];
    X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
    SUBGOAL_THEN `LENGTH (environment:real list) = 6` ASSUME_TAC THENL
     [MP_TAC
        (ASSUME
          `candle_q_stack_contains
            (outer_boxes:
              ((((num#num)#num)#((num#num)#num))list)) environment`) THEN
      REWRITE_TAC[candle_q_stack_contains_all2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP candle_all2_length) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_packed_delta_expr_def;
                  candle_analytic_regular_at_def];
      REWRITE_TAC[candle_q_packed_object_box_jet_def;
                  candle_q_packed_delta_jet_environment_def;
                  candle_q_packed_delta_jet_six_def;
                  candle_q_dim_jet_f_def;
                  candle_q_dim_jet_gradient_def;
                  candle_q_dim_jet_make_def; FST; SND] THEN
      MATCH_ACCEPT_TAC
        (REWRITE_RULE
          [candle_q_packed_delta_jet_environment_def;
           candle_q_packed_delta_jet_six_def;
           candle_q_dim_jet_make_def]
          (MATCH_MP
            (SPECL
              [`outer_boxes:
                 ((((num#num)#num)#((num#num)#num))list)`;
               `environment:real list`]
              candle_q_packed_delta_jet_environment_contains)
            (CONJ (ASSUME `LENGTH (environment:real list) = 6`)
              (ASSUME
                `candle_q_stack_contains outer_boxes environment`))))]]);;

let candle_q_packed_object_delta_item_invariant = prove
 (`!center_boxes outer_boxes radii.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii
     ==>
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_packed_object_delta_item
         radii center_boxes outer_boxes)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let raw_invariant =
    MATCH_MP
      (SPECL
        [`center_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:
           ((((num#num)#num)#((num#num)#num))list)`]
        candle_q_packed_object_delta_raw_item_invariant)
      (CONJ
        (ASSUME
          `LENGTH
            (center_boxes:
              ((((num#num)#num)#((num#num)#num))list)) = 6`)
        (ASSUME
          `LENGTH
            (outer_boxes:
              ((((num#num)#num)#((num#num)#num))list)) = 6`)) in
  let recompleted_invariant =
    MATCH_MP
      (ISPECL
        [`center_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`; `T`;
         `candle_q_dim_jet_f
           (candle_q_packed_delta_jet_environment center_boxes)`;
         `candle_q_dim_jet_gradient
           (candle_q_packed_delta_jet_environment center_boxes)`;
         `candle_q_dim_jet_f
           (candle_q_packed_delta_jet_environment outer_boxes)`;
         `candle_q_dim_jet_gradient
           (candle_q_packed_delta_jet_environment outer_boxes)`;
         `candle_q_packed_delta_hessian_six
           (candle_q_interval_lookup 0 outer_boxes)
           (candle_q_interval_lookup 1 outer_boxes)
           (candle_q_interval_lookup 2 outer_boxes)
           (candle_q_interval_lookup 3 outer_boxes)
           (candle_q_interval_lookup 4 outer_boxes)
           (candle_q_interval_lookup 5 outer_boxes)`;
         `candle_packed_delta_expr`; `candle_packed_delta_expr`]
        candle_q_packed_object_item_recomplete_analytic_invariant)
      (end_itlist CONJ
        [ASSUME
           `LENGTH
             (outer_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
           `candle_q_packed_source_correspondence
             outer_boxes center_boxes outer_boxes radii`;
         raw_invariant]) in
  REWRITE_TAC[candle_q_packed_object_delta_item_def;
              LET_DEF; LET_END_DEF;
              candle_q_packed_object_source_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC
      (SPEC
        `center_boxes:((((num#num)#num)#((num#num)#num))list)`
        candle_q_packed_delta_jet_environment_shape) THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def] THEN MESON_TAC[];
    MATCH_MP_TAC candle_q_packed_object_gradient_complete6_length THEN
    MP_TAC
      (SPEC
        `center_boxes:((((num#num)#num)#((num#num)#num))list)`
        candle_q_packed_delta_jet_environment_shape) THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def] THEN MESON_TAC[];
    REWRITE_TAC[candle_q_packed_delta_hessian_environment_length];
    MATCH_ACCEPT_TAC recompleted_invariant]);;

let candle_q_stack_contains_list_of_seq_lookup = prove
 (`!items (values:num->real) n.
     LENGTH items = n /\
     (!i. i < n
          ==> candle_q_interval_contains
                (candle_q_interval_lookup i items) (values i))
     ==>
     candle_q_stack_contains items (list_of_seq values n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let reconstruction =
    MATCH_MP
      (SPECL
        [`n:num`;
         `items:((((num#num)#num)#((num#num)#num))list)`]
        Candle_cv_analytic_expr_packed_source_object_mul_sound.candle_q_interval_list_eq_list_of_seq_lookup)
      (ASSUME
        `LENGTH
          (items:((((num#num)#num)#((num#num)#num))list)) = n`) in
  REWRITE_TAC[candle_q_stack_contains_all2] THEN
  ONCE_REWRITE_TAC[reconstruction] THEN
  REWRITE_TAC[candle_all2_list_of_seq] THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_delta_completed_gradient_contains = prove
 (`!center_boxes outer_boxes radii environment.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_stack_contains outer_boxes environment
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_gradient_complete6 radii
         (candle_q_dim_jet_gradient
           (candle_q_packed_delta_jet_environment center_boxes))
         (candle_q_packed_delta_hessian_six
           (candle_q_interval_lookup 0 outer_boxes)
           (candle_q_interval_lookup 1 outer_boxes)
           (candle_q_interval_lookup 2 outer_boxes)
           (candle_q_interval_lookup 3 outer_boxes)
           (candle_q_interval_lookup 4 outer_boxes)
           (candle_q_interval_lookup 5 outer_boxes)))
       (list_of_seq
         (\i. candle_analytic_d i environment candle_packed_delta_expr) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let item_invariant =
    MATCH_MP
      (SPECL
        [`center_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`]
        candle_q_packed_object_delta_item_invariant)
      (end_itlist CONJ
        [ASSUME
           `LENGTH
             (center_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
           `LENGTH
             (outer_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
           `candle_q_packed_source_correspondence
             outer_boxes center_boxes outer_boxes radii`]) in
  let item_invariant =
    REWRITE_RULE
      [candle_q_packed_object_delta_item_def;
       LET_DEF; LET_END_DEF;
       candle_q_packed_object_source_item_analytic_invariant_def]
      item_invariant in
  let item_rest = CONJUNCT2 item_invariant in
  let completed_gradient_length = CONJUNCT1 item_rest in
  let object_invariant = CONJUNCT2 (CONJUNCT2 item_rest) in
  let object_invariant =
    REWRITE_RULE[candle_q_packed_object_item_analytic_invariant_def]
      object_invariant in
  let outer_invariant =
    CONJUNCT2
      (CONJUNCT2
        (CONJUNCT2
          (CONJUNCT2 object_invariant))) in
  let outer_at_environment =
    MATCH_MP
      (SPEC `environment:real list` outer_invariant)
      (ASSUME
        `candle_q_stack_contains
          (outer_boxes:
            ((((num#num)#num)#((num#num)#num))list)) environment`) in
  let box_contains = CONJUNCT2 outer_at_environment in
  let box_components =
    REWRITE_RULE
      [candle_q_dim_analytic_contains_def;
       candle_q_dim_jet_contains_components_def;
       candle_q_packed_object_box_jet_def;
       candle_q_dim_jet_gradient_at_def;
       candle_q_dim_jet_gradient_def;
       candle_q_dim_jet_make_def; FST; SND]
      box_contains in
  let gradient_contains = CONJUNCT1 (CONJUNCT2 box_components) in
  let gradient_contains =
    REWRITE_RULE[GSYM candle_q_dim_jet_gradient_def]
      gradient_contains in
  MATCH_ACCEPT_TAC
    (MATCH_MP
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (SPECL
          [`candle_q_packed_object_gradient_complete6 radii
             (candle_q_dim_jet_gradient
               (candle_q_packed_delta_jet_environment center_boxes))
             (candle_q_packed_delta_hessian_six
               (candle_q_interval_lookup 0 outer_boxes)
               (candle_q_interval_lookup 1 outer_boxes)
               (candle_q_interval_lookup 2 outer_boxes)
               (candle_q_interval_lookup 3 outer_boxes)
               (candle_q_interval_lookup 4 outer_boxes)
               (candle_q_interval_lookup 5 outer_boxes))`;
           `(\i. candle_analytic_d i environment candle_packed_delta_expr)`;
           `6`]
          candle_q_stack_contains_list_of_seq_lookup))
      (CONJ completed_gradient_length gradient_contains)));;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_delta_jet_six_shape;
     candle_q_packed_delta_jet_six_analytic_contains;
     candle_q_packed_delta_jet_environment_shape;
     candle_q_packed_delta_jet_environment_contains;
     candle_q_packed_delta_hessian_environment_length;
     candle_q_packed_object_delta_raw_item_invariant;
     candle_q_packed_object_delta_item_invariant;
     candle_q_stack_contains_list_of_seq_lookup;
     candle_q_packed_object_delta_completed_gradient_contains] then
  failwith "packed object shared delta sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_DELTA_BASE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
