(* ========================================================================== *)
(* Exact object-q invariant for the authenticated negative-delta shortcuts. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Unlike the older normalized Taylor-result    *)
(* bridge, this file keeps the production object's center value/gradient and *)
(* packed Hessian, then applies the exact faithful recompletion used by the  *)
(* object-q checker.                                                         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_ordinary_program_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_specialized_result_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_delta_neg_derivative_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_state_complete_sound;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_jet_sound;;
open Candle_cv_analytic_expr_packed_source_delta_specialized_result_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_object_gradient_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_recomplete_sound;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;

let candle_q_packed_object_delta_neg_derivative_raw_item_def = new_definition
 `candle_q_packed_object_delta_neg_derivative_raw_item
      center_boxes outer_boxes coordinate =
    let center_jet =
      candle_q_packed_delta_neg_derivative_jet_environment coordinate
        center_boxes in
    let outer_jet =
      candle_q_packed_delta_neg_derivative_jet_environment coordinate
        outer_boxes in
    Candle_q_packed_object_item
      (Candle_q_packed_object_state T
        (candle_q_dim_jet_f center_jet)
        (candle_q_dim_jet_gradient center_jet)
        (candle_q_dim_jet_f outer_jet)
        (candle_q_dim_jet_gradient outer_jet)
        (candle_q_packed_delta_neg_derivative_hessian_six coordinate))
      (candle_packed_delta_neg_derivative_expr coordinate)
      (candle_packed_delta_neg_derivative_expr coordinate)`;;

let candle_q_packed_object_delta_neg_derivative_item_def = new_definition
 `candle_q_packed_object_delta_neg_derivative_item
      radii center_boxes coordinate =
    let center_jet =
      candle_q_packed_delta_neg_derivative_jet_environment coordinate
        center_boxes in
    let packed_hessian =
      candle_q_packed_delta_neg_derivative_hessian_six coordinate in
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
      (candle_packed_delta_neg_derivative_expr coordinate)
      (candle_packed_delta_neg_derivative_expr coordinate)`;;

let candle_q_packed_object_delta_neg_derivative_hessian_length = prove
 (`!coordinate.
     LENGTH
       (candle_q_packed_delta_neg_derivative_hessian_six coordinate) = 21`,
  REWRITE_TAC
    [candle_q_packed_delta_neg_derivative_hessian_six_def;
     candle_q_dim_interval_list_neg_length;
     candle_q_packed_delta_hessian_six_def;
     candle_q_packed_delta_hessian_rows_six_def;
     candle_q_packed_delta_sums_def;
     candle_q_packed_delta_basis_six_def;
     LET_DEF; LET_END_DEF; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_object_delta_neg_derivative_raw_item_invariant = prove
 (`!center_boxes outer_boxes coordinate.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_q_packed_object_item_analytic_invariant center_boxes outer_boxes
       T
       (candle_q_dim_jet_f
         (candle_q_packed_delta_neg_derivative_jet_environment
           coordinate center_boxes))
       (candle_q_dim_jet_gradient
         (candle_q_packed_delta_neg_derivative_jet_environment
           coordinate center_boxes))
       (candle_q_dim_jet_f
         (candle_q_packed_delta_neg_derivative_jet_environment
           coordinate outer_boxes))
       (candle_q_dim_jet_gradient
         (candle_q_packed_delta_neg_derivative_jet_environment
           coordinate outer_boxes))
       (candle_q_packed_delta_neg_derivative_hessian_six coordinate)
       (candle_packed_delta_neg_derivative_expr coordinate)
       (candle_packed_delta_neg_derivative_expr coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let coordinate_cases =
    ASSUME `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` in
  let center_shape =
    MATCH_MP
      (SPECL
        [`coordinate:num`;
         `center_boxes:
           ((((num#num)#num)#((num#num)#num))list)`]
        candle_q_packed_delta_neg_derivative_jet_environment_shape)
      coordinate_cases in
  let outer_shape =
    MATCH_MP
      (SPECL
        [`coordinate:num`;
         `outer_boxes:
           ((((num#num)#num)#((num#num)#num))list)`]
        candle_q_packed_delta_neg_derivative_jet_environment_shape)
      coordinate_cases in
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_packed_delta_neg_derivative_expr_def;
                candle_analytic_valid_dim_def] THEN
    MATCH_MP_TAC candle_packed_delta_neg_derivative_poly_valid THEN
    ASM_ARITH_TAC;
    MP_TAC center_shape THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def] THEN MESON_TAC[];
    MP_TAC outer_shape THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def;
                candle_q_packed_object_box_jet_def;
                candle_q_packed_delta_neg_derivative_jet_environment_def;
                candle_q_packed_delta_neg_derivative_jet_six_def;
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
              ((((num#num)#num)#((num#num)#num))list))
            (environment:real list)`) THEN
      REWRITE_TAC[candle_q_stack_contains_all2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP candle_all2_length) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[candle_packed_delta_neg_derivative_expr_def;
                candle_analytic_regular_at_def] THEN
    MP_TAC
      (MATCH_MP
        (SPECL
          [`center_boxes:
             ((((num#num)#num)#((num#num)#num))list)`;
           `environment:real list`; `coordinate:num`]
          candle_q_packed_delta_neg_derivative_jet_environment_contains)
        (CONJ (ASSUME `LENGTH (environment:real list) = 6`)
          (CONJ
            (ASSUME
              `candle_q_stack_contains center_boxes environment`)
            coordinate_cases))) THEN
    REWRITE_TAC[candle_q_dim_analytic_contains_def;
                candle_q_dim_jet_contains_components_def;
                candle_q_dim_jet_gradient_at_def;
                candle_packed_delta_neg_derivative_expr_def;
                candle_q_packed_object_center_first_contains_def] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "center_value_contains")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_gradient_contains")
          (K ALL_TAC))) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
    SUBGOAL_THEN `LENGTH (environment:real list) = 6` ASSUME_TAC THENL
     [MP_TAC
        (ASSUME
          `candle_q_stack_contains
            (outer_boxes:
              ((((num#num)#num)#((num#num)#num))list))
            (environment:real list)`) THEN
      REWRITE_TAC[candle_q_stack_contains_all2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP candle_all2_length) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_packed_delta_neg_derivative_expr_def;
                  candle_analytic_regular_at_def];
      REWRITE_TAC[candle_q_packed_object_box_jet_def;
                  candle_q_packed_delta_neg_derivative_jet_environment_def;
                  candle_q_packed_delta_neg_derivative_jet_six_def;
                  candle_q_dim_jet_f_def;
                  candle_q_dim_jet_gradient_def;
                  candle_q_dim_jet_make_def; FST; SND] THEN
      MATCH_ACCEPT_TAC
        (REWRITE_RULE
          [candle_q_packed_delta_neg_derivative_jet_environment_def;
           candle_q_packed_delta_neg_derivative_jet_six_def;
           candle_q_dim_jet_make_def]
          (MATCH_MP
            (SPECL
              [`outer_boxes:
                 ((((num#num)#num)#((num#num)#num))list)`;
               `environment:real list`; `coordinate:num`]
              candle_q_packed_delta_neg_derivative_jet_environment_contains)
            (CONJ (ASSUME `LENGTH (environment:real list) = 6`)
              (CONJ
                (ASSUME
                  `candle_q_stack_contains outer_boxes environment`)
                coordinate_cases))))]]);;

let candle_q_packed_object_delta_neg_derivative_item_invariant = prove
 (`!center_boxes outer_boxes radii coordinate.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_packed_object_delta_neg_derivative_item
         radii center_boxes coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let coordinate_cases =
    ASSUME `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` in
  let raw_invariant =
    MATCH_MP
      (SPECL
        [`center_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `coordinate:num`]
        candle_q_packed_object_delta_neg_derivative_raw_item_invariant)
      (end_itlist CONJ
        [ASSUME
           `LENGTH
             (center_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
           `LENGTH
             (outer_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         coordinate_cases]) in
  let recompleted_invariant =
    MATCH_MP
      (ISPECL
        [`center_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`; `T`;
         `candle_q_dim_jet_f
           (candle_q_packed_delta_neg_derivative_jet_environment
             coordinate center_boxes)`;
         `candle_q_dim_jet_gradient
           (candle_q_packed_delta_neg_derivative_jet_environment
             coordinate center_boxes)`;
         `candle_q_dim_jet_f
           (candle_q_packed_delta_neg_derivative_jet_environment
             coordinate outer_boxes)`;
         `candle_q_dim_jet_gradient
           (candle_q_packed_delta_neg_derivative_jet_environment
             coordinate outer_boxes)`;
         `candle_q_packed_delta_neg_derivative_hessian_six coordinate`;
         `candle_packed_delta_neg_derivative_expr coordinate`;
         `candle_packed_delta_neg_derivative_expr coordinate`]
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
  REWRITE_TAC[candle_q_packed_object_delta_neg_derivative_item_def;
              LET_DEF; LET_END_DEF;
              candle_q_packed_object_source_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC
      (MATCH_MP
        (SPECL
          [`coordinate:num`;
           `center_boxes:
             ((((num#num)#num)#((num#num)#num))list)`]
          candle_q_packed_delta_neg_derivative_jet_environment_shape)
        (ASSUME
          `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`)) THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def] THEN MESON_TAC[];
    MATCH_MP_TAC candle_q_packed_object_gradient_complete6_length THEN
    MP_TAC
      (MATCH_MP
        (SPECL
          [`coordinate:num`;
           `center_boxes:
             ((((num#num)#num)#((num#num)#num))list)`]
          candle_q_packed_delta_neg_derivative_jet_environment_shape)
        (ASSUME
          `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`)) THEN
    REWRITE_TAC[candle_q_dim_jet_shape_def] THEN MESON_TAC[];
    REWRITE_TAC[candle_q_packed_object_delta_neg_derivative_hessian_length];
    MATCH_ACCEPT_TAC recompleted_invariant]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_delta_neg_derivative_hessian_length;
     candle_q_packed_object_delta_neg_derivative_raw_item_invariant;
     candle_q_packed_object_delta_neg_derivative_item_invariant] then
  failwith "packed object negative delta derivative sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_DELTA_NEG_DERIVATIVE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
