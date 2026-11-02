(* ========================================================================== *)
(* Executable exact object-q states for the six authenticated delta shortcuts. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  These definitions deliberately consume the   *)
(* same explicit radius vector as the packed word checker.  In particular,   *)
(* they do not reuse the older source evaluator's independently rounded      *)
(* center/outer radii.                                                        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_linear_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_product_result_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_delta_product_source_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_specialized_compute = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_packed_source_delta_gradient;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_product_result_compute;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_result_compute;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_linear_compute;;
open Candle_cv_analytic_expr_packed_source_object_delta_base_sound;;
open Candle_cv_analytic_expr_packed_source_object_delta_neg_derivative_sound;;
open Candle_cv_analytic_expr_packed_source_object_delta_product_sound;;
open Candle_cv_analytic_expr_packed_source_object_delta_product_source_sound;;

let candle_cv_q_packed_object_delta_product_hessian_def = new_definition
 `candle_cv_q_packed_object_delta_product_hessian
      radii center_boxes outer_boxes coordinate =
    let delta_hessian =
      candle_cv_q_packed_delta_hessian_six
        (candle_cv_q_interval_lookup (Cexp_num 0) outer_boxes)
        (candle_cv_q_interval_lookup (Cexp_num 1) outer_boxes)
        (candle_cv_q_interval_lookup (Cexp_num 2) outer_boxes)
        (candle_cv_q_interval_lookup (Cexp_num 3) outer_boxes)
        (candle_cv_q_interval_lookup (Cexp_num 4) outer_boxes)
        (candle_cv_q_interval_lookup (Cexp_num 5) outer_boxes) in
    let delta_gradient =
      candle_cv_q_packed_object_gradient_complete6 radii
        (candle_cv_q_packed_delta_gradient_six
          (candle_cv_q_interval_lookup (Cexp_num 0) center_boxes)
          (candle_cv_q_interval_lookup (Cexp_num 1) center_boxes)
          (candle_cv_q_interval_lookup (Cexp_num 2) center_boxes)
          (candle_cv_q_interval_lookup (Cexp_num 3) center_boxes)
          (candle_cv_q_interval_lookup (Cexp_num 4) center_boxes)
          (candle_cv_q_interval_lookup (Cexp_num 5) center_boxes))
        delta_hessian in
    candle_cv_q_packed_delta_product_hessian_six coordinate
      (candle_cv_q_interval_lookup coordinate outer_boxes)
      delta_gradient delta_hessian`;;

let candle_cv_q_packed_object_delta_product_hessian_correct = prove
 (`!radii center_boxes outer_boxes coordinate.
     candle_cv_q_packed_object_delta_product_hessian
       (candle_cv_q_list radii)
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (Cexp_num coordinate) =
     candle_cv_q_interval_list
       (candle_q_packed_object_delta_product_hessian
         radii center_boxes outer_boxes coordinate)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_q_packed_delta_hessian_six
        (candle_q_interval_lookup 0 outer_boxes)
        (candle_q_interval_lookup 1 outer_boxes)
        (candle_q_interval_lookup 2 outer_boxes)
        (candle_q_interval_lookup 3 outer_boxes)
        (candle_q_interval_lookup 4 outer_boxes)
        (candle_q_interval_lookup 5 outer_boxes)) = 21`
   ASSUME_TAC THENL
   [REWRITE_TAC[candle_q_packed_delta_hessian_six_length];
    SUBGOAL_THEN
     `candle_cv_q_packed_object_gradient_complete6
        (candle_cv_q_list radii)
        (candle_cv_q_interval_list
          (candle_q_packed_delta_gradient_six
            (candle_q_interval_lookup 0 center_boxes)
            (candle_q_interval_lookup 1 center_boxes)
            (candle_q_interval_lookup 2 center_boxes)
            (candle_q_interval_lookup 3 center_boxes)
            (candle_q_interval_lookup 4 center_boxes)
            (candle_q_interval_lookup 5 center_boxes)))
        (candle_cv_q_interval_list
          (candle_q_packed_delta_hessian_six
            (candle_q_interval_lookup 0 outer_boxes)
            (candle_q_interval_lookup 1 outer_boxes)
            (candle_q_interval_lookup 2 outer_boxes)
            (candle_q_interval_lookup 3 outer_boxes)
            (candle_q_interval_lookup 4 outer_boxes)
            (candle_q_interval_lookup 5 outer_boxes))) =
      candle_cv_q_interval_list
        (candle_q_packed_object_gradient_complete6 radii
          (candle_q_packed_delta_gradient_six
            (candle_q_interval_lookup 0 center_boxes)
            (candle_q_interval_lookup 1 center_boxes)
            (candle_q_interval_lookup 2 center_boxes)
            (candle_q_interval_lookup 3 center_boxes)
            (candle_q_interval_lookup 4 center_boxes)
            (candle_q_interval_lookup 5 center_boxes))
          (candle_q_packed_delta_hessian_six
            (candle_q_interval_lookup 0 outer_boxes)
            (candle_q_interval_lookup 1 outer_boxes)
            (candle_q_interval_lookup 2 outer_boxes)
            (candle_q_interval_lookup 3 outer_boxes)
            (candle_q_interval_lookup 4 outer_boxes)
            (candle_q_interval_lookup 5 outer_boxes)))`
     ASSUME_TAC THENL
     [MATCH_MP_TAC candle_cv_q_packed_object_gradient_complete6_correct THEN
      ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC
      [candle_cv_q_packed_object_delta_product_hessian_def;
       candle_q_packed_object_delta_product_hessian_def;
       candle_q_packed_delta_jet_environment_def;
       candle_q_packed_delta_jet_six_def;
       candle_q_dim_jet_gradient_def;
       candle_q_dim_jet_make_def; FST; SND;
       candle_cv_q_interval_lookup_correct;
       candle_cv_q_packed_delta_hessian_six_correct;
       candle_cv_q_packed_delta_gradient_six_correct;
       candle_cv_q_packed_object_gradient_complete6_correct;
       candle_cv_q_packed_delta_product_hessian_six_correct;
       LET_DEF; LET_END_DEF]]]);;

let _ = print_endline "CANDLE_OBJECT_SPECIALIZED_STAGE product_hessian";;

let candle_cv_q_packed_object_delta_product_source_item_state_def =
  new_definition
 `candle_cv_q_packed_object_delta_product_source_item_state
      radii center_boxes outer_boxes coordinate =
    let center_jet =
      candle_cv_q_packed_delta_product_jet_environment coordinate
        center_boxes in
    let packed_hessian =
      candle_cv_q_packed_object_delta_product_hessian
        radii center_boxes outer_boxes coordinate in
    candle_cv_q_packed_object_state_recomplete radii (Cexp_num 1)
      (candle_cv_q_dim_jet_f center_jet)
      (candle_cv_q_dim_jet_gradient center_jet)
      packed_hessian`;;

let candle_cv_q_packed_object_delta_product_source_item_state_correct = prove
 (`!radii center_boxes outer_boxes coordinate.
     LENGTH radii = 6
     ==>
     candle_cv_q_packed_object_delta_product_source_item_state
       (candle_cv_q_list radii)
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (Cexp_num coordinate) =
     candle_cv_q_packed_object_item_state_encode
       (candle_q_packed_object_delta_product_source_item
         radii center_boxes outer_boxes coordinate)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_q_packed_object_delta_product_hessian
        radii center_boxes outer_boxes coordinate) = 21`
   ASSUME_TAC THENL
   [REWRITE_TAC
      [candle_q_packed_object_delta_product_hessian_def;
       LET_DEF; LET_END_DEF;
       candle_q_packed_delta_product_hessian_six_length];
    REWRITE_TAC
      [candle_cv_q_packed_object_delta_product_source_item_state_def;
       candle_q_packed_object_delta_product_source_item_def;
       candle_cv_q_packed_object_item_state_encode_def;
       LET_DEF; LET_END_DEF;
       candle_cv_q_packed_delta_product_jet_environment_correct;
       candle_cv_q_dim_jet_f_correct;
       candle_cv_q_dim_jet_gradient_correct;
       candle_cv_q_packed_object_delta_product_hessian_correct;
       candle_cv_bool_true_encoding] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_state_recomplete_correct THEN
    ASM_REWRITE_TAC[]]);;

let _ = print_endline "CANDLE_OBJECT_SPECIALIZED_STAGE product_item";;

let candle_cv_q_packed_object_delta_neg_derivative_item_state_def =
  new_definition
 `candle_cv_q_packed_object_delta_neg_derivative_item_state
      radii center_boxes coordinate =
    let center_jet =
      candle_cv_q_packed_delta_neg_derivative_jet_environment coordinate
        center_boxes in
    let packed_hessian =
      candle_cv_q_packed_delta_neg_derivative_hessian_six coordinate in
    candle_cv_q_packed_object_state_recomplete radii (Cexp_num 1)
      (candle_cv_q_dim_jet_f center_jet)
      (candle_cv_q_dim_jet_gradient center_jet)
      packed_hessian`;;

let candle_cv_q_packed_object_delta_neg_derivative_item_state_correct = prove
 (`!radii center_boxes coordinate.
     LENGTH radii = 6 /\
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_cv_q_packed_object_delta_neg_derivative_item_state
       (candle_cv_q_list radii)
       (candle_cv_q_interval_list center_boxes)
       (Cexp_num coordinate) =
     candle_cv_q_packed_object_item_state_encode
       (candle_q_packed_object_delta_neg_derivative_item
         radii center_boxes coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let jet_th =
    MATCH_MP
      (SPECL
        [`coordinate:num`;
         `center_boxes:
            ((((num#num)#num)#((num#num)#num))list)`]
        candle_cv_q_packed_delta_neg_derivative_jet_environment_correct)
      (ASSUME `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`) in
  REWRITE_TAC
    [candle_cv_q_packed_object_delta_neg_derivative_item_state_def;
     candle_q_packed_object_delta_neg_derivative_item_def;
     candle_cv_q_packed_object_item_state_encode_def;
     LET_DEF; LET_END_DEF;
     jet_th;
     candle_cv_q_dim_jet_f_correct;
     candle_cv_q_dim_jet_gradient_correct;
     candle_cv_q_packed_delta_neg_derivative_hessian_six_correct;
     candle_cv_bool_true_encoding] THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_recomplete_correct THEN
  ASM_REWRITE_TAC[candle_q_packed_delta_neg_derivative_hessian_six_length]);;

let _ = print_endline "CANDLE_OBJECT_SPECIALIZED_STAGE neg_derivative_item";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_delta_product_hessian_correct;
     candle_cv_q_packed_object_delta_product_source_item_state_correct;
     candle_cv_q_packed_object_delta_neg_derivative_item_state_correct] then
  failwith "packed object specialized compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_SPECIALIZED_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
