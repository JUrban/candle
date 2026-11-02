(* ========================================================================== *)
(* Authenticated source identity for the optimized [4 * x_i * delta] object. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The optimized jet is proved against a         *)
(* factored analytic expression, while the decoded Flyspeck source contains  *)
(* one compiled polynomial instruction.  The established value, gradient,   *)
(* and Hessian identities transport the exact object invariant to that       *)
(* authenticated source expression.                                          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_delta_product_object_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_specialization_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_delta_product_source_sound = struct

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_packed_source_delta_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_product_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_specialization_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_delta_product_sound;;
open Candle_cv_analytic_expr_packed_source_object_delta_product_object_sound;;

let candle_q_packed_object_delta_product_invariant_source = prove
 (`!center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian coordinate.
     coordinate < 3 /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian
       (candle_packed_delta_product_expr coordinate)
       (candle_packed_delta_product_expr coordinate)
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes domain center_value center_gradient
       value_bound gradient_bounds packed_hessian
       (candle_packed_delta_product_source_expr coordinate)
       (candle_packed_delta_product_source_expr coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let input_invariant =
    REWRITE_RULE[candle_q_packed_object_item_analytic_invariant_def]
      (ASSUME
        `candle_q_packed_object_item_analytic_invariant
          center_boxes outer_boxes domain center_value center_gradient
          value_bound gradient_bounds packed_hessian
          (candle_packed_delta_product_expr coordinate)
          (candle_packed_delta_product_expr coordinate)`) in
  let input_domain = CONJUNCT2 input_invariant in
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_packed_delta_product_source_expr_def;
                candle_packed_delta_product_source_poly_def;
                candle_analytic_valid_dim_def;
                candle_poly_valid_dim_def;
                candle_packed_delta_poly_valid] THEN
    ASM_ARITH_TAC;
    DISCH_TAC THEN
    let domain_components =
      MATCH_MP input_domain (ASSUME `domain:bool`) in
    let center_length = CONJUNCT1 domain_components in
    let box_shape = CONJUNCT1 (CONJUNCT2 domain_components) in
    let center_all =
      CONJUNCT1 (CONJUNCT2 (CONJUNCT2 domain_components)) in
    let box_all =
      CONJUNCT2 (CONJUNCT2 (CONJUNCT2 domain_components)) in
    REPEAT CONJ_TAC THENL
     [ACCEPT_TAC center_length;
      ACCEPT_TAC box_shape;
      (fun goal ->
        (X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
         let center_components =
           MATCH_MP (SPEC `environment:real list` center_all)
             (ASSUME
               `candle_q_stack_contains center_boxes environment`) in
         CONJ_TAC THENL
          [REWRITE_TAC[candle_packed_delta_product_source_expr_def;
                       candle_analytic_regular_at_def];
           MP_TAC (CONJUNCT2 center_components) THEN
           REWRITE_TAC
             [candle_q_packed_object_center_first_contains_def;
              candle_packed_delta_product_source_value;
              candle_packed_delta_product_source_d]]) goal);
      (fun goal ->
        (X_GEN_TAC `environment:real list` THEN DISCH_TAC THEN
         let box_components =
           MATCH_MP (SPEC `environment:real list` box_all)
             (ASSUME
               `candle_q_stack_contains outer_boxes environment`) in
         CONJ_TAC THENL
          [REWRITE_TAC[candle_packed_delta_product_source_expr_def;
                       candle_analytic_regular_at_def];
           MP_TAC (CONJUNCT2 box_components) THEN
           REWRITE_TAC
             [candle_q_dim_analytic_contains_delta_product_source]]) goal)]]);;

let candle_q_packed_object_delta_product_source_item_def = new_definition
 `candle_q_packed_object_delta_product_source_item
      radii center_boxes outer_boxes coordinate =
    let center_jet =
      candle_q_packed_delta_product_jet_environment coordinate center_boxes in
    let packed_hessian =
      candle_q_packed_object_delta_product_hessian
        radii center_boxes outer_boxes coordinate in
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
      (candle_packed_delta_product_source_expr coordinate)
      (candle_packed_delta_product_source_expr coordinate)`;;

let candle_q_packed_object_delta_product_source_item_invariant = prove
 (`!center_boxes outer_boxes radii coordinate.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     coordinate < 3
     ==>
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_packed_object_delta_product_source_item
         radii center_boxes outer_boxes coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let factored_item =
    MATCH_MP
      (SPECL
        [`center_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`; `coordinate:num`]
        candle_q_packed_object_delta_product_item_invariant)
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
             outer_boxes center_boxes outer_boxes radii`;
         ASSUME `(coordinate:num) < 3`]) in
  let factored_components =
    REWRITE_RULE
      [candle_q_packed_object_delta_product_item_def;
       LET_DEF; LET_END_DEF;
       candle_q_packed_object_source_item_analytic_invariant_def]
      factored_item in
  let center_length = CONJUNCT1 factored_components in
  let gradient_length = CONJUNCT1 (CONJUNCT2 factored_components) in
  let hessian_length =
    CONJUNCT1 (CONJUNCT2 (CONJUNCT2 factored_components)) in
  let factored_invariant =
    CONJUNCT2 (CONJUNCT2 (CONJUNCT2 factored_components)) in
  REWRITE_TAC[candle_q_packed_object_delta_product_source_item_def;
              LET_DEF; LET_END_DEF;
              candle_q_packed_object_source_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [ACCEPT_TAC center_length;
    ACCEPT_TAC gradient_length;
    ACCEPT_TAC hessian_length;
    MATCH_MP_TAC candle_q_packed_object_delta_product_invariant_source THEN
    ASM_REWRITE_TAC[] THEN
    ACCEPT_TAC factored_invariant]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_delta_product_invariant_source;
     candle_q_packed_object_delta_product_source_item_invariant] then
  failwith "packed object delta product source sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_DELTA_PRODUCT_SOURCE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
