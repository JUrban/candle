(* ========================================================================== *)
(* Exact encoded-state projection of logical object-q source items.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Analytic expressions stay in the logical    *)
(* soundness layer; executable replay carries precisely the proved six-field *)
(* state projection used by final acceptance.                                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_unary_compute.ml";;

module Candle_cv_analytic_expr_packed_source_object_item_compute = struct

open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_linear_compute;;
open Candle_cv_analytic_expr_packed_source_object_mul_compute;;
open Candle_cv_analytic_expr_packed_source_object_unary_compute;;

let candle_cv_q_packed_object_source_item_neg_correct = prove
 (`!radii center_boxes outer_boxes item.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes item
     ==>
     candle_cv_q_packed_object_state_neg
       (candle_cv_q_list radii)
       (candle_cv_q_packed_object_item_state_encode item) =
     candle_cv_q_packed_object_item_state_encode
       (candle_q_packed_object_source_item_neg radii item)`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `item:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_analytic_invariant_def;
     candle_q_packed_object_source_item_neg_def;
     candle_cv_q_packed_object_item_state_encode_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_neg_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_ITEM_STAGE neg";;

let candle_cv_q_packed_object_source_item_add_correct = prove
 (`!radii center_boxes outer_boxes left right.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes left /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes right
     ==>
     candle_cv_q_packed_object_state_add
       (candle_cv_q_list radii)
       (candle_cv_q_packed_object_item_state_encode left)
       (candle_cv_q_packed_object_item_state_encode right) =
     candle_cv_q_packed_object_item_state_encode
       (candle_q_packed_object_source_item_add radii left right)`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `left:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  MP_TAC
    (SPEC `right:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_analytic_invariant_def;
     candle_q_packed_object_source_item_add_def;
     candle_cv_q_packed_object_item_state_encode_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_add_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_ITEM_STAGE add";;

let candle_cv_q_packed_object_source_item_mul_correct = prove
 (`!radii center_boxes outer_boxes left right.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes left /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes right
     ==>
     candle_cv_q_packed_object_state_mul
       (candle_cv_q_list radii)
       (candle_cv_q_packed_object_item_state_encode left)
       (candle_cv_q_packed_object_item_state_encode right) =
     candle_cv_q_packed_object_item_state_encode
       (candle_q_packed_object_source_item_mul radii left right)`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `left:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  MP_TAC
    (SPEC `right:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_analytic_invariant_def;
     candle_q_packed_object_source_item_mul_def;
     candle_cv_q_packed_object_item_state_encode_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_mul_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_ITEM_STAGE mul";;

let candle_cv_q_packed_object_item_center_value_correct = prove
 (`!item.
     candle_cv_q_packed_object_state_center_value
       (candle_cv_q_packed_object_item_state_encode item) =
     candle_cv_q_interval
       (candle_q_packed_object_item_center_value item)`,
  GEN_TAC THEN
  MP_TAC
    (SPEC `item:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_item_state_encode_def;
     candle_q_packed_object_item_center_value_def;
     candle_cv_q_packed_object_state_center_value_correct]);;

let candle_cv_q_packed_object_item_value_bound_correct = prove
 (`!item.
     candle_cv_q_packed_object_state_value_bound
       (candle_cv_q_packed_object_item_state_encode item) =
     candle_cv_q_interval
       (candle_q_packed_object_item_value_bound item)`,
  GEN_TAC THEN
  MP_TAC
    (SPEC `item:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_item_state_encode_def;
     candle_q_packed_object_item_value_bound_def;
     candle_cv_q_packed_object_state_value_bound_correct]);;

let _ = print_endline "CANDLE_OBJECT_ITEM_STAGE projections";;

let candle_cv_q_packed_object_source_item_inverse_correct = prove
 (`!radii center_boxes outer_boxes center_reciprocal box_reciprocal item.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes item
     ==>
     candle_cv_q_packed_object_state_inverse
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_reciprocal)
       (candle_cv_q_interval box_reciprocal)
       (candle_cv_q_packed_object_item_state_encode item) =
     candle_cv_q_packed_object_item_state_encode
       (candle_q_packed_object_source_item_inverse radii
         center_reciprocal box_reciprocal item)`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `item:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_analytic_invariant_def;
     candle_q_packed_object_source_item_inverse_def;
     candle_cv_q_packed_object_item_state_encode_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_inverse_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_ITEM_STAGE inverse";;

let candle_cv_q_packed_object_source_item_sqrt_correct = prove
 (`!radii center_boxes outer_boxes center_root center_first box_root
       box_first box_second_reciprocal item.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes item
     ==>
     candle_cv_q_packed_object_state_sqrt
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_root)
       (candle_cv_q_interval center_first)
       (candle_cv_q_interval box_first)
       (candle_cv_q_interval box_second_reciprocal)
       (candle_cv_q_packed_object_item_state_encode item) =
     candle_cv_q_packed_object_item_state_encode
       (candle_q_packed_object_source_item_sqrt radii center_root
         center_first box_root box_first box_second_reciprocal item)`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `item:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_analytic_invariant_def;
     candle_q_packed_object_source_item_sqrt_def;
     candle_cv_q_packed_object_item_state_encode_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_sqrt_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_ITEM_STAGE sqrt";;

let candle_cv_q_packed_object_source_item_atn_correct = prove
 (`!radii center_boxes outer_boxes center_input center_result center_square
       center_first box_input box_square box_first box_first_square item.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes item
     ==>
     candle_cv_q_packed_object_state_atn
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_result)
       (candle_cv_q_interval center_first)
       (candle_cv_q_interval box_first)
       (candle_cv_q_interval box_first_square)
       (candle_cv_q_packed_object_item_state_encode item) =
     candle_cv_q_packed_object_item_state_encode
       (candle_q_packed_object_source_item_atn radii center_input
         center_result center_square center_first box_input box_square
         box_first box_first_square item)`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `item:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_analytic_invariant_def;
     candle_q_packed_object_source_item_atn_def;
     candle_cv_q_packed_object_item_state_encode_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_atn_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_ITEM_STAGE atn";;

let candle_cv_q_packed_object_pi_half_state_def = new_definition
 `candle_cv_q_packed_object_pi_half_state =
    candle_cv_q_packed_object_state_encode
      (Candle_q_packed_object_state T
        candle_q_packed_object_pi_half_scale40_interval
        candle_q_packed_object_zero_gradient6
        candle_q_packed_object_pi_half_scale40_interval
        candle_q_packed_object_zero_gradient6
        candle_q_packed_object_zero_hessian21)`;;

let candle_cv_q_packed_object_pi_half_state_correct = prove
 (`candle_cv_q_packed_object_pi_half_state =
     candle_cv_q_packed_object_item_state_encode
       candle_q_packed_object_source_item_pi_half`,
  REWRITE_TAC
    [candle_cv_q_packed_object_pi_half_state_def;
     candle_q_packed_object_source_item_pi_half_def;
     candle_cv_q_packed_object_item_state_encode_def]);;

let _ = print_endline "CANDLE_OBJECT_ITEM_STAGE pi-half";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_source_item_neg_correct;
     candle_cv_q_packed_object_source_item_add_correct;
     candle_cv_q_packed_object_source_item_mul_correct;
     candle_cv_q_packed_object_item_center_value_correct;
     candle_cv_q_packed_object_item_value_bound_correct;
     candle_cv_q_packed_object_source_item_inverse_correct;
     candle_cv_q_packed_object_source_item_sqrt_correct;
     candle_cv_q_packed_object_source_item_atn_correct;
     candle_cv_q_packed_object_pi_half_state_correct] then
  failwith "packed object item compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_ITEM_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
