(* ========================================================================== *)
(* One-step semantic preservation for the packed analytic source replay.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This relation is the ordinary-HOL boundary  *)
(* consumed by program induction.  It records the exact rational evidence   *)
(* needed by each successful packed instruction, while keeping certificate  *)
(* preparation and fixed-word execution outside the trusted semantics.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_certified_inverse_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certified_sqrt_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certified_atn_sound.ml";;

module Candle_cv_analytic_expr_packed_source_step_sound = struct

open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_packed_source_item_invariant;;
open Candle_cv_analytic_expr_packed_source_item_operations_sound;;
open Candle_cv_analytic_expr_packed_source_certified_inverse_sound;;
open Candle_cv_analytic_expr_packed_source_certified_sqrt_sound;;
open Candle_cv_analytic_expr_packed_source_certified_atn_sound;;

let candle_q_packed_source_stack_analytic_invariant_def = define
 `(candle_q_packed_source_stack_analytic_invariant boxes [] <=> T) /\
  (candle_q_packed_source_stack_analytic_invariant boxes (CONS item rest) <=>
     candle_q_packed_source_item_analytic_invariant boxes item /\
     candle_q_packed_source_stack_analytic_invariant boxes rest)`;;

(* The relation deliberately has no matan branch: the authenticated packed *)
(* source language does not implement that constructor and therefore fails  *)
(* closed if one occurs.                                                     *)

let candle_q_packed_source_step_def = new_definition
 `candle_q_packed_source_step boxes source stack next <=>
    (?polynomial.
       candle_poly_valid_dim 6 polynomial /\
       source =
         Candle_analytic_push_poly (candle_poly_compile polynomial) /\
       next =
         CONS (candle_q_packed_source_poly_item boxes polynomial) stack) \/
    (?result expression.
       candle_q_packed_delta_specialized_source_result
         boxes source result expression /\
       next =
         CONS
           (candle_q_packed_source_item_make
             result expression expression) stack) \/
    (?item rest.
       source = Candle_analytic_program_neg /\
       stack = CONS item rest /\
       next = CONS (candle_q_packed_source_item_neg boxes item) rest) \/
    (?right left rest.
       source = Candle_analytic_program_add /\
       stack = CONS right (CONS left rest) /\
       next =
         CONS (candle_q_packed_source_item_add boxes left right) rest) \/
    (?right left rest.
       source = Candle_analytic_program_mul /\
       stack = CONS right (CONS left rest) /\
       next =
         CONS (candle_q_packed_source_item_mul boxes left right) rest) \/
    (?item rest.
       source = Candle_analytic_program_square /\
       stack = CONS item rest /\
       next = CONS (candle_q_packed_source_item_square boxes item) rest) \/
    (?item rest center_reciprocal box_reciprocal.
       source = Candle_analytic_program_inv /\
       stack = CONS item rest /\
       candle_q_interval_inv_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_result_center
             (candle_q_packed_source_item_result item)))
         center_reciprocal /\
       candle_q_interval_inv_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_proxy
             (candle_q_packed_source_item_result item)))
         box_reciprocal /\
       next =
         CONS
           (candle_q_packed_source_item_inv_certified boxes
             center_reciprocal box_reciprocal item) rest) \/
    (?source_sqrt item rest center_root box_root center_derivative
        box_derivative box_second_reciprocal.
       source = Candle_analytic_program_sqrt source_sqrt /\
       stack = CONS item rest /\
       candle_q_interval_sqrt_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_result_center
             (candle_q_packed_source_item_result item))) center_root /\
       candle_q_interval_inv_certificate
         (candle_q_interval_add_normalized center_root center_root)
         center_derivative /\
       candle_q_dim_jet_sqrt_certificates
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_proxy
             (candle_q_packed_source_item_result item)))
         box_root box_derivative box_second_reciprocal /\
       next =
         CONS
           (candle_q_packed_source_item_sqrt_certified boxes
             center_root box_root center_derivative box_derivative
             box_second_reciprocal item) rest) \/
    (?item rest center_input box_input center_result center_square
        center_derivative box_square box_derivative box_derivative_square.
       source = Candle_analytic_program_atn /\
       stack = CONS item rest /\
       candle_q_interval_atn_outer_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_result_center
             (candle_q_packed_source_item_result item)))
         center_input center_result /\
       candle_q_interval_square_outer_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_result_center
             (candle_q_packed_source_item_result item)))
         center_input center_square /\
       candle_q_interval_inv_certificate
         (candle_q_dim_jet_atn_denominator_with_square center_square)
         center_derivative /\
       candle_q_interval_square_outer_certificate
         (candle_q_dim_jet_f
           (candle_q_dim_taylor_model_proxy
             (candle_q_packed_source_item_result item)))
         box_input box_square /\
       candle_q_interval_inv_certificate
         (candle_q_dim_jet_atn_denominator_with_square box_square)
         box_derivative /\
       candle_q_interval_square_outer_certificate
         box_derivative box_derivative box_derivative_square /\
       next =
         CONS
           (candle_q_packed_source_item_atn_faithful boxes
             center_input box_input center_result center_square
             center_derivative box_square box_derivative
             box_derivative_square item) rest) \/
    (source = Candle_analytic_program_pi_half /\
     next = CONS (candle_q_packed_source_pi_half_item boxes) stack)`;;

let candle_q_packed_source_step_analytic_invariant = prove
 (`!boxes source stack next.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_stack_analytic_invariant boxes stack /\
     candle_q_packed_source_step boxes source stack next
     ==>
     candle_q_packed_source_stack_analytic_invariant boxes next`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "stack_invariant")
          (LABEL_TAC "step")))) THEN
  USE_THEN "step" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[candle_q_packed_source_stack_analytic_invariant_def] THEN
    MATCH_MP_TAC candle_q_packed_source_poly_item_analytic_invariant THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[candle_q_packed_source_stack_analytic_invariant_def] THEN
    ASM_MESON_TAC
      [candle_q_packed_delta_specialized_source_item_analytic_invariant];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC[candle_q_packed_source_stack_analytic_invariant_def] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_packed_source_item_neg_analytic_invariant THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC[candle_q_packed_source_stack_analytic_invariant_def] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_packed_source_item_add_analytic_invariant THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC[candle_q_packed_source_stack_analytic_invariant_def] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_packed_source_item_mul_analytic_invariant THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC[candle_q_packed_source_stack_analytic_invariant_def] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_packed_source_item_square_analytic_invariant THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC[candle_q_packed_source_stack_analytic_invariant_def] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_packed_source_item_inv_certified_analytic_invariant THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC[candle_q_packed_source_stack_analytic_invariant_def] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
        candle_q_packed_source_item_sqrt_certified_analytic_invariant THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC[candle_q_packed_source_stack_analytic_invariant_def] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
        candle_q_packed_source_item_atn_faithful_analytic_invariant THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[candle_q_packed_source_stack_analytic_invariant_def] THEN
    MATCH_MP_TAC candle_q_packed_source_pi_half_item_analytic_invariant THEN
    ASM_REWRITE_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_source_step_analytic_invariant] then
  failwith "packed source step sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_STEP_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
