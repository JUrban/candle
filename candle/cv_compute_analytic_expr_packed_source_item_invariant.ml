(* ========================================================================== *)
(* Semantic stack items for the packed analytic source checker.              *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A logical item records the exact rational    *)
(* Taylor result together with the center and whole-box expressions that it  *)
(* denotes.  This is deliberately independent of the executable stack       *)
(* encoding: later refinement theorems may relate either an ordinary source  *)
(* step or an authenticated delta shortcut to the same semantic item.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_specialization_sound.ml";;

module Candle_cv_analytic_expr_packed_source_item_invariant = struct

open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_nonlinear_sound;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_analytic_expr_packed_source_delta_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_specialization_sound;;

let candle_q_packed_source_item_make_def = new_definition
 `candle_q_packed_source_item_make result center_e box_e =
    (result,(center_e,box_e))`;;

let candle_q_packed_source_item_result_def = new_definition
 `candle_q_packed_source_item_result item = FST item`;;

let candle_q_packed_source_item_center_expr_def = new_definition
 `candle_q_packed_source_item_center_expr item = FST (SND item)`;;

let candle_q_packed_source_item_box_expr_def = new_definition
 `candle_q_packed_source_item_box_expr item = SND (SND item)`;;

let candle_q_packed_source_item_analytic_invariant_def = new_definition
 `candle_q_packed_source_item_analytic_invariant boxes item <=>
    candle_analytic_valid_dim 6
      (candle_q_packed_source_item_box_expr item) /\
    candle_analytic_erase_sqrt_certificates
      (candle_q_packed_source_item_center_expr item) =
      candle_analytic_erase_sqrt_certificates
        (candle_q_packed_source_item_box_expr item) /\
    candle_q_dim_taylor_model_result_analytic_invariant
      (ARB:real^6) boxes
      (candle_q_packed_source_item_result item)
      (candle_q_packed_source_item_center_expr item)
      (candle_q_packed_source_item_box_expr item)`;;

let candle_q_packed_delta_specialized_source_result_valid = prove
 (`!boxes source result expression.
     candle_q_packed_delta_specialized_source_result
       boxes source result expression
     ==>
     candle_analytic_valid_dim 6 expression /\
     candle_analytic_compile expression = [source]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_specialized_source_result_def] THEN
  DISCH_THEN
    (DISJ_CASES_THEN
      (X_CHOOSE_THEN `coordinate:num` STRIP_ASSUME_TAC)) THENL
   [RULE_ASSUM_TAC
      (REWRITE_RULE
        [candle_packed_delta_neg_derivative_source_instruction_def]) THEN
    ASM_REWRITE_TAC[candle_packed_delta_neg_derivative_expr_def;
                    candle_analytic_valid_dim_def;
                    candle_analytic_compile_def] THEN
    MATCH_MP_TAC candle_packed_delta_neg_derivative_poly_valid THEN
    ASM_ARITH_TAC;
    RULE_ASSUM_TAC
      (REWRITE_RULE
        [candle_packed_delta_product_source_instruction_def]) THEN
    ASM_REWRITE_TAC[candle_packed_delta_product_source_expr_def;
                    candle_packed_delta_product_source_poly_def;
                    candle_analytic_valid_dim_def;
                    candle_analytic_compile_def;
                    candle_poly_valid_dim_def;
                    candle_packed_delta_poly_valid] THEN
    ASM_ARITH_TAC]);;

let candle_q_packed_delta_specialized_source_item_analytic_invariant = prove
 (`!boxes source result expression.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_delta_specialized_source_result
       boxes source result expression
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_item_make result expression expression)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND] THEN
  ASM_MESON_TAC
   [candle_q_packed_delta_specialized_source_result_valid;
    candle_q_packed_delta_specialized_source_result_analytic_invariant]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_delta_specialized_source_result_valid;
     candle_q_packed_delta_specialized_source_item_analytic_invariant] then
  failwith "packed source item invariant: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_ITEM_INVARIANT_OK DEVELOPMENT_NON_RELEASE";;

end;;
