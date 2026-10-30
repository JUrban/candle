(* ========================================================================== *)
(* Converse soundness for planned certificate dispatch.                      *)
(*                                                                            *)
(* A successful executable dispatch is shown to be an exact logical planned  *)
(* certificate step.  In particular, success cannot be obtained from a short *)
(* nonlinear certificate stream or an unauthenticated specialization code.   *)
(* ========================================================================== *)

module Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_packed_source_item_invariant;;
open Candle_cv_analytic_expr_packed_source_item_operations_sound;;
open Candle_cv_analytic_expr_packed_source_delta_specialization_sound;;
open Candle_cv_analytic_expr_packed_source_step_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_program_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_step_compute;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_result_compute;;
open Candle_cv_analytic_expr_packed_source_delta_product_result_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_compute;;

let candle_cv_q_packed_source_certificate_success_def = new_definition
 `candle_cv_q_packed_source_certificate_success state <=>
    Cexp_fst state = Cexp_num 1`;;

let candle_cv_q_packed_source_certificate_success_state = prove
 (`!stack certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_state T stack certificates)`,
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_success_def;
    candle_cv_q_packed_source_certificate_state_def;
    candle_cv_bool_def; cexp_fst_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_source_certificate_success_failure = prove
 (`!stack certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_failure stack certificates)`,
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_success_def;
    candle_cv_q_packed_source_certificate_failure_def;
    candle_cv_q_packed_source_certificate_state_def;
    candle_cv_bool_def; cexp_fst_def; injectivity "cval"] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_source_certificate_success_if = prove
 (`!condition success_stack success_certificates
       failure_stack failure_certificates.
     candle_cv_q_packed_source_certificate_success
       (Cexp_if (candle_cv_bool condition)
         (candle_cv_q_packed_source_certificate_state T
           success_stack success_certificates)
         (candle_cv_q_packed_source_certificate_failure
           failure_stack failure_certificates)) <=>
     condition`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `condition:bool` THEN
  ASM_REWRITE_TAC
   [candle_cv_bool_def; cexp_if_def;
    candle_cv_q_packed_source_certificate_success_state;
    candle_cv_q_packed_source_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_source_ordinary_instruction_def = new_definition
 `candle_q_packed_source_ordinary_instruction source <=>
    (?polynomial. candle_poly_valid_dim 6 polynomial /\
      source = Candle_analytic_push_poly (candle_poly_compile polynomial)) \/
    source = Candle_analytic_program_neg \/
    source = Candle_analytic_program_add \/
    source = Candle_analytic_program_mul \/
    source = Candle_analytic_program_square \/
    source = Candle_analytic_program_inv \/
    (?source_sqrt. source = Candle_analytic_program_sqrt source_sqrt) \/
    source = Candle_analytic_program_atn \/
    source = Candle_analytic_program_pi_half`;;

let candle_q_packed_source_plan_instruction_def = new_definition
 `candle_q_packed_source_plan_instruction code source <=>
    (code = 0 /\ candle_q_packed_source_ordinary_instruction source) \/
    (?coordinate. code = SUC coordinate /\ coordinate < 3 /\
      candle_packed_delta_product_source_instruction coordinate source) \/
    (?coordinate. code = SUC coordinate /\
      (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5) /\
      candle_packed_delta_neg_derivative_source_instruction
        coordinate source)`;;

print_endline "CANDLE_V1899_DISPATCH_SOUNDNESS_CORE_OK";;

let candle_q_packed_source_ordinary_poly_exists = prove
 (`!boxes polynomial certificates stack.
     candle_poly_valid_dim 6 polynomial
     ==> ?next certificate_rest.
       candle_q_packed_source_ordinary_certificate_step
         boxes (Candle_analytic_push_poly (candle_poly_compile polynomial))
         certificates stack next certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def;
              candle_q_packed_source_ordinary_step_def;
              distinctness "candle_analytic_instruction";
              injectivity "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_cv_q_packed_source_certificate_ordinary_neg_empty = prove
 (`!boxes certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_neg)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    candle_cv_q_dim_taylor_model_result_list_encode_def;
    cexp_ispair_def; cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC;
    candle_cv_q_packed_source_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_source_ordinary_neg_cons = prove
 (`!boxes certificates item rest.
     ?next certificate_rest.
       candle_q_packed_source_ordinary_certificate_step
         boxes Candle_analytic_program_neg certificates
         (item::rest) next certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def;
              candle_q_packed_source_ordinary_step_def;
              distinctness "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_cv_q_packed_source_certificate_ordinary_neg_sound = prove
 (`!stack boxes certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_neg)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode
           (candle_q_packed_source_item_results stack)))
     ==> ?next certificate_rest.
       candle_q_packed_source_ordinary_certificate_step
         boxes Candle_analytic_program_neg certificates
         stack next certificate_rest`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_item_results_def; MAP] THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_neg_empty];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    MESON_TAC[candle_q_packed_source_ordinary_neg_cons]]);;

let candle_cv_q_packed_source_certificate_ordinary_add_empty = prove
 (`!boxes certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_add)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    candle_cv_q_dim_taylor_model_result_list_encode_def;
    cexp_ispair_def; cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def; cexp_fst_def; injectivity "cval";
              distinctness "cval";
              candle_cv_q_packed_source_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_source_certificate_ordinary_add_singleton = prove
 (`!boxes certificates item.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_add)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode
           [candle_q_packed_source_item_result item]))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    candle_cv_q_dim_taylor_model_result_list_encode_def;
    cexp_ispair_def; cexp_fst_def; cexp_snd_def;
    cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def; cexp_fst_def; injectivity "cval";
              distinctness "cval";
              candle_cv_q_packed_source_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_source_certificate_ordinary_add_tail_sound = prove
 (`!tail boxes certificates right.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_add)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode
           (candle_q_packed_source_item_results (right::tail))))
     ==> ?next certificate_rest.
       candle_q_packed_source_ordinary_certificate_step
         boxes Candle_analytic_program_add certificates
         (right::tail) next certificate_rest`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_item_results_cons;
                candle_q_packed_source_item_results_def; MAP] THEN
    MESON_TAC
      [candle_cv_q_packed_source_certificate_ordinary_add_singleton];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def;
                candle_q_packed_source_ordinary_step_def;
                distinctness "candle_analytic_instruction"] THEN
    MESON_TAC[]]);;

let candle_cv_q_packed_source_certificate_ordinary_add_sound = prove
 (`!stack boxes certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_add)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode
           (candle_q_packed_source_item_results stack)))
     ==> ?next certificate_rest.
       candle_q_packed_source_ordinary_certificate_step
         boxes Candle_analytic_program_add certificates
         stack next certificate_rest`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_item_results_def; MAP] THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_add_empty];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    MESON_TAC
      [candle_cv_q_packed_source_certificate_ordinary_add_tail_sound]]);;

print_endline "CANDLE_V1899_DISPATCH_SOUNDNESS_ADD_OK";;

let candle_cv_q_packed_source_certificate_ordinary_mul_empty = prove
 (`!boxes certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_mul)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    candle_cv_q_dim_taylor_model_result_list_encode_def;
    cexp_ispair_def; cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def; cexp_fst_def; injectivity "cval";
              distinctness "cval";
              candle_cv_q_packed_source_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_source_certificate_ordinary_mul_singleton = prove
 (`!boxes certificates item.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_mul)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode
           [candle_q_packed_source_item_result item]))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    candle_cv_q_dim_taylor_model_result_list_encode_def;
    cexp_ispair_def; cexp_fst_def; cexp_snd_def;
    cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def; cexp_fst_def; injectivity "cval";
              distinctness "cval";
              candle_cv_q_packed_source_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_source_certificate_ordinary_mul_tail_sound = prove
 (`!tail boxes certificates right.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_mul)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode
           (candle_q_packed_source_item_results (right::tail))))
     ==> ?next certificate_rest.
       candle_q_packed_source_ordinary_certificate_step
         boxes Candle_analytic_program_mul certificates
         (right::tail) next certificate_rest`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_item_results_cons;
                candle_q_packed_source_item_results_def; MAP] THEN
    MESON_TAC
      [candle_cv_q_packed_source_certificate_ordinary_mul_singleton];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def;
                candle_q_packed_source_ordinary_step_def;
                distinctness "candle_analytic_instruction"] THEN
    MESON_TAC[]]);;

let candle_cv_q_packed_source_certificate_ordinary_mul_sound = prove
 (`!stack boxes certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_mul)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode
           (candle_q_packed_source_item_results stack)))
     ==> ?next certificate_rest.
       candle_q_packed_source_ordinary_certificate_step
         boxes Candle_analytic_program_mul certificates
         stack next certificate_rest`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_item_results_def; MAP] THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_mul_empty];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    MESON_TAC
      [candle_cv_q_packed_source_certificate_ordinary_mul_tail_sound]]);;

let candle_cv_q_packed_source_certificate_ordinary_square_empty = prove
 (`!boxes certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_square)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    candle_cv_q_dim_taylor_model_result_list_encode_def;
    cexp_ispair_def; cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def; cexp_fst_def; injectivity "cval";
              distinctness "cval";
              candle_cv_q_packed_source_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_source_certificate_ordinary_square_sound = prove
 (`!stack boxes certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_source_certificate_ordinary_step
         (candle_cv_q_interval_list boxes)
         (candle_cv_analytic_instruction Candle_analytic_program_square)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_dim_taylor_model_result_list_encode
           (candle_q_packed_source_item_results stack)))
     ==> ?next certificate_rest.
       candle_q_packed_source_ordinary_certificate_step
         boxes Candle_analytic_program_square certificates
         stack next certificate_rest`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_item_results_def; MAP] THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_square_empty];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def;
                candle_q_packed_source_ordinary_step_def;
                distinctness "candle_analytic_instruction"] THEN
    MESON_TAC[]]);;

let candle_q_packed_source_ordinary_pi_half_exists = prove
 (`!boxes certificates stack.
     ?next certificate_rest.
       candle_q_packed_source_ordinary_certificate_step
         boxes Candle_analytic_program_pi_half certificates
         stack next certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def;
              candle_q_packed_source_ordinary_step_def;
              distinctness "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

print_endline "CANDLE_V1899_DISPATCH_SOUNDNESS_ALGEBRAIC_OK";;

let candle_cv_q_packed_source_certificate_ordinary_inv_select = prove
 (`!boxes certificates stack.
    candle_cv_q_packed_source_certificate_ordinary_step
      (candle_cv_q_interval_list boxes)
      (candle_cv_analytic_instruction Candle_analytic_program_inv)
      (candle_cv_q_interval_list certificates) stack =
    candle_cv_q_packed_source_certificate_inv_step
      (candle_cv_q_interval_list boxes)
      (candle_cv_q_interval_list certificates) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    cexp_ispair_def; cexp_fst_def; cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def]);;

let candle_cv_q_packed_source_certificate_ordinary_inv_shaped = prove
 (`!boxes item rest center_reciprocal box_reciprocal certificate_rest.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction Candle_analytic_program_inv)
        (candle_cv_q_interval_list
          (center_reciprocal::box_reciprocal::certificate_rest))
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest)))) <=>
    candle_q_interval_inv_certificate
      (candle_q_dim_jet_f
        (candle_q_dim_taylor_model_result_center
          (candle_q_packed_source_item_result item))) center_reciprocal /\
    candle_q_interval_inv_certificate
      (candle_q_dim_jet_f
        (candle_q_dim_taylor_model_proxy
          (candle_q_packed_source_item_result item))) box_reciprocal`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_inv_select;
    candle_q_packed_source_item_results_cons;
    candle_cv_q_packed_source_certificate_inv_step_encoded;
    candle_cv_q_packed_source_certificate_success_if]);;

let candle_q_packed_source_ordinary_inv_exists = prove
 (`!boxes item rest center_reciprocal box_reciprocal certificate_rest.
    candle_q_interval_inv_certificate
      (candle_q_dim_jet_f
        (candle_q_dim_taylor_model_result_center
          (candle_q_packed_source_item_result item))) center_reciprocal /\
    candle_q_interval_inv_certificate
      (candle_q_dim_jet_f
        (candle_q_dim_taylor_model_proxy
          (candle_q_packed_source_item_result item))) box_reciprocal
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        Candle_analytic_program_inv
        (center_reciprocal::box_reciprocal::certificate_rest)
        (item::rest) next remaining`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def;
              candle_q_packed_source_certificate_step_def;
              distinctness "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_cv_q_packed_source_certificate_ordinary_inv_empty_stack = prove
 (`!boxes certificates.
    ~candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction Candle_analytic_program_inv)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_inv_select;
              candle_cv_q_packed_source_certificate_inv_step_def;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              cexp_ispair_def; cexp_if_def;
              candle_cv_q_packed_source_certificate_success_failure]);;

let candle_cv_q_packed_source_certificate_ordinary_inv_empty_cert = prove
 (`!boxes item rest.
    ~candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction Candle_analytic_program_inv)
        (candle_cv_q_interval_list [])
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_inv_select;
              candle_cv_q_packed_source_certificate_inv_step_def;
              candle_q_packed_source_item_results_cons;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              candle_cv_q_interval_list_def;
              cexp_ispair_def; cexp_if_def;
              candle_cv_q_packed_source_certificate_success_failure]);;

let candle_cv_q_packed_source_certificate_ordinary_inv_single_cert = prove
 (`!boxes item rest center_reciprocal.
    ~candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction Candle_analytic_program_inv)
        (candle_cv_q_interval_list [center_reciprocal])
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_inv_select;
              candle_cv_q_packed_source_certificate_inv_step_def;
              candle_q_packed_source_item_results_cons;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              candle_cv_q_interval_list_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
              candle_cv_q_packed_source_certificate_success_failure]);;

let candle_cv_q_packed_source_certificate_ordinary_inv_tail_sound = prove
 (`!tail boxes item rest center_reciprocal.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction Candle_analytic_program_inv)
        (candle_cv_q_interval_list (center_reciprocal::tail))
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        Candle_analytic_program_inv (center_reciprocal::tail)
        (item::rest) next remaining`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC
      [candle_cv_q_packed_source_certificate_ordinary_inv_single_cert];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_inv_shaped] THEN
    MESON_TAC[candle_q_packed_source_ordinary_inv_exists]]);;

let candle_cv_q_packed_source_certificate_ordinary_inv_certs_sound = prove
 (`!certificates boxes item rest.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction Candle_analytic_program_inv)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        Candle_analytic_program_inv certificates
        (item::rest) next remaining`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC
      [candle_cv_q_packed_source_certificate_ordinary_inv_empty_cert];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    MESON_TAC
      [candle_cv_q_packed_source_certificate_ordinary_inv_tail_sound]]);;

let candle_cv_q_packed_source_certificate_ordinary_inv_sound = prove
 (`!stack boxes certificates.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction Candle_analytic_program_inv)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        Candle_analytic_program_inv certificates stack next remaining`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_item_results_def; MAP] THEN
    MESON_TAC
      [candle_cv_q_packed_source_certificate_ordinary_inv_empty_stack];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    MESON_TAC
      [candle_cv_q_packed_source_certificate_ordinary_inv_certs_sound]]);;

print_endline "CANDLE_V1899_DISPATCH_SOUNDNESS_INV_OK";;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_shaped = prove
 (`!boxes source_sqrt item rest center_root box_root center_derivative
      box_derivative box_second_reciprocal certificate_rest.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list
          (center_root::box_root::center_derivative::box_derivative::
           box_second_reciprocal::certificate_rest))
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest)))) <=>
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
      box_root box_derivative box_second_reciprocal`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_sqrt_select;
    candle_q_packed_source_item_results_cons;
    candle_cv_q_packed_source_certificate_sqrt_step_encoded;
    candle_cv_q_packed_source_certificate_success_if]);;

let candle_q_packed_source_ordinary_sqrt_exists = prove
 (`!boxes source_sqrt item rest center_root box_root center_derivative
      box_derivative box_second_reciprocal certificate_rest.
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
      box_root box_derivative box_second_reciprocal
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        (Candle_analytic_program_sqrt source_sqrt)
        (center_root::box_root::center_derivative::box_derivative::
         box_second_reciprocal::certificate_rest)
        (item::rest) next remaining`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def;
              candle_q_packed_source_certificate_step_def;
              distinctness "candle_analytic_instruction";
              injectivity "candle_analytic_instruction";
              candle_q_interval_not_all_neq] THEN
  MESON_TAC[]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_empty_stack = prove
 (`!boxes source_sqrt certificates.
    ~candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_select;
              candle_cv_q_packed_source_certificate_sqrt_step_def;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              cexp_ispair_def; cexp_if_def;
              candle_cv_q_packed_source_certificate_success_failure]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_cert0 = prove
 (`!boxes source_sqrt item rest.
    ~candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list [])
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_select;
              candle_cv_q_packed_source_certificate_sqrt_step_def;
              candle_q_packed_source_item_results_cons;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              candle_cv_q_interval_list_def;
              cexp_ispair_def; cexp_if_def;
              candle_cv_q_packed_source_certificate_success_failure]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_cert1 = prove
 (`!boxes source_sqrt item rest c1.
    ~candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list [c1])
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_select;
              candle_cv_q_packed_source_certificate_sqrt_step_def;
              candle_q_packed_source_item_results_cons;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              candle_cv_q_interval_list_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
              candle_cv_q_packed_source_certificate_success_failure]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_cert2 = prove
 (`!boxes source_sqrt item rest c1 c2.
    ~candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list [c1;c2])
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_select;
              candle_cv_q_packed_source_certificate_sqrt_step_def;
              candle_q_packed_source_item_results_cons;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              candle_cv_q_interval_list_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
              candle_cv_q_packed_source_certificate_success_failure]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_cert3 = prove
 (`!boxes source_sqrt item rest c1 c2 c3.
    ~candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list [c1;c2;c3])
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_select;
              candle_cv_q_packed_source_certificate_sqrt_step_def;
              candle_q_packed_source_item_results_cons;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              candle_cv_q_interval_list_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
              candle_cv_q_packed_source_certificate_success_failure]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_cert4 = prove
 (`!boxes source_sqrt item rest c1 c2 c3 c4.
    ~candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list [c1;c2;c3;c4])
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_select;
              candle_cv_q_packed_source_certificate_sqrt_step_def;
              candle_q_packed_source_item_results_cons;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              candle_cv_q_interval_list_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
              candle_cv_q_packed_source_certificate_success_failure]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_prefix4_sound = prove
 (`!tail boxes source_sqrt item rest c1 c2 c3 c4.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list (c1::c2::c3::c4::tail))
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        (Candle_analytic_program_sqrt source_sqrt)
        (c1::c2::c3::c4::tail) (item::rest) next remaining`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_cert4];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_shaped] THEN
    MESON_TAC[candle_q_packed_source_ordinary_sqrt_exists]]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_prefix3_sound = prove
 (`!tail boxes source_sqrt item rest c1 c2 c3.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list (c1::c2::c3::tail))
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        (Candle_analytic_program_sqrt source_sqrt)
        (c1::c2::c3::tail) (item::rest) next remaining`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_cert3];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_prefix4_sound]]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_prefix2_sound = prove
 (`!tail boxes source_sqrt item rest c1 c2.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list (c1::c2::tail))
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        (Candle_analytic_program_sqrt source_sqrt)
        (c1::c2::tail) (item::rest) next remaining`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_cert2];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_prefix3_sound]]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_prefix1_sound = prove
 (`!tail boxes source_sqrt item rest c1.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list (c1::tail))
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        (Candle_analytic_program_sqrt source_sqrt)
        (c1::tail) (item::rest) next remaining`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_cert1];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_prefix2_sound]]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_certs_sound = prove
 (`!certificates boxes source_sqrt item rest.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        (Candle_analytic_program_sqrt source_sqrt)
        certificates (item::rest) next remaining`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_cert0];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_prefix1_sound]]);;

let candle_cv_q_packed_source_certificate_ordinary_sqrt_sound = prove
 (`!stack boxes source_sqrt certificates.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction
          (Candle_analytic_program_sqrt source_sqrt))
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        (Candle_analytic_program_sqrt source_sqrt)
        certificates stack next remaining`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_item_results_def; MAP] THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_empty_stack];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_source_certificate_ordinary_sqrt_certs_sound]]);;

print_endline "CANDLE_V1899_DISPATCH_SOUNDNESS_SQRT_OK";;

let candle_cv_q_packed_source_certificate_ordinary_atn_select = prove
 (`!boxes certificates stack.
    candle_cv_q_packed_source_certificate_ordinary_step
      (candle_cv_q_interval_list boxes)
      (candle_cv_analytic_instruction Candle_analytic_program_atn)
      (candle_cv_q_interval_list certificates) stack =
    candle_cv_q_packed_source_certificate_atn_step
      (candle_cv_q_interval_list boxes)
      (candle_cv_q_interval_list certificates) stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_step_def;
    LET_DEF; LET_END_DEF; candle_cv_analytic_instruction_def;
    cexp_ispair_def; cexp_fst_def; cexp_eq_def; cexp_if_def;
    injectivity "cval"; distinctness "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def]);;

let candle_cv_q_packed_source_certificate_ordinary_atn_shaped = prove
 (`!boxes item rest center_input box_input center_result center_square
      center_derivative box_square box_derivative box_derivative_square
      certificate_rest.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction Candle_analytic_program_atn)
        (candle_cv_q_interval_list
          (center_input::box_input::center_result::center_square::
           center_derivative::box_square::box_derivative::
           box_derivative_square::certificate_rest))
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest)))) <=>
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
      box_derivative box_derivative box_derivative_square`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [candle_cv_q_packed_source_certificate_ordinary_atn_select;
    candle_q_packed_source_item_results_cons;
    candle_cv_q_packed_source_certificate_atn_step_encoded;
    candle_cv_q_packed_source_certificate_success_if]);;

let candle_q_packed_source_ordinary_atn_exists = prove
 (`!boxes item rest center_input box_input center_result center_square
      center_derivative box_square box_derivative box_derivative_square
      certificate_rest.
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
      box_derivative box_derivative box_derivative_square
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        Candle_analytic_program_atn
        (center_input::box_input::center_result::center_square::
         center_derivative::box_square::box_derivative::
         box_derivative_square::certificate_rest)
        (item::rest) next remaining`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_certificate_step_def;
              candle_q_packed_source_certificate_step_def;
              distinctness "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_cv_q_packed_source_certificate_ordinary_atn_empty_stack = prove
 (`!boxes certificates.
    ~candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction Candle_analytic_program_atn)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_ordinary_atn_select;
              candle_cv_q_packed_source_certificate_atn_step_def;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              cexp_ispair_def; cexp_if_def;
              candle_cv_q_packed_source_certificate_success_failure]);;

let candle_cv_q_packed_source_certificate_ordinary_atn_certificates_shape =
  prove
 (`!certificates boxes item rest.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction Candle_analytic_program_atn)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results (item::rest))))
    ==> ?c1 c2 c3 c4 c5 c6 c7 c8 certificate_rest.
          certificates = c1::c2::c3::c4::c5::c6::c7::c8::certificate_rest`,
  let atn_short_tac =
    ASM_REWRITE_TAC
     [candle_cv_q_packed_source_certificate_ordinary_atn_select;
      candle_cv_q_packed_source_certificate_atn_step_def;
      candle_q_packed_source_item_results_cons;
      candle_cv_q_dim_taylor_model_result_list_encode_def;
      candle_cv_q_interval_list_def;
      cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
      candle_cv_q_packed_source_certificate_success_failure] in
  GEN_TAC THEN
  DISJ_CASES_TAC
    (ISPEC `certificates:(((num#num)#num)#((num#num)#num))list`
      list_CASES) THENL
   [atn_short_tac;
    FIRST_X_ASSUM
      (X_CHOOSE_THEN `c1:(((num#num)#num)#((num#num)#num))`
        (X_CHOOSE_THEN
          `tail1:(((num#num)#num)#((num#num)#num))list`
          SUBST_ALL_TAC)) THEN
    DISJ_CASES_TAC
      (ISPEC `tail1:(((num#num)#num)#((num#num)#num))list`
        list_CASES) THENL
     [atn_short_tac;
      FIRST_X_ASSUM
        (X_CHOOSE_THEN `c2:(((num#num)#num)#((num#num)#num))`
          (X_CHOOSE_THEN
            `tail2:(((num#num)#num)#((num#num)#num))list`
            SUBST_ALL_TAC)) THEN
      DISJ_CASES_TAC
        (ISPEC `tail2:(((num#num)#num)#((num#num)#num))list`
          list_CASES) THENL
       [atn_short_tac;
        FIRST_X_ASSUM
          (X_CHOOSE_THEN `c3:(((num#num)#num)#((num#num)#num))`
            (X_CHOOSE_THEN
              `tail3:(((num#num)#num)#((num#num)#num))list`
              SUBST_ALL_TAC)) THEN
        DISJ_CASES_TAC
          (ISPEC `tail3:(((num#num)#num)#((num#num)#num))list`
            list_CASES) THENL
         [atn_short_tac;
          FIRST_X_ASSUM
            (X_CHOOSE_THEN `c4:(((num#num)#num)#((num#num)#num))`
              (X_CHOOSE_THEN
                `tail4:(((num#num)#num)#((num#num)#num))list`
                SUBST_ALL_TAC)) THEN
          DISJ_CASES_TAC
            (ISPEC `tail4:(((num#num)#num)#((num#num)#num))list`
              list_CASES) THENL
           [atn_short_tac;
            FIRST_X_ASSUM
              (X_CHOOSE_THEN `c5:(((num#num)#num)#((num#num)#num))`
                (X_CHOOSE_THEN
                  `tail5:(((num#num)#num)#((num#num)#num))list`
                  SUBST_ALL_TAC)) THEN
            DISJ_CASES_TAC
              (ISPEC `tail5:(((num#num)#num)#((num#num)#num))list`
                list_CASES) THENL
             [atn_short_tac;
              FIRST_X_ASSUM
                (X_CHOOSE_THEN `c6:(((num#num)#num)#((num#num)#num))`
                  (X_CHOOSE_THEN
                    `tail6:(((num#num)#num)#((num#num)#num))list`
                    SUBST_ALL_TAC)) THEN
              DISJ_CASES_TAC
                (ISPEC `tail6:(((num#num)#num)#((num#num)#num))list`
                  list_CASES) THENL
               [atn_short_tac;
                FIRST_X_ASSUM
                  (X_CHOOSE_THEN
                    `c7:(((num#num)#num)#((num#num)#num))`
                    (X_CHOOSE_THEN
                      `tail7:(((num#num)#num)#((num#num)#num))list`
                      SUBST_ALL_TAC)) THEN
                DISJ_CASES_TAC
                  (ISPEC
                    `tail7:(((num#num)#num)#((num#num)#num))list`
                    list_CASES) THENL
                 [atn_short_tac;
                  FIRST_X_ASSUM
                    (X_CHOOSE_THEN
                      `c8:(((num#num)#num)#((num#num)#num))`
                      (X_CHOOSE_THEN
                        `certificate_rest:
                          (((num#num)#num)#((num#num)#num))list`
                        SUBST_ALL_TAC)) THEN
                  REPEAT GEN_TAC THEN DISCH_TAC THEN
                  MAP_EVERY EXISTS_TAC
                   [`c1:(((num#num)#num)#((num#num)#num))`;
                    `c2:(((num#num)#num)#((num#num)#num))`;
                    `c3:(((num#num)#num)#((num#num)#num))`;
                    `c4:(((num#num)#num)#((num#num)#num))`;
                    `c5:(((num#num)#num)#((num#num)#num))`;
                    `c6:(((num#num)#num)#((num#num)#num))`;
                    `c7:(((num#num)#num)#((num#num)#num))`;
                    `c8:(((num#num)#num)#((num#num)#num))`;
                    `certificate_rest:
                      (((num#num)#num)#((num#num)#num))list`] THEN
                  REFL_TAC]]]]]]]]);;

let candle_cv_q_packed_source_certificate_ordinary_atn_sound = prove
 (`!stack boxes certificates.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction Candle_analytic_program_atn)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step boxes
        Candle_analytic_program_atn certificates stack next remaining`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_item_results_def; MAP] THEN
    MESON_TAC
      [candle_cv_q_packed_source_certificate_ordinary_atn_empty_stack];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN (LABEL_TAC "success") THEN
    USE_THEN "success"
      (MP_TAC o MATCH_MP
        candle_cv_q_packed_source_certificate_ordinary_atn_certificates_shape)
      THEN
    DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    USE_THEN "success" MP_TAC THEN
    REWRITE_TAC
      [candle_cv_q_packed_source_certificate_ordinary_atn_shaped] THEN
    MESON_TAC[candle_q_packed_source_ordinary_atn_exists]]);;

print_endline "CANDLE_V1899_DISPATCH_SOUNDNESS_ATN_OK";;

let candle_cv_q_packed_source_certificate_ordinary_instruction_sound = prove
 (`!boxes source certificates stack.
    candle_q_packed_source_ordinary_instruction source /\
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_ordinary_step
        (candle_cv_q_interval_list boxes)
        (candle_cv_analytic_instruction source)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?next remaining.
      candle_q_packed_source_ordinary_certificate_step
        boxes source certificates stack next remaining`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_instruction_def] THEN
  MESON_TAC
   [candle_q_packed_source_ordinary_poly_exists;
    candle_cv_q_packed_source_certificate_ordinary_neg_sound;
    candle_cv_q_packed_source_certificate_ordinary_add_sound;
    candle_cv_q_packed_source_certificate_ordinary_mul_sound;
    candle_cv_q_packed_source_certificate_ordinary_square_sound;
    candle_cv_q_packed_source_certificate_ordinary_inv_sound;
    candle_cv_q_packed_source_certificate_ordinary_sqrt_sound;
    candle_cv_q_packed_source_certificate_ordinary_atn_sound;
    candle_q_packed_source_ordinary_pi_half_exists]);;

let candle_q_packed_source_specialized_plan_exists = prove
 (`!boxes code source certificates stack.
    candle_q_packed_source_plan_instruction code source /\ ~(code = 0)
    ==> ?next remaining.
      candle_q_packed_source_planned_certificate_step
        boxes code source certificates stack next remaining`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_plan_instruction_def;
              candle_q_packed_source_planned_certificate_step_def] THEN
  MESON_TAC[]);;

let candle_cv_q_packed_source_certificate_dispatch_zero_sound = prove
 (`!boxes source certificates stack.
    candle_q_packed_source_plan_instruction 0 source /\
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_step
        (candle_cv_q_interval_list boxes) (Cexp_num 0)
        (candle_cv_analytic_instruction source)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?next remaining.
      candle_q_packed_source_planned_certificate_step
        boxes 0 source certificates stack next remaining`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_plan_instruction_def;
              candle_cv_q_packed_source_certificate_dispatch_step_def;
              candle_q_packed_source_planned_certificate_step_def;
              cexp_eq_def; cexp_if_def; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MESON_TAC
    [candle_cv_q_packed_source_certificate_ordinary_instruction_sound]);;

let candle_cv_q_packed_source_certificate_dispatch_success_planned = prove
 (`!boxes code source certificates stack.
    candle_q_packed_source_plan_instruction code source /\
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_step
        (candle_cv_q_interval_list boxes) (Cexp_num code)
        (candle_cv_analytic_instruction source)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?next remaining.
      candle_q_packed_source_planned_certificate_step
        boxes code source certificates stack next remaining`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `code = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC
      candle_cv_q_packed_source_certificate_dispatch_zero_sound THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_packed_source_specialized_plan_exists THEN
    ASM_REWRITE_TAC[]]);;

let candle_exists_pair_strengthen = prove
 (`((?x:A y:B. P x y) /\ (!x y. P x y ==> Q x y))
    ==> ?x y. P x y /\ Q x y`,
  MESON_TAC[]);;

let candle_cv_q_packed_source_certificate_dispatch_success_exact = prove
 (`!boxes code source certificates stack.
    candle_q_packed_source_plan_instruction code source /\
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_step
        (candle_cv_q_interval_list boxes) (Cexp_num code)
        (candle_cv_analytic_instruction source)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?next remaining.
      candle_q_packed_source_planned_certificate_step
        boxes code source certificates stack next remaining /\
      candle_cv_q_packed_source_certificate_dispatch_step
        (candle_cv_q_interval_list boxes) (Cexp_num code)
        (candle_cv_analytic_instruction source)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)) =
      candle_cv_q_packed_source_certificate_state T
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results next))
        (candle_cv_q_interval_list remaining)`,
  REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "input") THEN
  MATCH_MP_TAC candle_exists_pair_strengthen THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
      candle_cv_q_packed_source_certificate_dispatch_success_planned THEN
    USE_THEN "input" ACCEPT_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC
      candle_cv_q_packed_source_certificate_dispatch_planned_correct THEN
    ASM_REWRITE_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_source_certificate_success_state;
     candle_cv_q_packed_source_certificate_success_failure;
     candle_cv_q_packed_source_certificate_success_if;
     candle_q_packed_source_ordinary_poly_exists;
     candle_cv_q_packed_source_certificate_ordinary_neg_sound;
     candle_cv_q_packed_source_certificate_ordinary_add_sound;
     candle_cv_q_packed_source_certificate_ordinary_mul_sound;
     candle_cv_q_packed_source_certificate_ordinary_square_sound;
     candle_q_packed_source_ordinary_pi_half_exists;
     candle_cv_q_packed_source_certificate_ordinary_inv_sound;
     candle_cv_q_packed_source_certificate_ordinary_sqrt_sound;
     candle_cv_q_packed_source_certificate_ordinary_atn_sound;
     candle_cv_q_packed_source_certificate_ordinary_instruction_sound;
     candle_q_packed_source_specialized_plan_exists;
     candle_cv_q_packed_source_certificate_dispatch_zero_sound;
     candle_cv_q_packed_source_certificate_dispatch_success_planned;
     candle_cv_q_packed_source_certificate_dispatch_success_exact] then
  failwith "packed source certificate dispatch sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFICATE_DISPATCH_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
