(* ========================================================================== *)
(* Success reflection for ordinary exact-object source instructions.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the converse of the ordinary forward  *)
(* executor theorem: authenticated source identity plus an executable success *)
(* must determine a logical ordinary successor.  The proof is generic in the *)
(* source expression and is not a reconstruction of a case-16594 trace.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_poly_compile_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_ordinary_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_complete_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_ordinary_success_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_poly_compute;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_compute;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_compute;;
open Candle_cv_analytic_expr_packed_source_object_poly_compile_sound;;

let candle_cv_q_packed_object_certificate_success_state = prove
 (`!stack certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_certificate_state T stack certificates)`,
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_success_def;
     candle_cv_q_packed_object_certificate_state_def;
     candle_cv_bool_def; cexp_fst_def] THEN
  REWRITE_TAC[injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN TRY ARITH_TAC);;

let candle_cv_q_packed_object_certificate_success_failure = prove
 (`!stack certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_certificate_failure stack certificates)`,
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_success_def;
     candle_cv_q_packed_object_certificate_failure_def;
     candle_cv_q_packed_object_certificate_state_def;
     candle_cv_bool_def; cexp_fst_def; injectivity "cval"] THEN
  REWRITE_TAC[injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN TRY ARITH_TAC);;

let candle_q_packed_object_ordinary_poly_exists = prove
 (`!center_boxes outer_boxes radii polynomial certificates stack.
     candle_poly_valid_dim 6 polynomial
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii (Candle_analytic_push_poly (candle_poly_compile polynomial))
         certificates stack next certificate_rest`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`polynomial:candle_poly_expr`;
       `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
       `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
       `radii:((num#num)#num)list`;
       `[]:(candle_q_packed_object_item)list`]
      candle_q_packed_object_poly_compile_run_exists) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `result:candle_q_packed_object_item`
      (LABEL_TAC "poly_run")) THEN
  EXISTS_TAC
    `(CONS result stack):(candle_q_packed_object_item)list` THEN
  EXISTS_TAC
    `certificates:(((num#num)#num)#((num#num)#num))list` THEN
  REWRITE_TAC[candle_q_packed_object_source_ordinary_step_def] THEN
  DISJ1_TAC THEN
  EXISTS_TAC `candle_poly_compile polynomial` THEN
  EXISTS_TAC `result:candle_q_packed_object_item` THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_ordinary_neg_cons_exists = prove
 (`!center_boxes outer_boxes radii certificates item rest.
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_neg certificates (CONS item rest)
         next certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_ordinary_step_def;
              candle_q_packed_object_source_nonpoly_step_def;
              distinctness "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_q_packed_object_ordinary_add_cons_exists = prove
 (`!center_boxes outer_boxes radii certificates right left rest.
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_add certificates
         (CONS right (CONS left rest)) next certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_ordinary_step_def;
              candle_q_packed_object_source_nonpoly_step_def;
              distinctness "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_q_packed_object_ordinary_mul_cons_exists = prove
 (`!center_boxes outer_boxes radii certificates right left rest.
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_mul certificates
         (CONS right (CONS left rest)) next certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_ordinary_step_def;
              candle_q_packed_object_source_nonpoly_step_def;
              distinctness "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_q_packed_object_ordinary_square_cons_exists = prove
 (`!center_boxes outer_boxes radii certificates item rest.
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_square certificates (CONS item rest)
         next certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_ordinary_step_def;
              candle_q_packed_object_source_nonpoly_step_def;
              distinctness "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_q_packed_object_ordinary_pi_half_exists = prove
 (`!center_boxes outer_boxes radii certificates stack.
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_pi_half certificates stack next
         certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_ordinary_step_def;
              candle_q_packed_object_source_nonpoly_step_def;
              distinctness "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_object_zero_not_one = ARITH_RULE `~(0 = 1)`;;

let candle_cv_q_packed_object_ordinary_neg_empty = prove
 (`!center_boxes outer_boxes radii certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_neg)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_step_def;
     candle_cv_q_packed_object_nonpoly_step_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_packed_object_poly_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_packed_object_execution_failure_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_from_execution_def;
     candle_cv_q_packed_source_certificate_success_def;
     candle_cv_q_packed_object_certificate_state_def; candle_cv_bool_def;
     cexp_ispair_def; cexp_eq_def; cexp_if_def; cexp_fst_def;
     injectivity "cval"; NOT_SUC;
     candle_cv_q_packed_object_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC
    [cexp_if_def; cexp_fst_def; cexp_snd_def; cexp_ispair_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_state_def;
     candle_cv_q_packed_source_certificate_success_def; candle_cv_bool_def] THEN
  REWRITE_TAC
    [injectivity "cval"; NOT_SUC; candle_object_zero_not_one]);;

let candle_cv_q_packed_object_ordinary_add_empty = prove
 (`!center_boxes outer_boxes radii certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_add)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_step_def;
     candle_cv_q_packed_object_nonpoly_step_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_packed_object_poly_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_packed_object_execution_failure_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_from_execution_def;
     candle_cv_q_packed_source_certificate_success_def;
     candle_cv_q_packed_object_certificate_state_def; candle_cv_bool_def;
     cexp_ispair_def; cexp_eq_def; cexp_if_def; cexp_fst_def;
     injectivity "cval"; NOT_SUC;
     candle_cv_q_packed_object_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC
    [cexp_if_def; cexp_fst_def; cexp_snd_def; cexp_ispair_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_state_def;
     candle_cv_q_packed_source_certificate_success_def; candle_cv_bool_def] THEN
  REWRITE_TAC
    [injectivity "cval"; NOT_SUC; candle_object_zero_not_one]);;

let candle_cv_q_packed_object_ordinary_add_singleton = prove
 (`!center_boxes outer_boxes radii certificates item.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_add)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode [item]))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_step_def;
     candle_cv_q_packed_object_nonpoly_step_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_packed_object_poly_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_packed_object_execution_failure_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_from_execution_def;
     candle_cv_q_packed_source_certificate_success_def;
     candle_cv_q_packed_object_certificate_state_def; candle_cv_bool_def;
     cexp_ispair_def; cexp_eq_def; cexp_if_def; cexp_fst_def; cexp_snd_def;
     injectivity "cval"; NOT_SUC;
     candle_cv_q_packed_object_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC
    [cexp_if_def; cexp_fst_def; cexp_snd_def; cexp_ispair_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_state_def;
     candle_cv_q_packed_source_certificate_success_def; candle_cv_bool_def] THEN
  REWRITE_TAC
    [injectivity "cval"; NOT_SUC; candle_object_zero_not_one]);;

let candle_cv_q_packed_object_ordinary_mul_empty = prove
 (`!center_boxes outer_boxes radii certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_mul)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_step_def;
     candle_cv_q_packed_object_nonpoly_step_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_packed_object_poly_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_packed_object_execution_failure_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_from_execution_def;
     candle_cv_q_packed_source_certificate_success_def;
     candle_cv_q_packed_object_certificate_state_def; candle_cv_bool_def;
     cexp_ispair_def; cexp_eq_def; cexp_if_def; cexp_fst_def;
     injectivity "cval"; NOT_SUC;
     candle_cv_q_packed_object_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC
    [cexp_if_def; cexp_fst_def; cexp_snd_def; cexp_ispair_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_state_def;
     candle_cv_q_packed_source_certificate_success_def; candle_cv_bool_def] THEN
  REWRITE_TAC
    [injectivity "cval"; NOT_SUC; candle_object_zero_not_one]);;

let candle_cv_q_packed_object_ordinary_mul_singleton = prove
 (`!center_boxes outer_boxes radii certificates item.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_mul)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode [item]))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_step_def;
     candle_cv_q_packed_object_nonpoly_step_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_packed_object_poly_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_packed_object_execution_failure_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_from_execution_def;
     candle_cv_q_packed_source_certificate_success_def;
     candle_cv_q_packed_object_certificate_state_def; candle_cv_bool_def;
     cexp_ispair_def; cexp_eq_def; cexp_if_def; cexp_fst_def; cexp_snd_def;
     injectivity "cval"; NOT_SUC;
     candle_cv_q_packed_object_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC
    [cexp_if_def; cexp_fst_def; cexp_snd_def; cexp_ispair_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_state_def;
     candle_cv_q_packed_source_certificate_success_def; candle_cv_bool_def] THEN
  REWRITE_TAC
    [injectivity "cval"; NOT_SUC; candle_object_zero_not_one]);;

let candle_cv_q_packed_object_ordinary_square_empty = prove
 (`!center_boxes outer_boxes radii certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_square)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_step_def;
     candle_cv_q_packed_object_nonpoly_step_def;
     candle_cv_analytic_instruction_def;
     candle_cv_q_packed_object_poly_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_packed_object_execution_failure_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_from_execution_def;
     candle_cv_q_packed_source_certificate_success_def;
     candle_cv_q_packed_object_certificate_state_def; candle_cv_bool_def;
     cexp_ispair_def; cexp_eq_def; cexp_if_def; cexp_fst_def;
     injectivity "cval"; NOT_SUC;
     candle_cv_q_packed_object_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC
    [cexp_if_def; cexp_fst_def; cexp_snd_def; cexp_ispair_def;
     candle_cv_q_packed_object_execution_state_def;
     candle_cv_q_packed_object_certificate_state_def;
     candle_cv_q_packed_source_certificate_success_def; candle_cv_bool_def] THEN
  REWRITE_TAC
    [injectivity "cval"; NOT_SUC; candle_object_zero_not_one]);;

let candle_cv_q_packed_object_ordinary_neg_sound = prove
 (`!stack center_boxes outer_boxes radii certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_neg)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_neg certificates stack next
         certificate_rest`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_object_ordinary_neg_empty];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN
    MATCH_ACCEPT_TAC candle_q_packed_object_ordinary_neg_cons_exists]);;

let candle_cv_q_packed_object_ordinary_add_sound = prove
 (`!stack center_boxes outer_boxes radii certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_add)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_add certificates stack next
         certificate_rest`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_object_ordinary_add_empty];
    X_GEN_TAC `right:candle_q_packed_object_item` THEN
    X_GEN_TAC `tail:(candle_q_packed_object_item)list` THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (ISPEC `tail:(candle_q_packed_object_item)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `left:candle_q_packed_object_item`
          (X_CHOOSE_THEN `rest:(candle_q_packed_object_item)list`
            SUBST_ALL_TAC))) THENL
     [ASM_MESON_TAC[candle_cv_q_packed_object_ordinary_add_singleton];
      MATCH_ACCEPT_TAC candle_q_packed_object_ordinary_add_cons_exists]]);;

let candle_cv_q_packed_object_ordinary_mul_sound = prove
 (`!stack center_boxes outer_boxes radii certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_mul)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_mul certificates stack next
         certificate_rest`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_object_ordinary_mul_empty];
    X_GEN_TAC `right:candle_q_packed_object_item` THEN
    X_GEN_TAC `tail:(candle_q_packed_object_item)list` THEN
    DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (ISPEC `tail:(candle_q_packed_object_item)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `left:candle_q_packed_object_item`
          (X_CHOOSE_THEN `rest:(candle_q_packed_object_item)list`
            SUBST_ALL_TAC))) THENL
     [ASM_MESON_TAC[candle_cv_q_packed_object_ordinary_mul_singleton];
      MATCH_ACCEPT_TAC candle_q_packed_object_ordinary_mul_cons_exists]]);;

let candle_cv_q_packed_object_ordinary_square_sound = prove
 (`!stack center_boxes outer_boxes radii certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_square)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_square certificates stack next
         certificate_rest`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_object_ordinary_square_empty];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN
    MATCH_ACCEPT_TAC candle_q_packed_object_ordinary_square_cons_exists]);;


if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_certificate_success_state;
     candle_cv_q_packed_object_certificate_success_failure;
     candle_q_packed_object_ordinary_poly_exists;
     candle_q_packed_object_ordinary_neg_cons_exists;
     candle_q_packed_object_ordinary_add_cons_exists;
     candle_q_packed_object_ordinary_mul_cons_exists;
     candle_q_packed_object_ordinary_square_cons_exists;
     candle_q_packed_object_ordinary_pi_half_exists;
     candle_cv_q_packed_object_ordinary_neg_empty;
     candle_cv_q_packed_object_ordinary_add_empty;
     candle_cv_q_packed_object_ordinary_add_singleton;
     candle_cv_q_packed_object_ordinary_mul_empty;
     candle_cv_q_packed_object_ordinary_mul_singleton;
     candle_cv_q_packed_object_ordinary_square_empty;
     candle_cv_q_packed_object_ordinary_neg_sound;
     candle_cv_q_packed_object_ordinary_add_sound;
     candle_cv_q_packed_object_ordinary_mul_sound;
     candle_cv_q_packed_object_ordinary_square_sound] then
  failwith "packed object ordinary simple success sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_ORDINARY_SUCCESS_SIMPLE_OK DEVELOPMENT_NON_RELEASE";;

end;;
