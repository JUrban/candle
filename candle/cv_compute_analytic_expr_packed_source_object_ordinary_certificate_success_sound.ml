(* ========================================================================== *)
(* Success reflection for certificate-consuming exact-object source steps.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  These converse theorems recover the exact     *)
(* logical inverse, square-root, and arctangent certificate predicates from   *)
(* executable success.  They therefore close the fail-closed ordinary bridge *)
(* without replaying a second numerical checker.                              *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_ordinary_success_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_ordinary_certificate_success_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_analytic_expr_packed_source_certificate_core;;
open Candle_cv_analytic_expr_packed_source_certified_atn_sound;;
open Candle_cv_exact_interval_sqrt_certificate;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_compute;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_compute;;
open Candle_cv_analytic_expr_packed_source_object_item_compute;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_success_sound;;

let candle_cv_q_packed_object_certificate_success_if = prove
 (`!condition success_stack success_certificates
       failure_stack failure_certificates.
     candle_cv_q_packed_source_certificate_success
       (Cexp_if (candle_cv_bool condition)
         (candle_cv_q_packed_object_certificate_state T
           success_stack success_certificates)
         (candle_cv_q_packed_object_certificate_failure
           failure_stack failure_certificates)) <=>
     condition`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `condition:bool` THEN
  ASM_REWRITE_TAC
    [candle_cv_bool_def; cexp_if_def;
     candle_cv_q_packed_object_certificate_success_state;
     candle_cv_q_packed_object_certificate_success_failure] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_object_ordinary_inv_select = prove
 (`!center_boxes outer_boxes radii certificates stack.
     candle_cv_q_packed_object_ordinary_step
       center_boxes outer_boxes radii
       (candle_cv_analytic_instruction Candle_analytic_program_inv)
       certificates stack =
     candle_cv_q_packed_object_inv_step radii certificates stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_step_def;
     candle_cv_q_packed_object_nonpoly_step_def;
     candle_cv_analytic_instruction_def;
     cexp_ispair_def; cexp_eq_def; cexp_if_def;
     injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def]);;

let candle_cv_q_packed_object_ordinary_inv_shaped = prove
 (`!center_boxes outer_boxes radii item rest center_reciprocal
       box_reciprocal certificate_rest.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_inv)
         (candle_cv_q_interval_list
           (CONS center_reciprocal
             (CONS box_reciprocal certificate_rest)))
         (candle_cv_q_packed_object_stack_encode (CONS item rest))) <=>
     candle_q_interval_inv_certificate
       (candle_q_packed_object_item_center_value item)
       center_reciprocal /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_item_value_bound item)
       box_reciprocal`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_inv_select;
     candle_cv_q_packed_object_inv_step_def;
     LET_DEF; LET_END_DEF;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_interval_list_def;
     candle_cv_cval_one_suc; candle_cv_cval_two_suc;
     candle_cv_cval_three_suc; candle_cv_cval_four_suc;
     candle_cv_cval_five_suc; candle_cv_cval_six_suc;
     candle_cv_cval_seven_suc; candle_cv_cval_eight_suc;
     candle_cv_cval_list_has_def;
     candle_cv_cval_list_nth_def;
     candle_cv_cval_list_drop_def;
     cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
     candle_cv_q_packed_object_item_center_value_correct;
     candle_cv_q_packed_object_item_value_bound_correct;
     candle_cv_q_interval_inv_certificate_correct;
     candle_cv_bool_and_correct;
     candle_cv_q_packed_object_certificate_success_if]);;

let candle_cv_q_packed_object_ordinary_inv_empty = prove
 (`!center_boxes outer_boxes radii certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_inv)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_inv_select;
     candle_cv_q_packed_object_inv_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     cexp_ispair_def; cexp_if_def;
     candle_cv_q_packed_object_certificate_success_failure]);;

let candle_cv_q_packed_object_ordinary_inv_cert0 = prove
 (`!center_boxes outer_boxes radii item rest.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_inv)
         (candle_cv_q_interval_list [])
         (candle_cv_q_packed_object_stack_encode (CONS item rest)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_inv_select;
     candle_cv_q_packed_object_inv_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_interval_list_def;
     candle_cv_cval_two_suc; candle_cv_cval_list_has_def;
     cexp_ispair_def; cexp_if_def;
     candle_cv_q_packed_object_certificate_success_failure]);;

let candle_cv_q_packed_object_ordinary_inv_cert1 = prove
 (`!center_boxes outer_boxes radii item rest certificate.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_inv)
         (candle_cv_q_interval_list [certificate])
         (candle_cv_q_packed_object_stack_encode (CONS item rest)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_inv_select;
     candle_cv_q_packed_object_inv_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_interval_list_def;
     candle_cv_cval_one_suc; candle_cv_cval_two_suc;
     candle_cv_cval_list_has_def;
     cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
     candle_cv_q_packed_object_certificate_success_failure]);;

let candle_q_packed_object_ordinary_inverse_exists = prove
 (`!center_boxes outer_boxes radii item rest center_reciprocal
       box_reciprocal certificate_rest.
     candle_q_interval_inv_certificate
       (candle_q_packed_object_item_center_value item)
       center_reciprocal /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_item_value_bound item)
       box_reciprocal
     ==>
     ?next remaining.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_inv
         (CONS center_reciprocal
           (CONS box_reciprocal certificate_rest))
         (CONS item rest) next remaining`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_packed_object_source_ordinary_step_def;
     candle_q_packed_object_source_nonpoly_step_def;
     distinctness "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_cv_q_packed_object_ordinary_inv_sound = prove
 (`!stack center_boxes outer_boxes radii certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_inv)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_inv certificates stack next
         certificate_rest`,
  X_GEN_TAC `stack:(candle_q_packed_object_item)list` THEN
  MP_TAC (ISPEC `stack:(candle_q_packed_object_item)list` list_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `item:candle_q_packed_object_item`
        (X_CHOOSE_THEN `rest:(candle_q_packed_object_item)list`
          SUBST_ALL_TAC))) THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_object_ordinary_inv_empty];
    MAP_EVERY X_GEN_TAC
      [`center_boxes:((((num#num)#num)#((num#num)#num))list)`;
       `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
       `radii:((num#num)#num)list`;
       `certificates:(((num#num)#num)#((num#num)#num))list`] THEN
    MP_TAC
      (ISPEC
        `certificates:(((num#num)#num)#((num#num)#num))list`
        list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN
          `center_reciprocal:((num#num)#num)#((num#num)#num)`
          (X_CHOOSE_THEN
            `tail:(((num#num)#num)#((num#num)#num))list`
            SUBST_ALL_TAC))) THENL
     [MESON_TAC[candle_cv_q_packed_object_ordinary_inv_cert0];
      MP_TAC
        (ISPEC `tail:(((num#num)#num)#((num#num)#num))list`
          list_CASES) THEN
      DISCH_THEN
        (DISJ_CASES_THEN2 SUBST_ALL_TAC
          (X_CHOOSE_THEN
            `box_reciprocal:((num#num)#num)#((num#num)#num)`
            (X_CHOOSE_THEN
              `certificate_rest:
                (((num#num)#num)#((num#num)#num))list`
              SUBST_ALL_TAC))) THENL
       [MESON_TAC[candle_cv_q_packed_object_ordinary_inv_cert1];
        REWRITE_TAC[candle_cv_q_packed_object_ordinary_inv_shaped] THEN
        MESON_TAC[candle_q_packed_object_ordinary_inverse_exists]]]]);;

let candle_suc_le_suc = ARITH_RULE `SUC n <= SUC m <=> n <= m`;;

let candle_cv_cval_list_has_interval_list = prove
 (`!n values.
     candle_cv_cval_list_has (Cexp_num n)
       (candle_cv_q_interval_list values) =
     candle_cv_bool (n <= LENGTH values)`,
  INDUCT_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[candle_cv_cval_list_has_def; candle_cv_bool_def] THEN
    REWRITE_TAC[ARITH_RULE `0 <= n`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    X_GEN_TAC `values:(((num#num)#num)#((num#num)#num))list` THEN
    MP_TAC
      (ISPEC `values:(((num#num)#num)#((num#num)#num))list`
        list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `head:((num#num)#num)#((num#num)#num)`
          (X_CHOOSE_THEN
            `tail:(((num#num)#num)#((num#num)#num))list`
            SUBST_ALL_TAC))) THENL
     [REWRITE_TAC
        [candle_cv_q_interval_list_def; candle_cv_cval_list_has_def;
         candle_cv_bool_def; LENGTH] THEN
      REWRITE_TAC[ARITH_RULE `~(SUC n <= 0)`];
      ASM_REWRITE_TAC
        [candle_cv_q_interval_list_def; candle_cv_cval_list_has_def;
         LENGTH; candle_suc_le_suc]]]);;

let candle_list_prefix_decomposition = prove
 (`!n (items:A list).
     n <= LENGTH items
     ==>
     ?prefix rest.
       LENGTH prefix = n /\ items = APPEND prefix rest`,
  INDUCT_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    EXISTS_TAC `[]:A list` THEN EXISTS_TAC `items:A list` THEN
    REWRITE_TAC[LENGTH; APPEND];
    X_GEN_TAC `items:A list` THEN
    MP_TAC (ISPEC `items:A list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `head:A`
          (X_CHOOSE_THEN `tail:A list` SUBST_ALL_TAC))) THENL
     [REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[LENGTH; candle_suc_le_suc] THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `tail:A list`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN
        (X_CHOOSE_THEN `prefix:A list`
          (X_CHOOSE_THEN `rest:A list` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `(CONS head prefix):A list` THEN
      EXISTS_TAC `rest:A list` THEN
      ASM_REWRITE_TAC[LENGTH; APPEND]]]);;

let candle_list_length_five = prove
 (`!items:A list.
     LENGTH items = 5 <=>
     ?x1 x2 x3 x4 x5. items = [x1;x2;x3;x4;x5]`,
  GEN_TAC THEN
  REWRITE_TAC
    [ARITH_RULE `5 = SUC (SUC (SUC (SUC (SUC 0))))`;
     LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let candle_list_length_at_least_five = prove
 (`!items:A list.
     5 <= LENGTH items
     ==>
     ?x1 x2 x3 x4 x5 rest.
       items = x1::x2::x3::x4::x5::rest`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
    (SPECL [`5`; `items:A list`] candle_list_prefix_decomposition) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `prefix:A list`
      (X_CHOOSE_THEN `rest:A list` STRIP_ASSUME_TAC)) THEN
  MP_TAC (SPEC `prefix:A list` candle_list_length_five) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `x1:A`
      (X_CHOOSE_THEN `x2:A`
        (X_CHOOSE_THEN `x3:A`
          (X_CHOOSE_THEN `x4:A`
            (X_CHOOSE_THEN `x5:A` SUBST_ALL_TAC))))) THEN
  MAP_EVERY EXISTS_TAC
    [`x1:A`; `x2:A`; `x3:A`; `x4:A`; `x5:A`; `rest:A list`] THEN
  ASM_REWRITE_TAC[APPEND]);;

let candle_cv_q_packed_object_ordinary_sqrt_select = prove
 (`!center_boxes outer_boxes radii source_sqrt certificates stack.
     candle_cv_q_packed_object_ordinary_step
       center_boxes outer_boxes radii
       (candle_cv_analytic_instruction
         (Candle_analytic_program_sqrt source_sqrt))
       certificates stack =
     candle_cv_q_packed_object_sqrt_step radii certificates stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_step_def;
     candle_cv_q_packed_object_nonpoly_step_def;
     candle_cv_analytic_instruction_def;
     cexp_ispair_def; cexp_fst_def; cexp_eq_def; cexp_if_def;
     injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[candle_cv_cval_one_suc; cexp_if_def]);;

let candle_cv_q_interval_sqrt_certificate_bool_correct = prove
 (`!input output.
     candle_cv_q_interval_sqrt_certificate
       (candle_cv_q_interval input) (candle_cv_q_interval output) =
     candle_cv_bool
       (candle_q_interval_sqrt_certificate input output)`,
  REWRITE_TAC
    [candle_cv_q_interval_sqrt_certificate_correct;
     candle_cv_bool_def; ARITH_RULE `1 = SUC 0`]);;

let candle_cv_q_packed_object_ordinary_sqrt_shaped = prove
 (`!center_boxes outer_boxes radii source_sqrt item rest center_root
       box_root center_derivative box_derivative box_second_reciprocal
       certificate_rest.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction
           (Candle_analytic_program_sqrt source_sqrt))
         (candle_cv_q_interval_list
           (center_root::box_root::center_derivative::box_derivative::
            box_second_reciprocal::certificate_rest))
         (candle_cv_q_packed_object_stack_encode (CONS item rest))) <=>
     candle_q_interval_sqrt_certificate
       (candle_q_packed_object_item_center_value item) center_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add center_root center_root)
       center_derivative /\
     candle_q_interval_sqrt_certificate
       (candle_q_packed_object_item_value_bound item) box_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add box_root box_root) box_derivative /\
     candle_q_interval_inv_certificate
       (candle_q_interval_mul
         (candle_q_interval_add box_root box_root)
         (candle_q_interval_add
           (candle_q_packed_object_item_value_bound item)
           (candle_q_packed_object_item_value_bound item)))
       box_second_reciprocal`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_sqrt_select;
     candle_cv_q_packed_object_sqrt_step_def;
     LET_DEF; LET_END_DEF;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_interval_list_def;
     candle_cv_cval_one_suc; candle_cv_cval_two_suc;
     candle_cv_cval_three_suc; candle_cv_cval_four_suc;
     candle_cv_cval_five_suc; candle_cv_cval_six_suc;
     candle_cv_cval_seven_suc; candle_cv_cval_eight_suc;
     candle_cv_cval_list_has_def;
     candle_cv_cval_list_nth_def;
     candle_cv_cval_list_drop_def;
     cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
     candle_cv_q_packed_object_item_center_value_correct;
     candle_cv_q_packed_object_item_value_bound_correct;
     candle_cv_q_interval_add_correct;
     candle_cv_q_interval_mul_correct;
     candle_cv_q_interval_sqrt_certificate_bool_correct;
     candle_cv_q_interval_inv_certificate_correct;
     candle_cv_bool_and_correct;
     candle_cv_q_packed_object_certificate_success_if]);;

let candle_cv_q_packed_object_ordinary_sqrt_empty = prove
 (`!center_boxes outer_boxes radii source_sqrt certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction
           (Candle_analytic_program_sqrt source_sqrt))
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_sqrt_select;
     candle_cv_q_packed_object_sqrt_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     cexp_ispair_def; cexp_if_def;
     candle_cv_q_packed_object_certificate_success_failure]);;

let candle_cv_q_packed_object_ordinary_sqrt_short = prove
 (`!center_boxes outer_boxes radii source_sqrt certificates item rest.
     LENGTH certificates < 5
     ==>
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction
           (Candle_analytic_program_sqrt source_sqrt))
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode (CONS item rest)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_sqrt_select;
     candle_cv_q_packed_object_sqrt_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_cval_list_has_interval_list;
     cexp_ispair_def; cexp_if_def] THEN
  SUBGOAL_THEN
   `~(5 <= LENGTH
      (certificates:(((num#num)#num)#((num#num)#num))list))`
  ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC
    [candle_cv_bool_def; cexp_if_def;
     candle_cv_q_packed_object_certificate_success_failure]);;

let candle_q_packed_object_ordinary_sqrt_exists = prove
 (`!center_boxes outer_boxes radii source_sqrt item rest center_root
       box_root center_derivative box_derivative box_second_reciprocal
       certificate_rest.
     candle_q_interval_sqrt_certificate
       (candle_q_packed_object_item_center_value item) center_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add center_root center_root)
       center_derivative /\
     candle_q_interval_sqrt_certificate
       (candle_q_packed_object_item_value_bound item) box_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add box_root box_root) box_derivative /\
     candle_q_interval_inv_certificate
       (candle_q_interval_mul
         (candle_q_interval_add box_root box_root)
         (candle_q_interval_add
           (candle_q_packed_object_item_value_bound item)
           (candle_q_packed_object_item_value_bound item)))
       box_second_reciprocal
     ==>
     ?next remaining.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii (Candle_analytic_program_sqrt source_sqrt)
         (center_root::box_root::center_derivative::box_derivative::
          box_second_reciprocal::certificate_rest)
         (CONS item rest) next remaining`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_packed_object_source_ordinary_step_def;
     candle_q_packed_object_source_nonpoly_step_def;
     distinctness "candle_analytic_instruction";
     injectivity "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_cv_q_packed_object_ordinary_sqrt_sound = prove
 (`!stack center_boxes outer_boxes radii source_sqrt certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction
           (Candle_analytic_program_sqrt source_sqrt))
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii (Candle_analytic_program_sqrt source_sqrt) certificates stack
         next certificate_rest`,
  X_GEN_TAC `stack:(candle_q_packed_object_item)list` THEN
  MP_TAC (ISPEC `stack:(candle_q_packed_object_item)list` list_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `item:candle_q_packed_object_item`
        (X_CHOOSE_THEN `rest:(candle_q_packed_object_item)list`
          SUBST_ALL_TAC))) THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_object_ordinary_sqrt_empty];
    REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "success") THEN
    SUBGOAL_THEN
     `5 <= LENGTH
        (certificates:(((num#num)#num)#((num#num)#num))list)`
    (LABEL_TAC "length") THENL
     [ASM_CASES_TAC
       `LENGTH
          (certificates:(((num#num)#num)#((num#num)#num))list) < 5`
      THENL
       [ASM_MESON_TAC[candle_cv_q_packed_object_ordinary_sqrt_short];
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC
      (ISPEC
        `certificates:(((num#num)#num)#((num#num)#num))list`
        candle_list_length_at_least_five) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    USE_THEN "success" MP_TAC THEN
    REWRITE_TAC[candle_cv_q_packed_object_ordinary_sqrt_shaped] THEN
    MESON_TAC[candle_q_packed_object_ordinary_sqrt_exists]]);;

let candle_list_length_eight = prove
 (`!items:A list.
     LENGTH items = 8 <=>
     ?x1 x2 x3 x4 x5 x6 x7 x8.
       items = [x1;x2;x3;x4;x5;x6;x7;x8]`,
  GEN_TAC THEN
  REWRITE_TAC
    [ARITH_RULE
      `8 = SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))`;
     LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let candle_list_length_at_least_eight = prove
 (`!items:A list.
     8 <= LENGTH items
     ==>
     ?x1 x2 x3 x4 x5 x6 x7 x8 rest.
       items = x1::x2::x3::x4::x5::x6::x7::x8::rest`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
    (SPECL [`8`; `items:A list`] candle_list_prefix_decomposition) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `prefix:A list`
      (X_CHOOSE_THEN `rest:A list` STRIP_ASSUME_TAC)) THEN
  MP_TAC (SPEC `prefix:A list` candle_list_length_eight) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `x1:A`
      (X_CHOOSE_THEN `x2:A`
        (X_CHOOSE_THEN `x3:A`
          (X_CHOOSE_THEN `x4:A`
            (X_CHOOSE_THEN `x5:A`
              (X_CHOOSE_THEN `x6:A`
                (X_CHOOSE_THEN `x7:A`
                  (X_CHOOSE_THEN `x8:A` SUBST_ALL_TAC)))))))) THEN
  MAP_EVERY EXISTS_TAC
    [`x1:A`; `x2:A`; `x3:A`; `x4:A`; `x5:A`; `x6:A`; `x7:A`;
     `x8:A`; `rest:A list`] THEN
  ASM_REWRITE_TAC[APPEND]);;

let candle_cv_q_packed_object_ordinary_atn_select = prove
 (`!center_boxes outer_boxes radii certificates stack.
     candle_cv_q_packed_object_ordinary_step
       center_boxes outer_boxes radii
       (candle_cv_analytic_instruction Candle_analytic_program_atn)
       certificates stack =
     candle_cv_q_packed_object_atn_step radii certificates stack`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_step_def;
     candle_cv_q_packed_object_nonpoly_step_def;
     candle_cv_analytic_instruction_def;
     cexp_ispair_def; cexp_eq_def; cexp_if_def;
     injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def]);;

let candle_cv_q_packed_object_ordinary_atn_shaped = prove
 (`!center_boxes outer_boxes radii item rest center_input box_input
       center_result center_square center_derivative box_square box_derivative
       box_derivative_square certificate_rest.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_atn)
         (candle_cv_q_interval_list
           (center_input::box_input::center_result::center_square::
            center_derivative::box_square::box_derivative::
            box_derivative_square::certificate_rest))
         (candle_cv_q_packed_object_stack_encode (CONS item rest))) <=>
     candle_q_interval_atn_outer_certificate
       (candle_q_packed_object_item_center_value item)
       center_input center_result /\
     candle_q_interval_square_outer_certificate
       (candle_q_packed_object_item_center_value item)
       center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator center_square)
       center_derivative /\
     candle_q_interval_square_outer_certificate
       (candle_q_packed_object_item_value_bound item)
       box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_atn_select;
     candle_cv_q_packed_object_atn_step_def;
     LET_DEF; LET_END_DEF;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_interval_list_def;
     candle_cv_cval_one_suc; candle_cv_cval_two_suc;
     candle_cv_cval_three_suc; candle_cv_cval_four_suc;
     candle_cv_cval_five_suc; candle_cv_cval_six_suc;
     candle_cv_cval_seven_suc; candle_cv_cval_eight_suc;
     candle_cv_cval_list_has_def;
     candle_cv_cval_list_nth_def;
     candle_cv_cval_list_drop_def;
     cexp_ispair_def; cexp_fst_def; cexp_snd_def; cexp_if_def;
     candle_cv_q_packed_object_item_center_value_correct;
     candle_cv_q_packed_object_item_value_bound_correct;
     candle_cv_q_packed_object_atn_denominator_correct;
     candle_cv_q_interval_atn_outer_certificate_correct;
     candle_cv_q_interval_square_outer_certificate_correct;
     candle_cv_q_interval_inv_certificate_correct;
     candle_cv_bool_and_correct;
     candle_cv_q_packed_object_certificate_success_if]);;

let candle_cv_q_packed_object_ordinary_atn_empty = prove
 (`!center_boxes outer_boxes radii certificates.
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_atn)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode []))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_atn_select;
     candle_cv_q_packed_object_atn_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     cexp_ispair_def; cexp_if_def;
     candle_cv_q_packed_object_certificate_success_failure]);;

let candle_cv_q_packed_object_ordinary_atn_short = prove
 (`!center_boxes outer_boxes radii certificates item rest.
     LENGTH certificates < 8
     ==>
     ~candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_atn)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode (CONS item rest)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_atn_select;
     candle_cv_q_packed_object_atn_step_def;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_cval_list_has_interval_list;
     cexp_ispair_def; cexp_if_def] THEN
  SUBGOAL_THEN
   `~(8 <= LENGTH
      (certificates:(((num#num)#num)#((num#num)#num))list))`
  ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC
    [candle_cv_bool_def; cexp_if_def;
     candle_cv_q_packed_object_certificate_success_failure]);;

let candle_q_packed_object_ordinary_atn_exists = prove
 (`!center_boxes outer_boxes radii item rest center_input box_input
       center_result center_square center_derivative box_square box_derivative
       box_derivative_square certificate_rest.
     candle_q_interval_atn_outer_certificate
       (candle_q_packed_object_item_center_value item)
       center_input center_result /\
     candle_q_interval_square_outer_certificate
       (candle_q_packed_object_item_center_value item)
       center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator center_square)
       center_derivative /\
     candle_q_interval_square_outer_certificate
       (candle_q_packed_object_item_value_bound item)
       box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square
     ==>
     ?next remaining.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_atn
         (center_input::box_input::center_result::center_square::
          center_derivative::box_square::box_derivative::
          box_derivative_square::certificate_rest)
         (CONS item rest) next remaining`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_packed_object_source_ordinary_step_def;
     candle_q_packed_object_source_nonpoly_step_def;
     distinctness "candle_analytic_instruction"] THEN
  MESON_TAC[]);;

let candle_cv_q_packed_object_ordinary_atn_sound = prove
 (`!stack center_boxes outer_boxes radii certificates.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction Candle_analytic_program_atn)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii Candle_analytic_program_atn certificates stack next
         certificate_rest`,
  X_GEN_TAC `stack:(candle_q_packed_object_item)list` THEN
  MP_TAC (ISPEC `stack:(candle_q_packed_object_item)list` list_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `item:candle_q_packed_object_item`
        (X_CHOOSE_THEN `rest:(candle_q_packed_object_item)list`
          SUBST_ALL_TAC))) THENL
   [REPEAT GEN_TAC THEN
    MESON_TAC[candle_cv_q_packed_object_ordinary_atn_empty];
    REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "success") THEN
    SUBGOAL_THEN
     `8 <= LENGTH
        (certificates:(((num#num)#num)#((num#num)#num))list)`
    (LABEL_TAC "length") THENL
     [ASM_CASES_TAC
       `LENGTH
          (certificates:(((num#num)#num)#((num#num)#num))list) < 8`
      THENL
       [ASM_MESON_TAC[candle_cv_q_packed_object_ordinary_atn_short];
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC
      (ISPEC
        `certificates:(((num#num)#num)#((num#num)#num))list`
        candle_list_length_at_least_eight) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    USE_THEN "success" MP_TAC THEN
    REWRITE_TAC[candle_cv_q_packed_object_ordinary_atn_shaped] THEN
    MESON_TAC[candle_q_packed_object_ordinary_atn_exists]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_certificate_success_if;
     candle_cv_q_packed_object_ordinary_inv_select;
     candle_cv_q_packed_object_ordinary_inv_shaped;
     candle_cv_q_packed_object_ordinary_inv_empty;
     candle_cv_q_packed_object_ordinary_inv_cert0;
     candle_cv_q_packed_object_ordinary_inv_cert1;
     candle_q_packed_object_ordinary_inverse_exists;
     candle_cv_q_packed_object_ordinary_inv_sound;
     candle_suc_le_suc;
     candle_cv_cval_list_has_interval_list;
     candle_list_prefix_decomposition;
     candle_list_length_five;
     candle_list_length_at_least_five;
     candle_cv_q_packed_object_ordinary_sqrt_select;
     candle_cv_q_interval_sqrt_certificate_bool_correct;
     candle_cv_q_packed_object_ordinary_sqrt_shaped;
     candle_cv_q_packed_object_ordinary_sqrt_empty;
     candle_cv_q_packed_object_ordinary_sqrt_short;
     candle_q_packed_object_ordinary_sqrt_exists;
     candle_cv_q_packed_object_ordinary_sqrt_sound;
     candle_list_length_eight;
     candle_list_length_at_least_eight;
     candle_cv_q_packed_object_ordinary_atn_select;
     candle_cv_q_packed_object_ordinary_atn_shaped;
     candle_cv_q_packed_object_ordinary_atn_empty;
     candle_cv_q_packed_object_ordinary_atn_short;
     candle_q_packed_object_ordinary_atn_exists;
     candle_cv_q_packed_object_ordinary_atn_sound] then
  failwith "packed object ordinary certificate success sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_ORDINARY_CERTIFICATE_SUCCESS_OK DEVELOPMENT_NON_RELEASE";;

end;;
