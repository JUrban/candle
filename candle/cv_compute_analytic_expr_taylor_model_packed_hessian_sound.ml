(* ========================================================================== *)
(* Six-dimensional packed-Hessian expansion for reflected Taylor models.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fixed-width checker stores the symmetric  *)
(* upper triangle in row-major order:                                         *)
(*                                                                            *)
(*   00 01 02 03 04 05 11 12 13 14 15 22 23 24 25 33 34 35 44 45 55.        *)
(*                                                                            *)
(* The analytic Taylor theorem consumes a full 6-by-6 matrix.  Expanding the *)
(* off-diagonal entries twice is also exactly the multiplicity used by the   *)
(* checker's packed quadratic accumulator.                                   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_semantics.ml";;

module Candle_cv_analytic_expr_taylor_model_packed_hessian_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_analytic_expr_taylor_model_semantics;;

let candle_q_packed_hessian6_expand_def = new_definition
 `candle_q_packed_hessian6_expand packed =
    [[EL 0 packed; EL 1 packed; EL 2 packed; EL 3 packed; EL 4 packed;
      EL 5 packed];
     [EL 1 packed; EL 6 packed; EL 7 packed; EL 8 packed; EL 9 packed;
      EL 10 packed];
     [EL 2 packed; EL 7 packed; EL 11 packed; EL 12 packed; EL 13 packed;
      EL 14 packed];
     [EL 3 packed; EL 8 packed; EL 12 packed; EL 15 packed; EL 16 packed;
      EL 17 packed];
     [EL 4 packed; EL 9 packed; EL 13 packed; EL 16 packed; EL 18 packed;
      EL 19 packed];
     [EL 5 packed; EL 10 packed; EL 14 packed; EL 17 packed; EL 19 packed;
      EL 20 packed]]`;;

let candle_q_packed_hessian6_values_def = new_definition
 `candle_q_packed_hessian6_values (h:num->num->real) =
    [h 0 0; h 0 1; h 0 2; h 0 3; h 0 4; h 0 5;
     h 1 1; h 1 2; h 1 3; h 1 4; h 1 5;
     h 2 2; h 2 3; h 2 4; h 2 5;
     h 3 3; h 3 4; h 3 5;
     h 4 4; h 4 5;
     h 5 5]`;;

let candle_q_symmetric_hessian6_values_def = new_definition
 `candle_q_symmetric_hessian6_values (h:num->num->real) =
    [[h 0 0; h 0 1; h 0 2; h 0 3; h 0 4; h 0 5];
     [h 0 1; h 1 1; h 1 2; h 1 3; h 1 4; h 1 5];
     [h 0 2; h 1 2; h 2 2; h 2 3; h 2 4; h 2 5];
     [h 0 3; h 1 3; h 2 3; h 3 3; h 3 4; h 3 5];
     [h 0 4; h 1 4; h 2 4; h 3 4; h 4 4; h 4 5];
     [h 0 5; h 1 5; h 2 5; h 3 5; h 4 5; h 5 5]]`;;

let candle_q_packed_hessian6_expand_shape = prove
 (`!packed.
     LENGTH (candle_q_packed_hessian6_expand packed) = 6 /\
     ALL (\row. LENGTH row = 6)
       (candle_q_packed_hessian6_expand packed)`,
  REWRITE_TAC[candle_q_packed_hessian6_expand_def; LENGTH; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_all2_length = prove
 (`!P (left:A list) (right:B list).
     ALL2 P left right ==> LENGTH left = LENGTH right`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [X_GEN_TAC `right:B list` THEN
    MP_TAC (ISPEC `right:B list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `right_head:B`
          (X_CHOOSE_THEN `right_tail:B list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL2; LENGTH];
    POP_ASSUM (LABEL_TAC "length_ih") THEN
    X_GEN_TAC `right:B list` THEN
    MP_TAC (ISPEC `right:B list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `right_head:B`
          (X_CHOOSE_THEN `right_tail:B list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL2; LENGTH; SUC_INJ] THEN
    STRIP_TAC THEN
    USE_THEN "length_ih" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let candle_all2_el_lt = prove
 (`!i P (left:A list) (right:B list).
     ALL2 P left right /\ i < LENGTH left
     ==> P (EL i left) (EL i right)`,
  INDUCT_TAC THENL
   [GEN_TAC THEN X_GEN_TAC `left:A list` THEN
    MP_TAC (ISPEC `left:A list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `left_head:A`
          (X_CHOOSE_THEN `left_tail:A list` SUBST_ALL_TAC))) THEN
    X_GEN_TAC `right:B list` THEN
    MP_TAC (ISPEC `right:B list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `right_head:B`
          (X_CHOOSE_THEN `right_tail:B list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL2; LENGTH; LT; EL; HD] THEN MESON_TAC[];
    POP_ASSUM (LABEL_TAC "el_ih") THEN
    GEN_TAC THEN X_GEN_TAC `left:A list` THEN
    MP_TAC (ISPEC `left:A list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `left_head:A`
          (X_CHOOSE_THEN `left_tail:A list` SUBST_ALL_TAC))) THEN
    X_GEN_TAC `right:B list` THEN
    MP_TAC (ISPEC `right:B list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `right_head:B`
          (X_CHOOSE_THEN `right_tail:B list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL2; LENGTH; LT_SUC; EL; TL] THEN
    TRY ARITH_TAC THEN
    USE_THEN "el_ih"
      (MP_TAC o SPECL
        [`P:A->B->bool`; `left_tail:A list`; `right_tail:B list`]) THEN
    MESON_TAC[]]);;

let candle_q_stack_contains_el_lt = prove
 (`!intervals values i.
     candle_q_stack_contains intervals values /\ i < LENGTH intervals
     ==>
     candle_q_interval_contains (EL i intervals) (EL i values)`,
  REWRITE_TAC[candle_q_stack_contains_all2] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_all2_el_lt THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_hessian6_expand_contains = prove
 (`!packed values.
     candle_q_stack_contains packed values /\ LENGTH values = 21
     ==>
     ALL2 candle_q_stack_contains
       (candle_q_packed_hessian6_expand packed)
       (candle_q_packed_hessian6_expand values)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let length_th =
      MATCH_MP candle_all2_length
        (REWRITE_RULE[candle_q_stack_contains_all2]
          (ASSUME `candle_q_stack_contains packed values`)) in
  ASSUME_TAC length_th THEN
  REWRITE_TAC[candle_q_packed_hessian6_expand_def;
              candle_q_stack_contains_all2; ALL2] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC candle_q_stack_contains_el_lt THEN
   CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     ASM_ARITH_TAC]));;

let candle_q_packed_hessian6_expand_contains_symmetric_values = prove
 (`!packed (h:num->num->real).
     candle_q_stack_contains packed
       (candle_q_packed_hessian6_values h)
     ==>
     ALL2 candle_q_stack_contains
       (candle_q_packed_hessian6_expand packed)
       (candle_q_symmetric_hessian6_values h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `candle_q_packed_hessian6_expand
      (candle_q_packed_hessian6_values h) =
    candle_q_symmetric_hessian6_values h`
   (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [REWRITE_TAC[candle_q_packed_hessian6_values_def;
                candle_q_packed_hessian6_expand_def;
                candle_q_symmetric_hessian6_values_def] THEN
    CONV_TAC (DEPTH_CONV EL_CONV) THEN REFL_TAC;
    MATCH_MP_TAC candle_q_packed_hessian6_expand_contains THEN
    ASM_REWRITE_TAC[candle_q_packed_hessian6_values_def; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REFL_TAC]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_hessian6_expand_shape;
     candle_all2_length;
     candle_all2_el_lt;
     candle_q_stack_contains_el_lt;
     candle_q_packed_hessian6_expand_contains;
     candle_q_packed_hessian6_expand_contains_symmetric_values] then
  failwith "packed Hessian6 soundness: assumptions";;

print_endline
  "CANDLE_CV_PACKED_HESSIAN6_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
