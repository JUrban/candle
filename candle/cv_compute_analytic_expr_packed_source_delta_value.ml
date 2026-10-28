(* ========================================================================== *)
(* Exact ordinary delta-value operation for the packed-source checker.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The scale-2^40 checker recognizes six exact   *)
(* polynomial programs built from the Flyspeck delta polynomial.  Its word   *)
(* implementation refines an unnormalised exact-rational computation.  This  *)
(* file defines that same association order in ordinary HOL/Candle and proves *)
(* the reusable value-level enclosure theorem.                               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_sqrt.ml";;

module Candle_cv_analytic_expr_packed_source_delta_value = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_packed_source_sqrt;;

let candle_q_packed_delta_sum_aux_def = define
 `(candle_q_packed_delta_sum_aux [] accumulator = accumulator) /\
  (candle_q_packed_delta_sum_aux (CONS value rest) accumulator =
     candle_q_packed_delta_sum_aux rest
       (candle_q_interval_add accumulator value))`;;

let candle_q_packed_delta_sum_def = new_definition
 `candle_q_packed_delta_sum values =
    candle_q_packed_delta_sum_aux values candle_q_zero_interval`;;

let candle_real_packed_delta_sum_aux_def = define
 `(candle_real_packed_delta_sum_aux [] accumulator = accumulator) /\
  (candle_real_packed_delta_sum_aux (CONS value rest) accumulator =
     candle_real_packed_delta_sum_aux rest (accumulator + value))`;;

let candle_real_packed_delta_sum_def = new_definition
 `candle_real_packed_delta_sum values =
    candle_real_packed_delta_sum_aux values (&0)`;;

let candle_cv_q_packed_delta_sum_aux_def = define
 `(candle_cv_q_packed_delta_sum_aux (Cexp_num n) accumulator = accumulator) /\
  (candle_cv_q_packed_delta_sum_aux (Cexp_pair value rest) accumulator =
     candle_cv_q_packed_delta_sum_aux rest
       (candle_cv_q_interval_add accumulator value))`;;

let candle_cv_q_packed_delta_sum_def = new_definition
 `candle_cv_q_packed_delta_sum values =
    candle_cv_q_packed_delta_sum_aux values
      (candle_cv_q_interval candle_q_zero_interval)`;;

let candle_cv_q_packed_delta_sum_aux_correct = prove
 (`!values accumulator.
     candle_cv_q_packed_delta_sum_aux
       (candle_cv_q_interval_list values)
       (candle_cv_q_interval accumulator) =
     candle_cv_q_interval
       (candle_q_packed_delta_sum_aux values accumulator)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_interval_list_def;
                  candle_cv_q_packed_delta_sum_aux_def;
                  candle_q_packed_delta_sum_aux_def;
                  candle_cv_q_interval_add_correct]);;

let candle_cv_q_packed_delta_sum_correct = prove
 (`!values.
     candle_cv_q_packed_delta_sum
       (candle_cv_q_interval_list values) =
     candle_cv_q_interval (candle_q_packed_delta_sum values)`,
  REWRITE_TAC[candle_cv_q_packed_delta_sum_def;
              candle_q_packed_delta_sum_def;
              candle_cv_q_packed_delta_sum_aux_correct]);;

let candle_q_packed_delta_sum_aux_sound = prove
 (`!intervals values accumulator accumulator_value.
     ALL2 candle_q_interval_contains intervals values /\
     candle_q_interval_contains accumulator accumulator_value
     ==>
     candle_q_interval_contains
       (candle_q_packed_delta_sum_aux intervals accumulator)
       (candle_real_packed_delta_sum_aux values accumulator_value)`,
  LIST_INDUCT_TAC THENL
   [X_GEN_TAC `values:real list` THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `value:real`
          (X_CHOOSE_THEN `rest:real list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL2; candle_real_packed_delta_sum_aux_def;
                candle_q_packed_delta_sum_aux_def];
    POP_ASSUM (LABEL_TAC "sum_ih") THEN
    X_GEN_TAC `values:real list` THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `value:real`
          (X_CHOOSE_THEN `rest:real list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL2; candle_real_packed_delta_sum_aux_def;
                candle_q_packed_delta_sum_aux_def] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "sum_ih" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_q_interval_add_sound THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_delta_sum_sound = prove
 (`!intervals values.
     ALL2 candle_q_interval_contains intervals values
     ==>
     candle_q_interval_contains
       (candle_q_packed_delta_sum intervals)
       (candle_real_packed_delta_sum values)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_sum_def;
              candle_real_packed_delta_sum_def] THEN
  MATCH_MP_TAC candle_q_packed_delta_sum_aux_sound THEN
  ASM_REWRITE_TAC[candle_q_zero_interval_contains]);;

let candle_q_packed_delta_mul3_def = new_definition
 `candle_q_packed_delta_mul3 first second third =
    candle_q_interval_mul (candle_q_interval_mul first second) third`;;

let candle_cv_q_packed_delta_mul3_def = new_definition
 `candle_cv_q_packed_delta_mul3 first second third =
    candle_cv_q_interval_mul
      (candle_cv_q_interval_mul first second) third`;;

let candle_cv_q_packed_delta_mul3_correct = prove
 (`!first second third.
     candle_cv_q_packed_delta_mul3
       (candle_cv_q_interval first)
       (candle_cv_q_interval second)
       (candle_cv_q_interval third) =
     candle_cv_q_interval
       (candle_q_packed_delta_mul3 first second third)`,
  REWRITE_TAC[candle_cv_q_packed_delta_mul3_def;
              candle_q_packed_delta_mul3_def;
              candle_cv_q_interval_mul_correct]);;

let candle_q_packed_delta_mul3_sound = prove
 (`!first second third first_value second_value third_value.
     candle_q_interval_contains first first_value /\
     candle_q_interval_contains second second_value /\
     candle_q_interval_contains third third_value
     ==>
     candle_q_interval_contains
       (candle_q_packed_delta_mul3 first second third)
       ((first_value * second_value) * third_value)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_mul3_def] THEN
  MATCH_MP_TAC candle_q_interval_mul_sound THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_q_interval_mul_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_delta_value_six_def = new_definition
 `candle_q_packed_delta_value_six x0 x1 x2 x3 x4 x5 =
    let first_linear = candle_q_packed_delta_sum
      [candle_q_interval_neg x0;x1;x2;candle_q_interval_neg x3;x4;x5] in
    let second_linear = candle_q_packed_delta_sum
      [x0;candle_q_interval_neg x1;x2;x3;candle_q_interval_neg x4;x5] in
    let third_linear = candle_q_packed_delta_sum
      [x0;x1;candle_q_interval_neg x2;x3;x4;candle_q_interval_neg x5] in
    let first = candle_q_packed_delta_mul3 x0 x3 first_linear in
    let second = candle_q_packed_delta_mul3 x1 x4 second_linear in
    let third = candle_q_packed_delta_mul3 x2 x5 third_linear in
    let fourth = candle_q_packed_delta_mul3 x1 x2 x3 in
    let fifth = candle_q_packed_delta_mul3 x0 x2 x4 in
    let sixth = candle_q_packed_delta_mul3 x0 x1 x5 in
    let seventh = candle_q_packed_delta_mul3 x3 x4 x5 in
    candle_q_packed_delta_sum
      [first;second;third;candle_q_interval_neg fourth;
       candle_q_interval_neg fifth;candle_q_interval_neg sixth;
       candle_q_interval_neg seventh]`;;

let candle_cv_q_packed_delta_six_def = new_definition
 `candle_cv_q_packed_delta_six a b c d e f =
    Cexp_pair a (Cexp_pair b (Cexp_pair c (Cexp_pair d
      (Cexp_pair e (Cexp_pair f (Cexp_num 0))))))`;;

let candle_cv_q_packed_delta_seven_def = new_definition
 `candle_cv_q_packed_delta_seven a b c d e f g =
    Cexp_pair a (Cexp_pair b (Cexp_pair c (Cexp_pair d
      (Cexp_pair e (Cexp_pair f (Cexp_pair g (Cexp_num 0)))))))`;;

let candle_cv_q_packed_delta_six_correct = prove
 (`!a b c d e f.
     candle_cv_q_packed_delta_six
       (candle_cv_q_interval a) (candle_cv_q_interval b)
       (candle_cv_q_interval c) (candle_cv_q_interval d)
       (candle_cv_q_interval e) (candle_cv_q_interval f) =
     candle_cv_q_interval_list [a;b;c;d;e;f]`,
  REWRITE_TAC[candle_cv_q_packed_delta_six_def;
              candle_cv_q_interval_list_def]);;

let candle_cv_q_packed_delta_seven_correct = prove
 (`!a b c d e f g.
     candle_cv_q_packed_delta_seven
       (candle_cv_q_interval a) (candle_cv_q_interval b)
       (candle_cv_q_interval c) (candle_cv_q_interval d)
       (candle_cv_q_interval e) (candle_cv_q_interval f)
       (candle_cv_q_interval g) =
     candle_cv_q_interval_list [a;b;c;d;e;f;g]`,
  REWRITE_TAC[candle_cv_q_packed_delta_seven_def;
              candle_cv_q_interval_list_def]);;

let candle_cv_q_packed_delta_value_six_def = new_definition
 `candle_cv_q_packed_delta_value_six x0 x1 x2 x3 x4 x5 =
    let first_linear = candle_cv_q_packed_delta_sum
      (candle_cv_q_packed_delta_six
        (candle_cv_q_interval_neg x0) x1 x2
        (candle_cv_q_interval_neg x3) x4 x5) in
    let second_linear = candle_cv_q_packed_delta_sum
      (candle_cv_q_packed_delta_six
        x0 (candle_cv_q_interval_neg x1) x2 x3
        (candle_cv_q_interval_neg x4) x5) in
    let third_linear = candle_cv_q_packed_delta_sum
      (candle_cv_q_packed_delta_six
        x0 x1 (candle_cv_q_interval_neg x2) x3 x4
        (candle_cv_q_interval_neg x5)) in
    let first = candle_cv_q_packed_delta_mul3 x0 x3 first_linear in
    let second = candle_cv_q_packed_delta_mul3 x1 x4 second_linear in
    let third = candle_cv_q_packed_delta_mul3 x2 x5 third_linear in
    let fourth = candle_cv_q_packed_delta_mul3 x1 x2 x3 in
    let fifth = candle_cv_q_packed_delta_mul3 x0 x2 x4 in
    let sixth = candle_cv_q_packed_delta_mul3 x0 x1 x5 in
    let seventh = candle_cv_q_packed_delta_mul3 x3 x4 x5 in
    candle_cv_q_packed_delta_sum
      (candle_cv_q_packed_delta_seven first second third
        (candle_cv_q_interval_neg fourth)
        (candle_cv_q_interval_neg fifth)
        (candle_cv_q_interval_neg sixth)
        (candle_cv_q_interval_neg seventh))`;;

let candle_cv_q_packed_delta_value_six_correct = prove
 (`!x0 x1 x2 x3 x4 x5.
     candle_cv_q_packed_delta_value_six
       (candle_cv_q_interval x0) (candle_cv_q_interval x1)
       (candle_cv_q_interval x2) (candle_cv_q_interval x3)
       (candle_cv_q_interval x4) (candle_cv_q_interval x5) =
     candle_cv_q_interval
       (candle_q_packed_delta_value_six x0 x1 x2 x3 x4 x5)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_delta_value_six_def;
              candle_q_packed_delta_value_six_def;
              candle_cv_q_interval_neg_correct;
              candle_cv_q_packed_delta_six_correct;
              candle_cv_q_packed_delta_seven_correct;
              candle_cv_q_packed_delta_sum_correct;
              candle_cv_q_packed_delta_mul3_correct;
              LET_DEF; LET_END_DEF]);;

let candle_packed_delta_real_def = new_definition
 `candle_packed_delta_real x0 x1 x2 x3 x4 x5 =
    x0 * x3 * (--x0 + x1 + x2 - x3 + x4 + x5) +
    x1 * x4 * (x0 - x1 + x2 + x3 - x4 + x5) +
    x2 * x5 * (x0 + x1 - x2 + x3 + x4 - x5) -
    (x1 * x2 * x3 + x0 * x2 * x4 + x0 * x1 * x5 + x3 * x4 * x5)`;;

let candle_q_packed_delta_value_six_sound = prove
 (`!x0 x1 x2 x3 x4 x5 v0 v1 v2 v3 v4 v5.
     candle_q_interval_contains x0 v0 /\
     candle_q_interval_contains x1 v1 /\
     candle_q_interval_contains x2 v2 /\
     candle_q_interval_contains x3 v3 /\
     candle_q_interval_contains x4 v4 /\
     candle_q_interval_contains x5 v5
     ==>
     candle_q_interval_contains
       (candle_q_packed_delta_value_six x0 x1 x2 x3 x4 x5)
       (candle_packed_delta_real v0 v1 v2 v3 v4 v5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_value_six_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_packed_delta_sum
        [candle_q_interval_neg x0;x1;x2;candle_q_interval_neg x3;x4;x5])
      (--v0 + v1 + v2 - v3 + v4 + v5)`
   (LABEL_TAC "first_linear") THENL
   [SUBGOAL_THEN
     `--v0 + v1 + v2 - v3 + v4 + v5 =
      candle_real_packed_delta_sum [--v0;v1;v2;--v3;v4;v5]`
     SUBST1_TAC THENL
     [REWRITE_TAC[candle_real_packed_delta_sum_def;
                  candle_real_packed_delta_sum_aux_def] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC candle_q_packed_delta_sum_sound THEN
    REWRITE_TAC[ALL2; candle_real_packed_delta_sum_def;
                candle_real_packed_delta_sum_aux_def] THEN
    ASM_SIMP_TAC[candle_q_interval_neg_sound];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_packed_delta_sum
        [x0;candle_q_interval_neg x1;x2;x3;candle_q_interval_neg x4;x5])
      (v0 - v1 + v2 + v3 - v4 + v5)`
   (LABEL_TAC "second_linear") THENL
   [SUBGOAL_THEN
     `v0 - v1 + v2 + v3 - v4 + v5 =
      candle_real_packed_delta_sum [v0;--v1;v2;v3;--v4;v5]`
     SUBST1_TAC THENL
     [REWRITE_TAC[candle_real_packed_delta_sum_def;
                  candle_real_packed_delta_sum_aux_def] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC candle_q_packed_delta_sum_sound THEN
    REWRITE_TAC[ALL2; candle_real_packed_delta_sum_def;
                candle_real_packed_delta_sum_aux_def] THEN
    ASM_SIMP_TAC[candle_q_interval_neg_sound];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_packed_delta_sum
        [x0;x1;candle_q_interval_neg x2;x3;x4;candle_q_interval_neg x5])
      (v0 + v1 - v2 + v3 + v4 - v5)`
   (LABEL_TAC "third_linear") THENL
   [SUBGOAL_THEN
     `v0 + v1 - v2 + v3 + v4 - v5 =
      candle_real_packed_delta_sum [v0;v1;--v2;v3;v4;--v5]`
     SUBST1_TAC THENL
     [REWRITE_TAC[candle_real_packed_delta_sum_def;
                  candle_real_packed_delta_sum_aux_def] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC candle_q_packed_delta_sum_sound THEN
    REWRITE_TAC[ALL2; candle_real_packed_delta_sum_def;
                candle_real_packed_delta_sum_aux_def] THEN
    ASM_SIMP_TAC[candle_q_interval_neg_sound];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_packed_delta_real v0 v1 v2 v3 v4 v5 =
    candle_real_packed_delta_sum
      [(v0 * v3) * (--v0 + v1 + v2 - v3 + v4 + v5);
       (v1 * v4) * (v0 - v1 + v2 + v3 - v4 + v5);
       (v2 * v5) * (v0 + v1 - v2 + v3 + v4 - v5);
       --((v1 * v2) * v3);--((v0 * v2) * v4);
       --((v0 * v1) * v5);--((v3 * v4) * v5)]`
   SUBST1_TAC THENL
   [REWRITE_TAC[candle_packed_delta_real_def;
                candle_real_packed_delta_sum_def;
                candle_real_packed_delta_sum_aux_def] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC candle_q_packed_delta_sum_sound THEN
  REWRITE_TAC[ALL2; candle_real_packed_delta_sum_def;
              candle_real_packed_delta_sum_aux_def] THEN
  ASM_MESON_TAC[candle_q_packed_delta_mul3_sound;
                candle_q_interval_neg_sound]);;

let candle_cv_q_packed_source_delta_value_compute_eqs =
  candle_cv_q_packed_source_sqrt_compute_eqs @
  map SPEC_ALL
    [candle_cv_q_packed_delta_sum_aux_def;
     candle_cv_q_packed_delta_sum_def;
     candle_cv_q_packed_delta_mul3_def;
     candle_cv_q_packed_delta_six_def;
     candle_cv_q_packed_delta_seven_def;
     candle_cv_q_packed_delta_value_six_def];;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_delta_sum_aux_correct;
     candle_cv_q_packed_delta_sum_correct;
     candle_q_packed_delta_sum_aux_sound;
     candle_q_packed_delta_sum_sound;
     candle_cv_q_packed_delta_mul3_correct;
     candle_q_packed_delta_mul3_sound;
     candle_cv_q_packed_delta_six_correct;
     candle_cv_q_packed_delta_seven_correct;
     candle_cv_q_packed_delta_value_six_correct;
     candle_q_packed_delta_value_six_sound] then
  failwith "packed source delta value: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_VALUE_OK DEVELOPMENT_NON_RELEASE";;

end;;
