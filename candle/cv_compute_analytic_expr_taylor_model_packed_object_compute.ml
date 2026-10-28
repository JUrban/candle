(* ========================================================================== *)
(* Ordinary Candle entry layer for the exact packed six-dimensional bound.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is deliberately only the final object-q *)
(* arithmetic layer.  It does not claim that its arguments came from an      *)
(* authenticated source-program run; that provenance remains an explicit     *)
(* obligation of the registered fast-evaluator refinement.                    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_packed_object_error_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_packed_object_compute = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_packed_object_error_sound;;

(* A total lookup for exact-rational lists.  The zero default is irrelevant   *)
(* on the length-checked public path and makes malformed values fail closed.  *)

let candle_q_list_lookup_def = define
 `(candle_q_list_lookup n ([]:((num#num)#num)list) = candle_q_zero) /\
  (candle_q_list_lookup 0 (CONS h t) = h) /\
  (candle_q_list_lookup (SUC n) (CONS h t) =
     candle_q_list_lookup n t)`;;

let candle_cv_q_list_lookup_def = define
 `(candle_cv_q_list_lookup (Cexp_num n) (Cexp_num z) = candle_cv_q_zero) /\
  (candle_cv_q_list_lookup (Cexp_pair p q) items = candle_cv_q_zero) /\
  (candle_cv_q_list_lookup (Cexp_num 0) (Cexp_pair h t) = h) /\
  (candle_cv_q_list_lookup (Cexp_num (SUC n)) (Cexp_pair h t) =
     candle_cv_q_list_lookup (Cexp_num n) t)`;;

let candle_cv_q_list_lookup_compute = prove
 (`!n items.
     candle_cv_q_list_lookup n items =
     Cexp_if (Cexp_ispair n)
       candle_cv_q_zero
       (Cexp_if (Cexp_ispair items)
         (Cexp_if (Cexp_eq n (Cexp_num 0))
           (Cexp_fst items)
           (candle_cv_q_list_lookup
             (Cexp_sub n (Cexp_num 1)) (Cexp_snd items)))
         candle_cv_q_zero)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `n:cval` (cases "cval")) THEN
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `m:num` SUBST1_TAC)
    (SPEC `a:num` num_CASES) THEN
  ASM_REWRITE_TAC[candle_cv_q_list_lookup_def; cexp_if_def;
                  cexp_ispair_def; cexp_eq_def; cexp_fst_def; cexp_snd_def;
                  cexp_sub_def; distinctness "cval"; injectivity "cval";
                  NOT_SUC; SUC_SUB1]);;

let candle_cv_q_list_lookup_correct = prove
 (`!n items.
     candle_cv_q_list_lookup (Cexp_num n) (candle_cv_q_list items) =
     candle_cv_q (candle_q_list_lookup n items)`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_list_lookup_def; candle_cv_q_list_def;
                  candle_q_list_lookup_def; candle_cv_q_zero_def]);;

let candle_cv_q_packed_quadratic_term_def = new_definition
 `candle_cv_q_packed_quadratic_term
      left_radius right_radius twice entry =
    let raw =
      candle_cv_q_mul (candle_cv_q_mul left_radius right_radius)
        (candle_cv_q_abs_upper entry) in
    Cexp_if twice (candle_cv_q_add raw raw) raw`;;

let candle_cv_q_packed_quadratic_term_correct = prove
 (`!left_radius right_radius twice entry.
     candle_cv_q_packed_quadratic_term
       (candle_cv_q left_radius) (candle_cv_q right_radius)
       (Cexp_num (if twice then SUC 0 else 0))
       (candle_cv_q_interval entry) =
     candle_cv_q
       (candle_q_packed_quadratic_term
         left_radius right_radius twice entry)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_quadratic_term_def;
              candle_q_packed_quadratic_term_def;
              candle_cv_q_mul_correct; candle_cv_q_add_correct;
              candle_cv_q_abs_upper_correct; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `twice:bool` THEN
  ASM_REWRITE_TAC[cexp_if_def]);;

let candle_cv_q_packed_quadratic_term_false_correct =
  GEN_ALL
    (REWRITE_RULE[COND_CLAUSES]
      (SPECL
        [`left_radius:(num#num)#num`;
         `right_radius:(num#num)#num`;
         `F`;
         `entry:((num#num)#num)#((num#num)#num)`]
        candle_cv_q_packed_quadratic_term_correct));;

let candle_cv_q_packed_quadratic_term_true_correct =
  GEN_ALL
    (REWRITE_RULE[COND_CLAUSES]
      (SPECL
        [`left_radius:(num#num)#num`;
         `right_radius:(num#num)#num`;
         `T`;
         `entry:((num#num)#num)#((num#num)#num)`]
        candle_cv_q_packed_quadratic_term_correct));;

let candle_cv_q_packed_quadratic_term_at_def = new_definition
 `candle_cv_q_packed_quadratic_term_at packed i left right twice =
    candle_cv_q_packed_quadratic_term left right twice
      (candle_cv_q_interval_lookup i packed)`;;

let candle_q_list_lookup_in_range = prove
 (`!items i. i < LENGTH items ==> candle_q_list_lookup i items = EL i items`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LT];
    X_GEN_TAC `i:num` THEN
    MP_TAC (SPEC `i:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `j:num` SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[LENGTH; candle_q_list_lookup_def;
                    EL; HD; TL; LT_SUC]]);;

let candle_q_packed_index_bounds = prove
 (`0 < 6 /\ 1 < 6 /\ 2 < 6 /\ 3 < 6 /\ 4 < 6 /\ 5 < 6 /\
   0 < 21 /\ 1 < 21 /\ 2 < 21 /\ 3 < 21 /\ 4 < 21 /\
   5 < 21 /\ 6 < 21 /\ 7 < 21 /\ 8 < 21 /\ 9 < 21 /\
   10 < 21 /\ 11 < 21 /\ 12 < 21 /\ 13 < 21 /\ 14 < 21 /\
   15 < 21 /\ 16 < 21 /\ 17 < 21 /\ 18 < 21 /\ 19 < 21 /\
   20 < 21`,
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_quadratic_term_at_def = new_definition
 `candle_q_packed_quadratic_term_at packed i left right twice =
    candle_q_packed_quadratic_term left right twice
      (candle_q_interval_lookup i packed)`;;

let candle_q_packed_quadratic_abs_upper6_lookup_def = new_definition
 `candle_q_packed_quadratic_abs_upper6_lookup radii packed =
    let r0 = candle_q_list_lookup 0 radii in
    let r1 = candle_q_list_lookup 1 radii in
    let r2 = candle_q_list_lookup 2 radii in
    let r3 = candle_q_list_lookup 3 radii in
    let r4 = candle_q_list_lookup 4 radii in
    let r5 = candle_q_list_lookup 5 radii in
    let a20 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 20 r5 r5 F)
      candle_q_zero in
    let a19 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 19 r4 r5 T) a20 in
    let a18 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 18 r4 r4 F) a19 in
    let a17 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 17 r3 r5 T) a18 in
    let a16 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 16 r3 r4 T) a17 in
    let a15 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 15 r3 r3 F) a16 in
    let a14 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 14 r2 r5 T) a15 in
    let a13 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 13 r2 r4 T) a14 in
    let a12 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 12 r2 r3 T) a13 in
    let a11 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 11 r2 r2 F) a12 in
    let a10 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 10 r1 r5 T) a11 in
    let a9 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 9 r1 r4 T) a10 in
    let a8 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 8 r1 r3 T) a9 in
    let a7 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 7 r1 r2 T) a8 in
    let a6 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 6 r1 r1 F) a7 in
    let a5 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 5 r0 r5 T) a6 in
    let a4 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 4 r0 r4 T) a5 in
    let a3 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 3 r0 r3 T) a4 in
    let a2 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 2 r0 r2 T) a3 in
    let a1 = candle_q_add
      (candle_q_packed_quadratic_term_at packed 1 r0 r1 T) a2 in
    candle_q_add
      (candle_q_packed_quadratic_term_at packed 0 r0 r0 F) a1`;;

let candle_cv_q_packed_quadratic_abs_upper6_def = new_definition
 `candle_cv_q_packed_quadratic_abs_upper6 radii packed =
    let r0 = candle_cv_q_list_lookup (Cexp_num 0) radii in
    let r1 = candle_cv_q_list_lookup (Cexp_num 1) radii in
    let r2 = candle_cv_q_list_lookup (Cexp_num 2) radii in
    let r3 = candle_cv_q_list_lookup (Cexp_num 3) radii in
    let r4 = candle_cv_q_list_lookup (Cexp_num 4) radii in
    let r5 = candle_cv_q_list_lookup (Cexp_num 5) radii in
    let true_flag = Cexp_num (SUC 0) in
    let a20 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 20)
        r5 r5 (Cexp_num 0)) candle_cv_q_zero in
    let a19 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 19)
        r4 r5 true_flag) a20 in
    let a18 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 18)
        r4 r4 (Cexp_num 0)) a19 in
    let a17 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 17)
        r3 r5 true_flag) a18 in
    let a16 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 16)
        r3 r4 true_flag) a17 in
    let a15 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 15)
        r3 r3 (Cexp_num 0)) a16 in
    let a14 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 14)
        r2 r5 true_flag) a15 in
    let a13 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 13)
        r2 r4 true_flag) a14 in
    let a12 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 12)
        r2 r3 true_flag) a13 in
    let a11 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 11)
        r2 r2 (Cexp_num 0)) a12 in
    let a10 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 10)
        r1 r5 true_flag) a11 in
    let a9 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 9)
        r1 r4 true_flag) a10 in
    let a8 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 8)
        r1 r3 true_flag) a9 in
    let a7 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 7)
        r1 r2 true_flag) a8 in
    let a6 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 6)
        r1 r1 (Cexp_num 0)) a7 in
    let a5 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 5)
        r0 r5 true_flag) a6 in
    let a4 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 4)
        r0 r4 true_flag) a5 in
    let a3 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 3)
        r0 r3 true_flag) a4 in
    let a2 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 2)
        r0 r2 true_flag) a3 in
    let a1 = candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 1)
        r0 r1 true_flag) a2 in
    candle_cv_q_add
      (candle_cv_q_packed_quadratic_term_at packed (Cexp_num 0)
        r0 r0 (Cexp_num 0)) a1`;;

let candle_cv_q_packed_quadratic_abs_upper6_correct = prove
 (`!radii packed.
     candle_cv_q_packed_quadratic_abs_upper6
       (candle_cv_q_list radii) (candle_cv_q_interval_list packed) =
     candle_cv_q
       (candle_q_packed_quadratic_abs_upper6_lookup radii packed)`,
  REWRITE_TAC[candle_cv_q_packed_quadratic_abs_upper6_def;
              candle_q_packed_quadratic_abs_upper6_lookup_def;
              candle_cv_q_packed_quadratic_term_at_def;
              candle_q_packed_quadratic_term_at_def;
              candle_cv_q_list_lookup_correct;
              candle_cv_q_interval_lookup_correct;
              candle_cv_q_packed_quadratic_term_false_correct;
              candle_cv_q_packed_quadratic_term_true_correct;
              candle_cv_q_add_correct; candle_cv_q_zero_def;
              LET_DEF; LET_END_DEF]);;

let candle_q_packed_quadratic_abs_upper6_lookup_eq = prove
 (`!radii packed.
     LENGTH radii = 6 /\ LENGTH packed = 21
     ==>
     candle_q_packed_quadratic_abs_upper6_lookup radii packed =
     candle_q_packed_quadratic_abs_upper6 radii packed`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_quadratic_abs_upper6_lookup_def;
              candle_q_packed_quadratic_abs_upper6_def;
              candle_q_packed_quadratic_terms6_def;
              candle_q_packed_sum_def;
              candle_q_packed_quadratic_term_at_def;
              LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
    `!i. i < 6 ==> candle_q_list_lookup i radii = EL i radii`
    ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC candle_q_list_lookup_in_range THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!i. i < 21 ==> candle_q_interval_lookup i packed = EL i packed`
    ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC candle_q_interval_lookup_in_range THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[candle_q_packed_index_bounds]);;

let candle_q_packed_object_error6_lookup_def = new_definition
 `candle_q_packed_object_error6_lookup radii center_gradient packed =
    let linear = candle_q_dot_abs_upper radii center_gradient in
    let quadratic =
      candle_q_packed_quadratic_abs_upper6_lookup radii packed in
    candle_q_add (candle_q_add linear linear) quadratic`;;

let candle_cv_q_packed_object_error6_def = new_definition
 `candle_cv_q_packed_object_error6 radii center_gradient packed =
    let linear = candle_cv_q_dot_abs_upper radii center_gradient in
    let quadratic =
      candle_cv_q_packed_quadratic_abs_upper6 radii packed in
    candle_cv_q_add (candle_cv_q_add linear linear) quadratic`;;

let candle_cv_q_packed_object_error6_correct = prove
 (`!radii center_gradient packed.
     candle_cv_q_packed_object_error6
       (candle_cv_q_list radii)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval_list packed) =
     candle_cv_q
       (candle_q_packed_object_error6_lookup
         radii center_gradient packed)`,
  REWRITE_TAC[candle_cv_q_packed_object_error6_def;
              candle_q_packed_object_error6_lookup_def;
              candle_cv_q_dot_abs_upper_correct;
              candle_cv_q_packed_quadratic_abs_upper6_correct;
              candle_cv_q_add_correct; LET_DEF; LET_END_DEF]);;

let candle_q_packed_object_value_bound6_lookup_def = new_definition
 `candle_q_packed_object_value_bound6_lookup
      radii center_value center_gradient packed =
    let half_error =
      candle_q_mul candle_q_half
        (candle_q_packed_object_error6_lookup
          radii center_gradient packed) in
    candle_q_interval_add center_value
      (candle_q_neg half_error,half_error)`;;

let candle_cv_q_packed_object_value_bound6_def = new_definition
 `candle_cv_q_packed_object_value_bound6
      radii center_value center_gradient packed =
    let half_error =
      candle_cv_q_mul candle_cv_q_half
        (candle_cv_q_packed_object_error6
          radii center_gradient packed) in
    candle_cv_q_interval_add center_value
      (Cexp_pair (candle_cv_q_neg half_error) half_error)`;;

let candle_cv_q_symmetric_interval_correct = prove
 (`!error.
     Cexp_pair (candle_cv_q_neg (candle_cv_q error))
       (candle_cv_q error) =
     candle_cv_q_interval (candle_q_neg error,error)`,
  REWRITE_TAC[candle_cv_q_neg_correct; candle_cv_q_interval_def;
              FST; SND]);;

let candle_cv_q_packed_object_value_bound6_correct = prove
 (`!radii center_value center_gradient packed.
     candle_cv_q_packed_object_value_bound6
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_value)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval_list packed) =
     candle_cv_q_interval
       (candle_q_packed_object_value_bound6_lookup
         radii center_value center_gradient packed)`,
  REWRITE_TAC[candle_cv_q_packed_object_value_bound6_def;
              candle_q_packed_object_value_bound6_lookup_def;
              candle_cv_q_packed_object_error6_correct;
              candle_cv_q_half_def; candle_cv_q_mul_correct;
              candle_cv_q_symmetric_interval_correct;
              candle_cv_q_interval_add_correct;
              LET_DEF; LET_END_DEF]);;

let candle_q_packed_object_value_bound6_lookup_eq = prove
 (`!radii center_value center_gradient packed.
     LENGTH radii = 6 /\ LENGTH packed = 21
     ==>
     candle_q_packed_object_value_bound6_lookup
       radii center_value center_gradient packed =
     candle_q_packed_object_value_bound6
       radii center_value center_gradient packed`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_value_bound6_lookup_def;
              candle_q_packed_object_value_bound6_def;
              candle_q_packed_object_error6_lookup_def;
              candle_q_packed_object_error6_def;
              LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[candle_q_packed_quadratic_abs_upper6_lookup_eq]);;

(* Return both the Boolean verdict and the exact upper endpoint.  Length and *)
(* domain checks are part of the ordinary function, not assumptions hidden   *)
(* in its registered fast implementation.                                    *)

let candle_cv_q_list_length_eq_correct = prove
 (`!items n.
     Cexp_eq
       (candle_cv_list_length (candle_cv_q_list items))
       (Cexp_num n) =
     candle_cv_bool (LENGTH items = n)`,
  REWRITE_TAC[candle_cv_list_length_correct; cexp_eq_def;
              candle_cv_bool_def; injectivity "cval"]);;

let candle_cv_q_interval_list_length_eq_correct = prove
 (`!items n.
     Cexp_eq
       (candle_cv_list_length (candle_cv_q_interval_list items))
       (Cexp_num n) =
     candle_cv_bool (LENGTH items = n)`,
  REWRITE_TAC[candle_cv_interval_list_length_correct; cexp_eq_def;
              candle_cv_bool_def; injectivity "cval"]);;

let candle_cv_q_le_bool_correct = prove
 (`!x y.
     candle_cv_q_le (candle_cv_q x) (candle_cv_q y) =
     candle_cv_bool (candle_q_le x y)`,
  REWRITE_TAC[candle_cv_q_le_correct; candle_cv_bool_def]);;

let candle_cv_bool_not_num_correct = prove
 (`!b.
     Cexp_if (candle_cv_bool b) (Cexp_num 0) (Cexp_num 1) =
     candle_cv_bool (~b)`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[candle_cv_bool_def; cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_bool_guard_correct = prove
 (`!guard accepted.
     Cexp_if (candle_cv_bool guard) (candle_cv_bool accepted)
       (Cexp_num 0) =
     candle_cv_bool (guard /\ accepted)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `guard:bool` THEN
  BOOL_CASES_TAC `accepted:bool` THEN
  ASM_REWRITE_TAC[candle_cv_bool_def; cexp_if_def]);;

let candle_cv_q_packed_object_finish6_def = new_definition
 `candle_cv_q_packed_object_finish6
      domain radii center_value center_gradient packed =
    let bound =
      candle_cv_q_packed_object_value_bound6
        radii center_value center_gradient packed in
    let shape =
      candle_cv_bool_and
        (Cexp_eq (candle_cv_list_length radii) (Cexp_num 6))
        (candle_cv_bool_and
          (Cexp_eq (candle_cv_list_length center_gradient) (Cexp_num 6))
          (Cexp_eq (candle_cv_list_length packed) (Cexp_num 21))) in
    Cexp_pair
      (Cexp_if (candle_cv_bool_and domain shape)
        (Cexp_if (candle_cv_q_le candle_cv_q_zero (Cexp_snd bound))
          (Cexp_num 0) (Cexp_num 1))
        (Cexp_num 0))
      (Cexp_snd bound)`;;

let candle_cv_q_packed_object_accept6_def = new_definition
 `candle_cv_q_packed_object_accept6
      domain radii center_value center_gradient packed =
    Cexp_fst
      (candle_cv_q_packed_object_finish6
        domain radii center_value center_gradient packed)`;;

let candle_cv_q_packed_object_finish6_correct = prove
 (`!domain radii center_value center_gradient packed.
     candle_cv_q_packed_object_finish6
       (candle_cv_bool domain)
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_value)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval_list packed) =
     Cexp_pair
       (candle_cv_bool
         (domain /\ LENGTH radii = 6 /\
          LENGTH center_gradient = 6 /\ LENGTH packed = 21 /\
          ~(candle_q_le candle_q_zero
             (SND
               (candle_q_packed_object_value_bound6_lookup
                 radii center_value center_gradient packed)))))
       (candle_cv_q
         (SND
           (candle_q_packed_object_value_bound6_lookup
             radii center_value center_gradient packed)))`,
  REWRITE_TAC[candle_cv_q_packed_object_finish6_def;
              candle_cv_q_packed_object_value_bound6_correct;
              candle_cv_q_list_length_eq_correct;
              candle_cv_q_interval_list_length_eq_correct;
              candle_cv_bool_and_correct;
              candle_cv_q_interval_snd_correct;
              candle_cv_q_zero_def; candle_cv_q_le_bool_correct;
              candle_cv_bool_not_num_correct;
              candle_cv_bool_guard_correct;
              LET_DEF; LET_END_DEF; CONJ_ASSOC]);;

let candle_cv_q_packed_object_accept6_correct = prove
 (`!domain radii center_value center_gradient packed.
     candle_cv_q_packed_object_accept6
       (candle_cv_bool domain)
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_value)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval_list packed) =
     candle_cv_bool
       (domain /\ LENGTH radii = 6 /\
        LENGTH center_gradient = 6 /\ LENGTH packed = 21 /\
        ~(candle_q_le candle_q_zero
           (SND
             (candle_q_packed_object_value_bound6_lookup
               radii center_value center_gradient packed))))`,
  REWRITE_TAC[candle_cv_q_packed_object_accept6_def;
              candle_cv_q_packed_object_finish6_correct;
              cexp_fst_def]);;

let candle_cv_q_packed_object_accept6_conditions = prove
 (`!domain radii center_value center_gradient packed.
     candle_cv_q_packed_object_accept6
         (candle_cv_bool domain)
         (candle_cv_q_list radii)
         (candle_cv_q_interval center_value)
         (candle_cv_q_interval_list center_gradient)
         (candle_cv_q_interval_list packed) =
     Cexp_num 1
     ==>
     domain /\ LENGTH radii = 6 /\
     LENGTH center_gradient = 6 /\ LENGTH packed = 21 /\
     ~(candle_q_le candle_q_zero
        (SND
          (candle_q_packed_object_value_bound6_lookup
            radii center_value center_gradient packed)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_object_accept6_correct;
              candle_cv_bool_def;
              injectivity "cval"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_object_accept6_negative = prove
 (`!domain radii center_value center_gradient packed.
     candle_cv_q_packed_object_accept6
         (candle_cv_bool domain)
         (candle_cv_q_list radii)
         (candle_cv_q_interval center_value)
         (candle_cv_q_interval_list center_gradient)
         (candle_cv_q_interval_list packed) =
     Cexp_num 1
     ==>
     domain /\ LENGTH radii = 6 /\
     LENGTH center_gradient = 6 /\ LENGTH packed = 21 /\
     candle_q_real
       (SND
         (candle_q_packed_object_value_bound6
           radii center_value center_gradient packed)) < &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`domain:bool`;
       `radii:((num#num)#num)list`;
       `center_value:((num#num)#num)#((num#num)#num)`;
       `center_gradient:
          (((num#num)#num)#((num#num)#num))list`;
       `packed:(((num#num)#num)#((num#num)#num))list`]
      candle_cv_q_packed_object_accept6_conditions) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_packed_object_value_bound6_lookup
      radii center_value center_gradient packed =
    candle_q_packed_object_value_bound6
      radii center_value center_gradient packed`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_value_bound6_lookup_eq THEN
    ASM_REWRITE_TAC[];
    REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
      `~candle_q_le candle_q_zero
        (SND
          (candle_q_packed_object_value_bound6_lookup
            radii center_value center_gradient packed))` THEN
    ASM_REWRITE_TAC[candle_q_le_real; candle_q_packed_real_zero;
                    REAL_NOT_LE]]);;

let candle_cv_q_packed_object_compute_eqs =
  union candle_cv_q_dim_whole_box_compute_eqs
    (map SPEC_ALL
      [candle_cv_q_list_lookup_compute;
       candle_cv_q_packed_quadratic_term_def;
       candle_cv_q_packed_quadratic_term_at_def;
       candle_cv_q_packed_quadratic_abs_upper6_def;
       candle_cv_q_packed_object_error6_def;
       candle_cv_q_packed_object_value_bound6_def;
       candle_cv_q_packed_object_finish6_def;
       candle_cv_q_packed_object_accept6_def]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_list_lookup_compute;
     candle_cv_q_list_lookup_correct;
     candle_cv_q_packed_quadratic_term_correct;
     candle_cv_q_packed_quadratic_term_false_correct;
     candle_cv_q_packed_quadratic_term_true_correct;
     candle_q_list_lookup_in_range;
     candle_q_packed_index_bounds;
     candle_q_packed_quadratic_abs_upper6_lookup_eq;
     candle_cv_q_packed_quadratic_abs_upper6_correct;
     candle_q_packed_object_value_bound6_lookup_eq;
     candle_cv_q_packed_object_error6_correct;
     candle_cv_q_symmetric_interval_correct;
     candle_cv_q_packed_object_value_bound6_correct;
     candle_cv_q_list_length_eq_correct;
     candle_cv_q_interval_list_length_eq_correct;
     candle_cv_q_le_bool_correct;
     candle_cv_bool_not_num_correct;
     candle_cv_bool_guard_correct;
     candle_cv_q_packed_object_finish6_correct;
     candle_cv_q_packed_object_accept6_correct;
     candle_cv_q_packed_object_accept6_conditions;
     candle_cv_q_packed_object_accept6_negative] then
  failwith "packed object compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_OBJECT_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
