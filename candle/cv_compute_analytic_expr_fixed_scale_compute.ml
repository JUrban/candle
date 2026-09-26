(* ========================================================================== *)
(* Reflected fixed-scale arithmetic for centered polynomial Taylor models.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the computed-value counterpart of the *)
(* successful ordinary-ML fixed-scale discriminator.  A signed scaled value  *)
(* is represented by [Cexp_pair positive negative] and denotes               *)
(*                                                                            *)
(*                  (positive - negative) / 10^12.                           *)
(*                                                                            *)
(* Completed Taylor-model nodes are always brought back to that scale with   *)
(* directed division.  Raw products remain signed numerators only; no GCD or *)
(* general rational normalization is performed.  The first purpose of this   *)
(* file is a Kernel.compute performance/equality discriminator.  It must not  *)
(* support a release claim until its representation and semantic equivalence  *)
(* theorems are complete.                                                     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_compute.ml";;

module Candle_cv_analytic_expr_fixed_scale_compute = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;

let candle_cv_fs_scale_def = new_definition
 `candle_cv_fs_scale = Cexp_num 1000000000000`;;

let candle_cv_fs_scale_squared_def = new_definition
 `candle_cv_fs_scale_squared =
    Cexp_mul candle_cv_fs_scale candle_cv_fs_scale`;;

let candle_cv_fs_two_scale_squared_def = new_definition
 `candle_cv_fs_two_scale_squared =
    Cexp_mul (Cexp_num 2) candle_cv_fs_scale_squared`;;

let candle_cv_fs_zero_def = new_definition
 `candle_cv_fs_zero = Cexp_pair (Cexp_num 0) (Cexp_num 0)`;;

let candle_cv_fs_one_def = new_definition
 `candle_cv_fs_one = Cexp_pair candle_cv_fs_scale (Cexp_num 0)`;;

(* Raw signed numerators use the same pair representation. *)

let candle_cv_fs_raw_add_def = new_definition
 `candle_cv_fs_raw_add x y =
    Cexp_pair
      (Cexp_add (Cexp_fst x) (Cexp_fst y))
      (Cexp_add (Cexp_snd x) (Cexp_snd y))`;;

let candle_cv_fs_raw_neg_def = new_definition
 `candle_cv_fs_raw_neg x = Cexp_pair (Cexp_snd x) (Cexp_fst x)`;;

let candle_cv_fs_raw_mul_def = new_definition
 `candle_cv_fs_raw_mul x y =
    Cexp_pair
      (Cexp_add
        (Cexp_mul (Cexp_fst x) (Cexp_fst y))
        (Cexp_mul (Cexp_snd x) (Cexp_snd y)))
      (Cexp_add
        (Cexp_mul (Cexp_fst x) (Cexp_snd y))
        (Cexp_mul (Cexp_snd x) (Cexp_fst y)))`;;

let candle_cv_fs_raw_scale_def = new_definition
 `candle_cv_fs_raw_scale factor x =
    Cexp_pair
      (Cexp_mul factor (Cexp_fst x))
      (Cexp_mul factor (Cexp_snd x))`;;

let candle_cv_fs_raw_le_def = new_definition
 `candle_cv_fs_raw_le x y =
    Cexp_less
      (Cexp_add (Cexp_fst x) (Cexp_snd y))
      (Cexp_add
        (Cexp_add (Cexp_fst y) (Cexp_snd x)) (Cexp_num 1))`;;

let candle_cv_fs_raw_min_def = new_definition
 `candle_cv_fs_raw_min x y =
    Cexp_if (candle_cv_fs_raw_le x y) x y`;;

let candle_cv_fs_raw_max_def = new_definition
 `candle_cv_fs_raw_max x y =
    Cexp_if (candle_cv_fs_raw_le x y) y x`;;

let candle_cv_fs_raw_abs_def = new_definition
 `candle_cv_fs_raw_abs x =
    candle_cv_fs_raw_max x (candle_cv_fs_raw_neg x)`;;

let candle_cv_fs_canonical_def = new_definition
 `candle_cv_fs_canonical x =
    Cexp_if (Cexp_less (Cexp_fst x) (Cexp_snd x))
      (Cexp_pair (Cexp_num 0)
        (Cexp_sub (Cexp_snd x) (Cexp_fst x)))
      (Cexp_pair
        (Cexp_sub (Cexp_fst x) (Cexp_snd x)) (Cexp_num 0))`;;

let candle_cv_fs_add_def = new_definition
 `candle_cv_fs_add x y =
    candle_cv_fs_canonical (candle_cv_fs_raw_add x y)`;;

let candle_cv_fs_neg_def = new_definition
 `candle_cv_fs_neg x = candle_cv_fs_raw_neg x`;;

let candle_cv_fs_floor_div_def = new_definition
 `candle_cv_fs_floor_div x denominator =
    Cexp_if (Cexp_less (Cexp_fst x) (Cexp_snd x))
      (Cexp_pair (Cexp_num 0)
        (candle_cv_q_ceil_div
          (Cexp_sub (Cexp_snd x) (Cexp_fst x)) denominator))
      (Cexp_pair
        (Cexp_div
          (Cexp_sub (Cexp_fst x) (Cexp_snd x)) denominator)
        (Cexp_num 0))`;;

let candle_cv_fs_ceil_div_def = new_definition
 `candle_cv_fs_ceil_div x denominator =
    Cexp_if (Cexp_less (Cexp_fst x) (Cexp_snd x))
      (Cexp_pair (Cexp_num 0)
        (Cexp_div
          (Cexp_sub (Cexp_snd x) (Cexp_fst x)) denominator))
      (Cexp_pair
        (candle_cv_q_ceil_div
          (Cexp_sub (Cexp_fst x) (Cexp_snd x)) denominator)
        (Cexp_num 0))`;;

let candle_cv_fs_of_q_lower_def = new_definition
 `candle_cv_fs_of_q_lower q =
    Cexp_fst (candle_cv_q_fixed_round_lower q)`;;

let candle_cv_fs_of_q_upper_def = new_definition
 `candle_cv_fs_of_q_upper q =
    Cexp_fst (candle_cv_q_fixed_round_upper q)`;;

let candle_cv_fs_to_q_def = new_definition
 `candle_cv_fs_to_q x =
    Cexp_pair x (Cexp_sub candle_cv_fs_scale (Cexp_num 1))`;;

(* Fixed intervals and raw-numerator intervals. *)

let candle_cv_fs_interval_zero_def = new_definition
 `candle_cv_fs_interval_zero =
    Cexp_pair candle_cv_fs_zero candle_cv_fs_zero`;;

let candle_cv_fs_interval_one_def = new_definition
 `candle_cv_fs_interval_one =
    Cexp_pair candle_cv_fs_one candle_cv_fs_one`;;

let candle_cv_fs_interval_of_q_def = new_definition
 `candle_cv_fs_interval_of_q i =
    Cexp_pair
      (candle_cv_fs_of_q_lower (Cexp_fst i))
      (candle_cv_fs_of_q_upper (Cexp_snd i))`;;

let candle_cv_fs_interval_constant_def = new_definition
 `candle_cv_fs_interval_constant q =
    Cexp_pair
      (candle_cv_fs_of_q_lower q)
      (candle_cv_fs_of_q_upper q)`;;

let candle_cv_fs_interval_neg_def = new_definition
 `candle_cv_fs_interval_neg i =
    Cexp_pair
      (candle_cv_fs_neg (Cexp_snd i))
      (candle_cv_fs_neg (Cexp_fst i))`;;

let candle_cv_fs_interval_add_def = new_definition
 `candle_cv_fs_interval_add x y =
    Cexp_pair
      (candle_cv_fs_add (Cexp_fst x) (Cexp_fst y))
      (candle_cv_fs_add (Cexp_snd x) (Cexp_snd y))`;;

let candle_cv_fs_raw_interval_neg_def = new_definition
 `candle_cv_fs_raw_interval_neg i =
    Cexp_pair
      (candle_cv_fs_raw_neg (Cexp_snd i))
      (candle_cv_fs_raw_neg (Cexp_fst i))`;;

let candle_cv_fs_raw_interval_add_def = new_definition
 `candle_cv_fs_raw_interval_add x y =
    Cexp_pair
      (candle_cv_fs_raw_add (Cexp_fst x) (Cexp_fst y))
      (candle_cv_fs_raw_add (Cexp_snd x) (Cexp_snd y))`;;

let candle_cv_fs_raw_interval_mul_def = new_definition
 `candle_cv_fs_raw_interval_mul x y =
    Cexp_pair
      (candle_cv_fs_raw_min
        (candle_cv_fs_raw_min
          (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_fst y))
          (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_snd y)))
        (candle_cv_fs_raw_min
          (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_fst y))
          (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_snd y))))
      (candle_cv_fs_raw_max
        (candle_cv_fs_raw_max
          (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_fst y))
          (candle_cv_fs_raw_mul (Cexp_fst x) (Cexp_snd y)))
        (candle_cv_fs_raw_max
          (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_fst y))
          (candle_cv_fs_raw_mul (Cexp_snd x) (Cexp_snd y))))`;;

let candle_cv_fs_raw_interval_round_def = new_definition
 `candle_cv_fs_raw_interval_round denominator i =
    Cexp_pair
      (candle_cv_fs_floor_div (Cexp_fst i) denominator)
      (candle_cv_fs_ceil_div (Cexp_snd i) denominator)`;;

let candle_cv_fs_interval_abs_upper_def = new_definition
 `candle_cv_fs_interval_abs_upper i =
    candle_cv_fs_raw_max
      (candle_cv_fs_raw_abs (Cexp_fst i))
      (candle_cv_fs_raw_abs (Cexp_snd i))`;;

(* Generic fixed-interval list and matrix plumbing. *)

let candle_cv_fs_interval_lookup_def = define
 `(candle_cv_fs_interval_lookup variable (Cexp_num n) =
     candle_cv_fs_interval_zero) /\
  (candle_cv_fs_interval_lookup (Cexp_pair p q) (Cexp_pair h t) =
     candle_cv_fs_interval_zero) /\
  (candle_cv_fs_interval_lookup (Cexp_num 0) (Cexp_pair h t) = h) /\
  (candle_cv_fs_interval_lookup (Cexp_num (SUC n)) (Cexp_pair h t) =
     candle_cv_fs_interval_lookup (Cexp_num n) t)`;;

let candle_cv_fs_interval_lookup_compute = prove
 (`!variable items.
     candle_cv_fs_interval_lookup variable items =
     Cexp_if (Cexp_ispair items)
       (Cexp_if (Cexp_ispair variable)
         candle_cv_fs_interval_zero
         (Cexp_if (Cexp_eq variable (Cexp_num 0))
           (Cexp_fst items)
           (candle_cv_fs_interval_lookup
             (Cexp_sub variable (Cexp_num 1)) (Cexp_snd items))))
       candle_cv_fs_interval_zero`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `variable:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_lookup_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def] THEN
  MP_TAC (SPEC `a:num` num_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
  REWRITE_TAC[candle_cv_fs_interval_lookup_def; cexp_eq_def;
              cexp_if_def; cexp_sub_def; injectivity "cval";
              injectivity "num"; NOT_SUC;
              ARITH_RULE `SUC n - 1 = n`] THEN
  ARITH_TAC);;

let candle_cv_fs_interval_zeros_def = define
 `(candle_cv_fs_interval_zeros (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_interval_zeros (Cexp_pair h t) =
     Cexp_pair candle_cv_fs_interval_zero
       (candle_cv_fs_interval_zeros t))`;;

let candle_cv_fs_interval_zeros_compute = prove
 (`!items.
     candle_cv_fs_interval_zeros items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair candle_cv_fs_interval_zero
         (candle_cv_fs_interval_zeros (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_zeros_def; cexp_if_def;
              cexp_ispair_def; cexp_snd_def]);;

let candle_cv_fs_interval_unit_def = define
 `(candle_cv_fs_interval_unit (Cexp_num n) (Cexp_num z) = Cexp_num 0) /\
  (candle_cv_fs_interval_unit (Cexp_pair p q) (Cexp_num z) = Cexp_num 0) /\
  (candle_cv_fs_interval_unit (Cexp_num 0) (Cexp_pair h t) =
     Cexp_pair candle_cv_fs_interval_one
       (candle_cv_fs_interval_zeros t)) /\
  (candle_cv_fs_interval_unit (Cexp_num (SUC n)) (Cexp_pair h t) =
     Cexp_pair candle_cv_fs_interval_zero
       (candle_cv_fs_interval_unit (Cexp_num n) t)) /\
  (candle_cv_fs_interval_unit (Cexp_pair p q) (Cexp_pair h t) =
     candle_cv_fs_interval_zeros (Cexp_pair h t))`;;

let candle_cv_fs_interval_unit_compute = prove
 (`!variable items.
     candle_cv_fs_interval_unit variable items =
     Cexp_if (Cexp_ispair items)
       (Cexp_if (Cexp_ispair variable)
         (candle_cv_fs_interval_zeros items)
         (Cexp_if (Cexp_eq variable (Cexp_num 0))
           (Cexp_pair candle_cv_fs_interval_one
             (candle_cv_fs_interval_zeros (Cexp_snd items)))
           (Cexp_pair candle_cv_fs_interval_zero
             (candle_cv_fs_interval_unit
               (Cexp_sub variable (Cexp_num 1)) (Cexp_snd items)))))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `variable:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_unit_def; cexp_if_def;
              cexp_ispair_def; cexp_snd_def] THEN
  MP_TAC (SPEC `a:num` num_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
  REWRITE_TAC[candle_cv_fs_interval_unit_def; cexp_eq_def;
              cexp_if_def; cexp_sub_def; injectivity "cval";
              injectivity "num"; NOT_SUC;
              ARITH_RULE `SUC n - 1 = n`] THEN
  ARITH_TAC);;

let candle_cv_fs_interval_zero_matrix_def = define
 `(candle_cv_fs_interval_zero_matrix width (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_interval_zero_matrix width (Cexp_pair h t) =
     Cexp_pair (candle_cv_fs_interval_zeros width)
       (candle_cv_fs_interval_zero_matrix width t))`;;

let candle_cv_fs_interval_zero_matrix_compute = prove
 (`!width row_lists.
     candle_cv_fs_interval_zero_matrix width row_lists =
     Cexp_if (Cexp_ispair row_lists)
       (Cexp_pair (candle_cv_fs_interval_zeros width)
         (candle_cv_fs_interval_zero_matrix width (Cexp_snd row_lists)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_zero_matrix_def; cexp_if_def;
              cexp_ispair_def; cexp_snd_def]);;

let candle_cv_fs_interval_list_of_q_def = define
 `(candle_cv_fs_interval_list_of_q (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_interval_list_of_q (Cexp_pair h t) =
     Cexp_pair (candle_cv_fs_interval_of_q h)
       (candle_cv_fs_interval_list_of_q t))`;;

let candle_cv_fs_interval_list_of_q_compute = prove
 (`!items.
     candle_cv_fs_interval_list_of_q items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair (candle_cv_fs_interval_of_q (Cexp_fst items))
         (candle_cv_fs_interval_list_of_q (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_list_of_q_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_list_of_q_def = define
 `(candle_cv_fs_list_of_q (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_list_of_q (Cexp_pair h t) =
     Cexp_pair (Cexp_fst h) (candle_cv_fs_list_of_q t))`;;

let candle_cv_fs_list_of_q_compute = prove
 (`!items.
     candle_cv_fs_list_of_q items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair (Cexp_fst (Cexp_fst items))
         (candle_cv_fs_list_of_q (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_list_of_q_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_interval_list_neg_def = define
 `(candle_cv_fs_interval_list_neg (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_interval_list_neg (Cexp_pair h t) =
     Cexp_pair (candle_cv_fs_interval_neg h)
       (candle_cv_fs_interval_list_neg t))`;;

let candle_cv_fs_interval_list_neg_compute = prove
 (`!items.
     candle_cv_fs_interval_list_neg items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair (candle_cv_fs_interval_neg (Cexp_fst items))
         (candle_cv_fs_interval_list_neg (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_list_neg_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_interval_list_add_def = define
 `(candle_cv_fs_interval_list_add (Cexp_num n) ys = Cexp_num 0) /\
  (candle_cv_fs_interval_list_add (Cexp_pair x xs) (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fs_interval_list_add
     (Cexp_pair x xs) (Cexp_pair y ys) =
     Cexp_pair (candle_cv_fs_interval_add x y)
       (candle_cv_fs_interval_list_add xs ys))`;;

let candle_cv_fs_interval_list_add_compute = prove
 (`!xs ys.
     candle_cv_fs_interval_list_add xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_if (Cexp_ispair ys)
         (Cexp_pair
           (candle_cv_fs_interval_add (Cexp_fst xs) (Cexp_fst ys))
           (candle_cv_fs_interval_list_add (Cexp_snd xs) (Cexp_snd ys)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `ys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_list_add_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_interval_matrix_neg_def = define
 `(candle_cv_fs_interval_matrix_neg (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_interval_matrix_neg (Cexp_pair h t) =
     Cexp_pair (candle_cv_fs_interval_list_neg h)
       (candle_cv_fs_interval_matrix_neg t))`;;

let candle_cv_fs_interval_matrix_neg_compute = prove
 (`!row_lists.
     candle_cv_fs_interval_matrix_neg row_lists =
     Cexp_if (Cexp_ispair row_lists)
       (Cexp_pair (candle_cv_fs_interval_list_neg (Cexp_fst row_lists))
         (candle_cv_fs_interval_matrix_neg (Cexp_snd row_lists)))
       (Cexp_num 0)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_matrix_neg_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_interval_matrix_add_def = define
 `(candle_cv_fs_interval_matrix_add (Cexp_num n) ys = Cexp_num 0) /\
  (candle_cv_fs_interval_matrix_add (Cexp_pair x xs) (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fs_interval_matrix_add
     (Cexp_pair x xs) (Cexp_pair y ys) =
     Cexp_pair (candle_cv_fs_interval_list_add x y)
       (candle_cv_fs_interval_matrix_add xs ys))`;;

let candle_cv_fs_interval_matrix_add_compute = prove
 (`!xs ys.
     candle_cv_fs_interval_matrix_add xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_if (Cexp_ispair ys)
         (Cexp_pair
           (candle_cv_fs_interval_list_add (Cexp_fst xs) (Cexp_fst ys))
           (candle_cv_fs_interval_matrix_add (Cexp_snd xs) (Cexp_snd ys)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `ys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_matrix_add_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

(* Raw product list/matrix operations.  Every member of these structures has *)
(* the same implicit denominator within a call.                              *)

let candle_cv_fs_raw_interval_list_add_def = define
 `(candle_cv_fs_raw_interval_list_add (Cexp_num n) ys = Cexp_num 0) /\
  (candle_cv_fs_raw_interval_list_add (Cexp_pair x xs) (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fs_raw_interval_list_add
     (Cexp_pair x xs) (Cexp_pair y ys) =
     Cexp_pair (candle_cv_fs_raw_interval_add x y)
       (candle_cv_fs_raw_interval_list_add xs ys))`;;

let candle_cv_fs_raw_interval_list_add_compute = prove
 (`!xs ys.
     candle_cv_fs_raw_interval_list_add xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_if (Cexp_ispair ys)
         (Cexp_pair
           (candle_cv_fs_raw_interval_add (Cexp_fst xs) (Cexp_fst ys))
           (candle_cv_fs_raw_interval_list_add
             (Cexp_snd xs) (Cexp_snd ys)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `ys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_list_add_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_raw_interval_list_scale_def = define
 `(candle_cv_fs_raw_interval_list_scale scalar (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_raw_interval_list_scale scalar (Cexp_pair h t) =
     Cexp_pair (candle_cv_fs_raw_interval_mul scalar h)
       (candle_cv_fs_raw_interval_list_scale scalar t))`;;

let candle_cv_fs_raw_interval_list_scale_compute = prove
 (`!scalar items.
     candle_cv_fs_raw_interval_list_scale scalar items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair
         (candle_cv_fs_raw_interval_mul scalar (Cexp_fst items))
         (candle_cv_fs_raw_interval_list_scale scalar (Cexp_snd items)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_list_scale_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_raw_interval_matrix_add_def = define
 `(candle_cv_fs_raw_interval_matrix_add (Cexp_num n) ys = Cexp_num 0) /\
  (candle_cv_fs_raw_interval_matrix_add (Cexp_pair x xs) (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fs_raw_interval_matrix_add
     (Cexp_pair x xs) (Cexp_pair y ys) =
     Cexp_pair (candle_cv_fs_raw_interval_list_add x y)
       (candle_cv_fs_raw_interval_matrix_add xs ys))`;;

let candle_cv_fs_raw_interval_matrix_add_compute = prove
 (`!xs ys.
     candle_cv_fs_raw_interval_matrix_add xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_if (Cexp_ispair ys)
         (Cexp_pair
           (candle_cv_fs_raw_interval_list_add
             (Cexp_fst xs) (Cexp_fst ys))
           (candle_cv_fs_raw_interval_matrix_add
             (Cexp_snd xs) (Cexp_snd ys)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `ys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_matrix_add_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_raw_interval_matrix_scale_def = define
 `(candle_cv_fs_raw_interval_matrix_scale scalar (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fs_raw_interval_matrix_scale scalar (Cexp_pair h t) =
     Cexp_pair (candle_cv_fs_raw_interval_list_scale scalar h)
       (candle_cv_fs_raw_interval_matrix_scale scalar t))`;;

let candle_cv_fs_raw_interval_matrix_scale_compute = prove
 (`!scalar row_lists.
     candle_cv_fs_raw_interval_matrix_scale scalar row_lists =
     Cexp_if (Cexp_ispair row_lists)
       (Cexp_pair
         (candle_cv_fs_raw_interval_list_scale scalar (Cexp_fst row_lists))
         (candle_cv_fs_raw_interval_matrix_scale
           scalar (Cexp_snd row_lists)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_matrix_scale_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_raw_interval_outer_def = define
 `(candle_cv_fs_raw_interval_outer (Cexp_num n) ys = Cexp_num 0) /\
  (candle_cv_fs_raw_interval_outer (Cexp_pair x xs) ys =
     Cexp_pair (candle_cv_fs_raw_interval_list_scale x ys)
       (candle_cv_fs_raw_interval_outer xs ys))`;;

let candle_cv_fs_raw_interval_outer_compute = prove
 (`!xs ys.
     candle_cv_fs_raw_interval_outer xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_pair
         (candle_cv_fs_raw_interval_list_scale (Cexp_fst xs) ys)
         (candle_cv_fs_raw_interval_outer (Cexp_snd xs) ys))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_outer_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_raw_interval_list_round_def = define
 `(candle_cv_fs_raw_interval_list_round denominator (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fs_raw_interval_list_round denominator (Cexp_pair h t) =
     Cexp_pair (candle_cv_fs_raw_interval_round denominator h)
       (candle_cv_fs_raw_interval_list_round denominator t))`;;

let candle_cv_fs_raw_interval_list_round_compute = prove
 (`!denominator items.
     candle_cv_fs_raw_interval_list_round denominator items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair
         (candle_cv_fs_raw_interval_round denominator (Cexp_fst items))
         (candle_cv_fs_raw_interval_list_round
           denominator (Cexp_snd items)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_list_round_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_raw_interval_matrix_round_def = define
 `(candle_cv_fs_raw_interval_matrix_round denominator (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fs_raw_interval_matrix_round denominator (Cexp_pair h t) =
     Cexp_pair (candle_cv_fs_raw_interval_list_round denominator h)
       (candle_cv_fs_raw_interval_matrix_round denominator t))`;;

let candle_cv_fs_raw_interval_matrix_round_compute = prove
 (`!denominator row_lists.
     candle_cv_fs_raw_interval_matrix_round denominator row_lists =
     Cexp_if (Cexp_ispair row_lists)
       (Cexp_pair
         (candle_cv_fs_raw_interval_list_round
           denominator (Cexp_fst row_lists))
         (candle_cv_fs_raw_interval_matrix_round
           denominator (Cexp_snd row_lists)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_matrix_round_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

(* Taylor sums.  The dot numerator has denominator scale^2.  The weighted    *)
(* matrix numerator has denominator scale^3.                                 *)

let candle_cv_fs_dot_abs_upper_def = define
 `(candle_cv_fs_dot_abs_upper (Cexp_num n) ys = candle_cv_fs_zero) /\
  (candle_cv_fs_dot_abs_upper (Cexp_pair x xs) (Cexp_num n) =
     candle_cv_fs_zero) /\
  (candle_cv_fs_dot_abs_upper (Cexp_pair x xs) (Cexp_pair y ys) =
     candle_cv_fs_raw_add
       (candle_cv_fs_raw_mul x (candle_cv_fs_interval_abs_upper y))
       (candle_cv_fs_dot_abs_upper xs ys))`;;

let candle_cv_fs_dot_abs_upper_compute = prove
 (`!xs ys.
     candle_cv_fs_dot_abs_upper xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_if (Cexp_ispair ys)
         (candle_cv_fs_raw_add
           (candle_cv_fs_raw_mul
             (Cexp_fst xs)
             (candle_cv_fs_interval_abs_upper (Cexp_fst ys)))
           (candle_cv_fs_dot_abs_upper (Cexp_snd xs) (Cexp_snd ys)))
         candle_cv_fs_zero)
       candle_cv_fs_zero`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `ys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_dot_abs_upper_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_weighted_rows_abs_upper_def = define
 `(candle_cv_fs_weighted_rows_abs_upper radii (Cexp_num n) row_lists =
     candle_cv_fs_zero) /\
  (candle_cv_fs_weighted_rows_abs_upper
     radii (Cexp_pair w ws) (Cexp_num n) = candle_cv_fs_zero) /\
  (candle_cv_fs_weighted_rows_abs_upper
     radii (Cexp_pair w ws) (Cexp_pair interval_row row_lists) =
     candle_cv_fs_raw_add
       (candle_cv_fs_raw_mul w
         (candle_cv_fs_dot_abs_upper radii interval_row))
       (candle_cv_fs_weighted_rows_abs_upper radii ws row_lists))`;;

let candle_cv_fs_weighted_rows_abs_upper_compute = prove
 (`!radii weights row_lists.
     candle_cv_fs_weighted_rows_abs_upper radii weights row_lists =
     Cexp_if (Cexp_ispair weights)
       (Cexp_if (Cexp_ispair row_lists)
         (candle_cv_fs_raw_add
           (candle_cv_fs_raw_mul
             (Cexp_fst weights)
             (candle_cv_fs_dot_abs_upper radii (Cexp_fst row_lists)))
           (candle_cv_fs_weighted_rows_abs_upper
             radii (Cexp_snd weights) (Cexp_snd row_lists)))
         candle_cv_fs_zero)
       candle_cv_fs_zero`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `weights:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_weighted_rows_abs_upper_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

(* First jets and complete centered Taylor-model results. *)

let candle_cv_fs_first_make_def = new_definition
 `candle_cv_fs_first_make value gradient = Cexp_pair value gradient`;;

let candle_cv_fs_first_value_def = new_definition
 `candle_cv_fs_first_value first = Cexp_fst first`;;

let candle_cv_fs_first_gradient_def = new_definition
 `candle_cv_fs_first_gradient first = Cexp_snd first`;;

let candle_cv_fs_result_make_def = new_definition
 `candle_cv_fs_result_make domain center value_bound gradient_bounds hessian =
    Cexp_pair domain
      (Cexp_pair center
        (Cexp_pair value_bound (Cexp_pair gradient_bounds hessian)))`;;

let candle_cv_fs_result_domain_def = new_definition
 `candle_cv_fs_result_domain result = Cexp_fst result`;;

let candle_cv_fs_result_center_def = new_definition
 `candle_cv_fs_result_center result = Cexp_fst (Cexp_snd result)`;;

let candle_cv_fs_result_value_bound_def = new_definition
 `candle_cv_fs_result_value_bound result =
    Cexp_fst (Cexp_snd (Cexp_snd result))`;;

let candle_cv_fs_result_gradient_bounds_def = new_definition
 `candle_cv_fs_result_gradient_bounds result =
    Cexp_fst (Cexp_snd (Cexp_snd (Cexp_snd result)))`;;

let candle_cv_fs_result_hessian_def = new_definition
 `candle_cv_fs_result_hessian result =
    Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd result)))`;;

let candle_cv_fs_gradient_bounds_def = define
 `(candle_cv_fs_gradient_bounds
     radii (Cexp_num n) row_lists = Cexp_num 0) /\
  (candle_cv_fs_gradient_bounds
     radii (Cexp_pair g gs) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_gradient_bounds
     radii (Cexp_pair g gs) (Cexp_pair interval_row row_lists) =
     Cexp_pair
       (candle_cv_fs_raw_interval_round candle_cv_fs_scale
         (candle_cv_fs_raw_interval_add
           (Cexp_pair
             (candle_cv_fs_raw_scale candle_cv_fs_scale (Cexp_fst g))
             (candle_cv_fs_raw_scale candle_cv_fs_scale (Cexp_snd g)))
           (Cexp_pair
             (candle_cv_fs_raw_neg
               (candle_cv_fs_dot_abs_upper radii interval_row))
             (candle_cv_fs_dot_abs_upper radii interval_row))))
       (candle_cv_fs_gradient_bounds radii gs row_lists))`;;

let candle_cv_fs_gradient_bounds_compute = prove
 (`!radii gradients row_lists.
     candle_cv_fs_gradient_bounds radii gradients row_lists =
     Cexp_if (Cexp_ispair gradients)
       (Cexp_if (Cexp_ispair row_lists)
         (Cexp_pair
           (candle_cv_fs_raw_interval_round candle_cv_fs_scale
             (candle_cv_fs_raw_interval_add
               (Cexp_pair
                 (candle_cv_fs_raw_scale candle_cv_fs_scale
                   (Cexp_fst (Cexp_fst gradients)))
                 (candle_cv_fs_raw_scale candle_cv_fs_scale
                   (Cexp_snd (Cexp_fst gradients))))
               (Cexp_pair
                 (candle_cv_fs_raw_neg
                   (candle_cv_fs_dot_abs_upper
                     radii (Cexp_fst row_lists)))
                 (candle_cv_fs_dot_abs_upper
                   radii (Cexp_fst row_lists)))))
           (candle_cv_fs_gradient_bounds
             radii (Cexp_snd gradients) (Cexp_snd row_lists)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `gradients:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_gradient_bounds_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_result_complete_rounded_def = new_definition
 `candle_cv_fs_result_complete_rounded radii domain center hessian =
    candle_cv_fs_result_make domain center
      (candle_cv_fs_raw_interval_round candle_cv_fs_two_scale_squared
        (candle_cv_fs_raw_interval_add
          (Cexp_pair
            (candle_cv_fs_raw_scale candle_cv_fs_two_scale_squared
              (Cexp_fst (candle_cv_fs_first_value center)))
            (candle_cv_fs_raw_scale candle_cv_fs_two_scale_squared
              (Cexp_snd (candle_cv_fs_first_value center))))
          (Cexp_pair
            (candle_cv_fs_raw_neg
              (candle_cv_fs_raw_add
                (candle_cv_fs_raw_scale
                  (Cexp_mul (Cexp_num 2) candle_cv_fs_scale)
                  (candle_cv_fs_dot_abs_upper radii
                    (candle_cv_fs_first_gradient center)))
                (candle_cv_fs_weighted_rows_abs_upper
                  radii radii hessian)))
            (candle_cv_fs_raw_add
              (candle_cv_fs_raw_scale
                (Cexp_mul (Cexp_num 2) candle_cv_fs_scale)
                (candle_cv_fs_dot_abs_upper radii
                  (candle_cv_fs_first_gradient center)))
              (candle_cv_fs_weighted_rows_abs_upper
                radii radii hessian)))))
      (candle_cv_fs_gradient_bounds
        radii (candle_cv_fs_first_gradient center) hessian)
      hessian`;;

let candle_cv_fs_result_complete_raw_def = new_definition
 `candle_cv_fs_result_complete_raw radii domain raw_center raw_hessian =
    candle_cv_fs_result_complete_rounded radii domain
      (candle_cv_fs_first_make
        (candle_cv_fs_raw_interval_round candle_cv_fs_scale
          (candle_cv_fs_first_value raw_center))
        (candle_cv_fs_raw_interval_list_round candle_cv_fs_scale
          (candle_cv_fs_first_gradient raw_center)))
      (candle_cv_fs_raw_interval_matrix_round
        candle_cv_fs_scale raw_hessian)`;;

let candle_cv_fs_result_zero_def = new_definition
 `candle_cv_fs_result_zero dimensions =
    candle_cv_fs_result_complete_rounded (Cexp_num 0) (Cexp_num 0)
      (candle_cv_fs_first_make candle_cv_fs_interval_zero
        (candle_cv_fs_interval_zeros dimensions))
      (candle_cv_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_cv_fs_result_head_def = new_definition
 `candle_cv_fs_result_head dimensions stack =
    Cexp_if (Cexp_ispair stack) (Cexp_fst stack)
      (candle_cv_fs_result_zero dimensions)`;;

let candle_cv_fs_result_tail_def = new_definition
 `candle_cv_fs_result_tail stack =
    Cexp_if (Cexp_ispair stack) (Cexp_snd stack) (Cexp_num 0)`;;

let candle_cv_fs_result_constant_def = new_definition
 `candle_cv_fs_result_constant dimensions radii q =
    candle_cv_fs_result_complete_rounded radii (Cexp_num 1)
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_constant q)
        (candle_cv_fs_interval_zeros dimensions))
      (candle_cv_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_cv_fs_result_variable_def = new_definition
 `candle_cv_fs_result_variable dimensions radii variable =
    candle_cv_fs_result_complete_rounded radii (Cexp_num 1)
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_lookup variable dimensions)
        (candle_cv_fs_interval_unit variable dimensions))
      (candle_cv_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_cv_fs_result_neg_def = new_definition
 `candle_cv_fs_result_neg radii result =
    candle_cv_fs_result_complete_rounded radii
      (candle_cv_fs_result_domain result)
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_neg
          (candle_cv_fs_first_value
            (candle_cv_fs_result_center result)))
        (candle_cv_fs_interval_list_neg
          (candle_cv_fs_first_gradient
            (candle_cv_fs_result_center result))))
      (candle_cv_fs_interval_matrix_neg
        (candle_cv_fs_result_hessian result))`;;

let candle_cv_fs_result_add_def = new_definition
 `candle_cv_fs_result_add radii left right =
    candle_cv_fs_result_complete_rounded radii
      (candle_cv_bool_and
        (candle_cv_fs_result_domain left)
        (candle_cv_fs_result_domain right))
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_add
          (candle_cv_fs_first_value (candle_cv_fs_result_center left))
          (candle_cv_fs_first_value (candle_cv_fs_result_center right)))
        (candle_cv_fs_interval_list_add
          (candle_cv_fs_first_gradient (candle_cv_fs_result_center left))
          (candle_cv_fs_first_gradient (candle_cv_fs_result_center right))))
      (candle_cv_fs_interval_matrix_add
        (candle_cv_fs_result_hessian left)
        (candle_cv_fs_result_hessian right))`;;

let candle_cv_fs_result_mul_def = new_definition
 `candle_cv_fs_result_mul radii left right =
    candle_cv_fs_result_complete_raw radii
      (candle_cv_bool_and
        (candle_cv_fs_result_domain left)
        (candle_cv_fs_result_domain right))
      (candle_cv_fs_first_make
        (candle_cv_fs_raw_interval_mul
          (candle_cv_fs_first_value (candle_cv_fs_result_center left))
          (candle_cv_fs_first_value (candle_cv_fs_result_center right)))
        (candle_cv_fs_raw_interval_list_add
          (candle_cv_fs_raw_interval_list_scale
            (candle_cv_fs_first_value (candle_cv_fs_result_center right))
            (candle_cv_fs_first_gradient (candle_cv_fs_result_center left)))
          (candle_cv_fs_raw_interval_list_scale
            (candle_cv_fs_first_value (candle_cv_fs_result_center left))
            (candle_cv_fs_first_gradient (candle_cv_fs_result_center right)))))
      (candle_cv_fs_raw_interval_matrix_add
        (candle_cv_fs_raw_interval_matrix_add
          (candle_cv_fs_raw_interval_matrix_scale
            (candle_cv_fs_result_value_bound right)
            (candle_cv_fs_result_hessian left))
          (candle_cv_fs_raw_interval_outer
            (candle_cv_fs_result_gradient_bounds left)
            (candle_cv_fs_result_gradient_bounds right)))
        (candle_cv_fs_raw_interval_matrix_add
          (candle_cv_fs_raw_interval_outer
            (candle_cv_fs_result_gradient_bounds right)
            (candle_cv_fs_result_gradient_bounds left))
          (candle_cv_fs_raw_interval_matrix_scale
            (candle_cv_fs_result_value_bound left)
            (candle_cv_fs_result_hessian right))))`;;

let candle_cv_fs_result_square_def = new_definition
 `candle_cv_fs_result_square radii result =
    candle_cv_fs_result_mul radii result result`;;

(* Postfix polynomial execution.  [dimensions] is the already rounded center *)
(* environment, so its list spine also supplies the dimension.               *)

let candle_cv_fs_poly_step_def = new_definition
 `candle_cv_fs_poly_step dimensions radii instruction stack =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
        (Cexp_pair
          (candle_cv_fs_result_constant
            dimensions radii (Cexp_snd instruction)) stack)
        (Cexp_pair
          (candle_cv_fs_result_variable
            dimensions radii (Cexp_snd instruction)) stack))
      (Cexp_if (Cexp_eq instruction (Cexp_num 2))
        (Cexp_pair
          (candle_cv_fs_result_neg radii
            (candle_cv_fs_result_head dimensions stack))
          (candle_cv_fs_result_tail stack))
        (Cexp_if (Cexp_eq instruction (Cexp_num 3))
          (Cexp_pair
            (candle_cv_fs_result_add radii
              (candle_cv_fs_result_head dimensions
                (candle_cv_fs_result_tail stack))
              (candle_cv_fs_result_head dimensions stack))
            (candle_cv_fs_result_tail
              (candle_cv_fs_result_tail stack)))
          (Cexp_if (Cexp_eq instruction (Cexp_num 4))
            (Cexp_pair
              (candle_cv_fs_result_mul radii
                (candle_cv_fs_result_head dimensions
                  (candle_cv_fs_result_tail stack))
                (candle_cv_fs_result_head dimensions stack))
              (candle_cv_fs_result_tail
                (candle_cv_fs_result_tail stack)))
            (Cexp_pair
              (candle_cv_fs_result_square radii
                (candle_cv_fs_result_head dimensions stack))
              (candle_cv_fs_result_tail stack)))))`;;

let candle_cv_fs_poly_run_def = define
 `(candle_cv_fs_poly_run
     dimensions radii (Cexp_num n) stack = stack) /\
  (candle_cv_fs_poly_run
     dimensions radii (Cexp_pair h t) stack =
     candle_cv_fs_poly_run dimensions radii t
       (candle_cv_fs_poly_step dimensions radii h stack))`;;

let candle_cv_fs_poly_run_compute = prove
 (`!dimensions radii program stack.
     candle_cv_fs_poly_run dimensions radii program stack =
     Cexp_if (Cexp_ispair program)
       (candle_cv_fs_poly_run dimensions radii (Cexp_snd program)
         (candle_cv_fs_poly_step
           dimensions radii (Cexp_fst program) stack))
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_poly_run_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_poly_program_fixed_def = new_definition
 `candle_cv_fs_poly_program_fixed dimensions radii program =
    candle_cv_fs_result_head dimensions
      (candle_cv_fs_poly_run dimensions radii program (Cexp_num 0))`;;

let candle_cv_fs_poly_program_def = new_definition
 `candle_cv_fs_poly_program center_boxes radii program =
    candle_cv_fs_poly_program_fixed
      (candle_cv_fs_interval_list_of_q center_boxes)
      (candle_cv_fs_list_of_q radii) program`;;

(* Conversion is deliberately outside the hot representation.  It supports  *)
(* exact comparison with the established rational result during development. *)

let candle_cv_fs_interval_to_q_def = new_definition
 `candle_cv_fs_interval_to_q i =
    Cexp_pair
      (candle_cv_fs_to_q (Cexp_fst i))
      (candle_cv_fs_to_q (Cexp_snd i))`;;

let candle_cv_fs_interval_list_to_q_def = define
 `(candle_cv_fs_interval_list_to_q (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_interval_list_to_q (Cexp_pair h t) =
     Cexp_pair (candle_cv_fs_interval_to_q h)
       (candle_cv_fs_interval_list_to_q t))`;;

let candle_cv_fs_interval_list_to_q_compute = prove
 (`!items.
     candle_cv_fs_interval_list_to_q items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair (candle_cv_fs_interval_to_q (Cexp_fst items))
         (candle_cv_fs_interval_list_to_q (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_list_to_q_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_interval_matrix_to_q_def = define
 `(candle_cv_fs_interval_matrix_to_q (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_interval_matrix_to_q (Cexp_pair h t) =
     Cexp_pair (candle_cv_fs_interval_list_to_q h)
       (candle_cv_fs_interval_matrix_to_q t))`;;

let candle_cv_fs_interval_matrix_to_q_compute = prove
 (`!row_lists.
     candle_cv_fs_interval_matrix_to_q row_lists =
     Cexp_if (Cexp_ispair row_lists)
       (Cexp_pair
         (candle_cv_fs_interval_list_to_q (Cexp_fst row_lists))
         (candle_cv_fs_interval_matrix_to_q (Cexp_snd row_lists)))
       (Cexp_num 0)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_interval_matrix_to_q_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_result_to_q_def = new_definition
 `candle_cv_fs_result_to_q result =
    candle_cv_q_dim_taylor_model_result_make
      (candle_cv_fs_result_domain result)
      (candle_cv_q_dim_first_jet_make
        (candle_cv_fs_interval_to_q
          (candle_cv_fs_first_value (candle_cv_fs_result_center result)))
        (candle_cv_fs_interval_list_to_q
          (candle_cv_fs_first_gradient (candle_cv_fs_result_center result))))
      (candle_cv_fs_interval_to_q
        (candle_cv_fs_result_value_bound result))
      (candle_cv_fs_interval_list_to_q
        (candle_cv_fs_result_gradient_bounds result))
      (candle_cv_fs_interval_matrix_to_q
        (candle_cv_fs_result_hessian result))`;;

let candle_cv_fs_poly_program_to_q_def = new_definition
 `candle_cv_fs_poly_program_to_q center_boxes radii program =
    candle_cv_fs_result_to_q
      (candle_cv_fs_poly_program center_boxes radii program)`;;

let candle_cv_fs_compute_eqs =
  union candle_cv_q_dim_taylor_model_compute_eqs
    (map SPEC_ALL
      [candle_cv_fs_scale_def;
       candle_cv_fs_scale_squared_def;
       candle_cv_fs_two_scale_squared_def;
       candle_cv_fs_zero_def;
       candle_cv_fs_one_def;
       candle_cv_fs_raw_add_def;
       candle_cv_fs_raw_neg_def;
       candle_cv_fs_raw_mul_def;
       candle_cv_fs_raw_scale_def;
       candle_cv_fs_raw_le_def;
       candle_cv_fs_raw_min_def;
       candle_cv_fs_raw_max_def;
       candle_cv_fs_raw_abs_def;
       candle_cv_fs_canonical_def;
       candle_cv_fs_add_def;
       candle_cv_fs_neg_def;
       candle_cv_fs_floor_div_def;
       candle_cv_fs_ceil_div_def;
       candle_cv_fs_of_q_lower_def;
       candle_cv_fs_of_q_upper_def;
       candle_cv_fs_to_q_def;
       candle_cv_fs_interval_zero_def;
       candle_cv_fs_interval_one_def;
       candle_cv_fs_interval_of_q_def;
       candle_cv_fs_interval_constant_def;
       candle_cv_fs_interval_neg_def;
       candle_cv_fs_interval_add_def;
       candle_cv_fs_raw_interval_neg_def;
       candle_cv_fs_raw_interval_add_def;
       candle_cv_fs_raw_interval_mul_def;
       candle_cv_fs_raw_interval_round_def;
       candle_cv_fs_interval_abs_upper_def;
       candle_cv_fs_interval_lookup_compute;
       candle_cv_fs_interval_zeros_compute;
       candle_cv_fs_interval_unit_compute;
       candle_cv_fs_interval_zero_matrix_compute;
       candle_cv_fs_interval_list_of_q_compute;
       candle_cv_fs_list_of_q_compute;
       candle_cv_fs_interval_list_neg_compute;
       candle_cv_fs_interval_list_add_compute;
       candle_cv_fs_interval_matrix_neg_compute;
       candle_cv_fs_interval_matrix_add_compute;
       candle_cv_fs_raw_interval_list_add_compute;
       candle_cv_fs_raw_interval_list_scale_compute;
       candle_cv_fs_raw_interval_matrix_add_compute;
       candle_cv_fs_raw_interval_matrix_scale_compute;
       candle_cv_fs_raw_interval_outer_compute;
       candle_cv_fs_raw_interval_list_round_compute;
       candle_cv_fs_raw_interval_matrix_round_compute;
       candle_cv_fs_dot_abs_upper_compute;
       candle_cv_fs_weighted_rows_abs_upper_compute;
       candle_cv_fs_first_make_def;
       candle_cv_fs_first_value_def;
       candle_cv_fs_first_gradient_def;
       candle_cv_fs_result_make_def;
       candle_cv_fs_result_domain_def;
       candle_cv_fs_result_center_def;
       candle_cv_fs_result_value_bound_def;
       candle_cv_fs_result_gradient_bounds_def;
       candle_cv_fs_result_hessian_def;
       candle_cv_fs_gradient_bounds_compute;
       candle_cv_fs_result_complete_rounded_def;
       candle_cv_fs_result_complete_raw_def;
       candle_cv_fs_result_zero_def;
       candle_cv_fs_result_head_def;
       candle_cv_fs_result_tail_def;
       candle_cv_fs_result_constant_def;
       candle_cv_fs_result_variable_def;
       candle_cv_fs_result_neg_def;
       candle_cv_fs_result_add_def;
       candle_cv_fs_result_mul_def;
       candle_cv_fs_result_square_def;
       candle_cv_fs_poly_step_def;
       candle_cv_fs_poly_run_compute;
       candle_cv_fs_poly_program_fixed_def;
       candle_cv_fs_poly_program_def;
       candle_cv_fs_interval_to_q_def;
       candle_cv_fs_interval_list_to_q_compute;
       candle_cv_fs_interval_matrix_to_q_compute;
       candle_cv_fs_result_to_q_def;
       candle_cv_fs_poly_program_to_q_def]);;

end;;
