(* ========================================================================== *)
(* Total bounded-arithmetic contract for reflected fixed-scale computation.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file specifies the logical boundary for *)
(* a future fast word executor.  The bounded result is only an optimization  *)
(* result: overflow selects the existing exact fixed-scale value.  Thus the  *)
(* theorem interface remains independent of the eventual word encoding.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;

module Candle_cv_analytic_expr_fixed_scale_bounded_contract = struct

open Candle_cv_analytic_expr_fixed_scale_compute;;

(* Exclusive signed-magnitude limits. *)

let candle_cv_fs_endpoint_limit_def = new_definition
 `candle_cv_fs_endpoint_limit =
    Cexp_num 340282366920938463463374607431768211456`;;

let candle_cv_fs_accumulator_limit_def = new_definition
 `candle_cv_fs_accumulator_limit =
    Cexp_num
      6277101735386680763835789423207666416102355444464034512896`;;

let candle_cv_fs_bounded_fits_def = new_definition
 `candle_cv_fs_bounded_fits bound value =
    Cexp_if
      (Cexp_less (Cexp_fst (candle_cv_fs_canonical value)) bound)
      (Cexp_less (Cexp_snd (candle_cv_fs_canonical value)) bound)
      (Cexp_num 0)`;;

(* A checked result is [pair success value].  Failure carries the fixed zero *)
(* only, so no rejected wide intermediate can accidentally escape.           *)

let candle_cv_fs_bounded_checked_def = new_definition
 `candle_cv_fs_bounded_checked bound exact =
    Cexp_if (candle_cv_fs_bounded_fits bound exact)
      (Cexp_pair (Cexp_num 1) exact)
      (Cexp_pair (Cexp_num 0) candle_cv_fs_zero)`;;

let candle_cv_fs_bounded_success_def = new_definition
 `candle_cv_fs_bounded_success checked = Cexp_fst checked`;;

let candle_cv_fs_bounded_value_def = new_definition
 `candle_cv_fs_bounded_value checked = Cexp_snd checked`;;

let candle_cv_fs_bounded_with_fallback_def = new_definition
 `candle_cv_fs_bounded_with_fallback bound exact =
    Cexp_if
      (candle_cv_fs_bounded_success
        (candle_cv_fs_bounded_checked bound exact))
      (candle_cv_fs_bounded_value
        (candle_cv_fs_bounded_checked bound exact))
      exact`;;

let _ = print_endline "CANDLE_CV_FS_BOUNDED_PROOF if_checked";;
let candle_cv_fs_bounded_if_checked_fallback = prove
 (`!condition value.
     Cexp_if
       (Cexp_fst
         (Cexp_if condition
           (Cexp_pair (Cexp_num 1) value)
           (Cexp_pair (Cexp_num 0) candle_cv_fs_zero)))
       (Cexp_snd
         (Cexp_if condition
           (Cexp_pair (Cexp_num 1) value)
           (Cexp_pair (Cexp_num 0) candle_cv_fs_zero)))
       value = value`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `condition:cval` (cases "cval")) THENL
   [MP_TAC (SPEC `a:num` num_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
    REWRITE_TAC[cexp_if_def;cexp_fst_def;cexp_snd_def;ONE];
    REWRITE_TAC[cexp_if_def;cexp_fst_def;cexp_snd_def;ONE]]);;

let _ = print_endline "CANDLE_CV_FS_BOUNDED_PROOF generic_fallback";;
let candle_cv_fs_bounded_with_fallback_exact = prove
 (`!bound exact.
     candle_cv_fs_bounded_with_fallback bound exact = exact`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_bounded_with_fallback_def;
              candle_cv_fs_bounded_checked_def;
              candle_cv_fs_bounded_success_def;
              candle_cv_fs_bounded_value_def] THEN
  REWRITE_TAC[candle_cv_fs_bounded_if_checked_fallback]);;

(* These first operations deliberately expose the same canonical exact value *)
(* on success and fallback.  Subsequent list/matrix operations can compose   *)
(* this contract without changing the existing fixed-scale theorem.          *)

let candle_cv_fs_bounded_add_exact_def = new_definition
 `candle_cv_fs_bounded_add_exact x y =
    candle_cv_fs_canonical (candle_cv_fs_raw_add x y)`;;

let candle_cv_fs_bounded_mul_exact_def = new_definition
 `candle_cv_fs_bounded_mul_exact x y =
    candle_cv_fs_canonical (candle_cv_fs_raw_mul x y)`;;

let candle_cv_fs_bounded_add_def = new_definition
 `candle_cv_fs_bounded_add bound x y =
    candle_cv_fs_bounded_checked bound
      (candle_cv_fs_bounded_add_exact x y)`;;

let candle_cv_fs_bounded_mul_def = new_definition
 `candle_cv_fs_bounded_mul bound x y =
    candle_cv_fs_bounded_checked bound
      (candle_cv_fs_bounded_mul_exact x y)`;;

let candle_cv_fs_bounded_add_or_exact_def = new_definition
 `candle_cv_fs_bounded_add_or_exact bound x y =
    candle_cv_fs_bounded_with_fallback bound
      (candle_cv_fs_bounded_add_exact x y)`;;

let candle_cv_fs_bounded_mul_or_exact_def = new_definition
 `candle_cv_fs_bounded_mul_or_exact bound x y =
    candle_cv_fs_bounded_with_fallback bound
      (candle_cv_fs_bounded_mul_exact x y)`;;

let _ = print_endline "CANDLE_CV_FS_BOUNDED_PROOF add_fallback";;
let candle_cv_fs_bounded_add_or_exact_correct = prove
 (`!bound x y.
     candle_cv_fs_bounded_add_or_exact bound x y =
     candle_cv_fs_bounded_add_exact x y`,
  REWRITE_TAC[candle_cv_fs_bounded_add_or_exact_def;
              candle_cv_fs_bounded_with_fallback_exact]);;

let _ = print_endline "CANDLE_CV_FS_BOUNDED_PROOF mul_fallback";;
let candle_cv_fs_bounded_mul_or_exact_correct = prove
 (`!bound x y.
     candle_cv_fs_bounded_mul_or_exact bound x y =
     candle_cv_fs_bounded_mul_exact x y`,
  REWRITE_TAC[candle_cv_fs_bounded_mul_or_exact_def;
              candle_cv_fs_bounded_with_fallback_exact]);;

let candle_cv_fs_bounded_contract_compute_eqs =
  map SPEC_ALL
    [candle_cv_fs_endpoint_limit_def;
     candle_cv_fs_accumulator_limit_def;
     candle_cv_fs_bounded_fits_def;
     candle_cv_fs_bounded_checked_def;
     candle_cv_fs_bounded_success_def;
     candle_cv_fs_bounded_value_def;
     candle_cv_fs_bounded_with_fallback_def;
     candle_cv_fs_bounded_add_exact_def;
     candle_cv_fs_bounded_mul_exact_def;
     candle_cv_fs_bounded_add_def;
     candle_cv_fs_bounded_mul_def;
     candle_cv_fs_bounded_add_or_exact_def;
     candle_cv_fs_bounded_mul_or_exact_def];;

print_endline
  "CANDLE_CV_FS_BOUNDED_CONTRACT_OK DEVELOPMENT_NON_RELEASE";;

end;;
