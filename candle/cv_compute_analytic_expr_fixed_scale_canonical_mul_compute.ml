(* ========================================================================== *)
(* Canonical fast path for signed fixed products.                             *)
(*                                                                            *)
(* A signed integer is represented by a pair of naturals (positive,negative).*)
(* Rounded fixed-scale values are canonical: at least one component is zero.  *)
(* This derived implementation performs one natural multiplication on those  *)
(* values and retains the existing four-product formula as an exact fallback. *)
(* The original function and every theorem interface remain unchanged.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;

module Candle_cv_analytic_expr_fixed_scale_canonical_mul_compute = struct

open Candle_cv_analytic_expr_fixed_scale_compute;;

let candle_cv_fs_raw_mul_full_def = new_definition
 `candle_cv_fs_raw_mul_full x y =
    Cexp_pair
      (Cexp_add
        (Cexp_mul (Cexp_fst x) (Cexp_fst y))
        (Cexp_mul (Cexp_snd x) (Cexp_snd y)))
      (Cexp_add
        (Cexp_mul (Cexp_fst x) (Cexp_snd y))
        (Cexp_mul (Cexp_snd x) (Cexp_fst y)))`;;

let candle_cv_fs_raw_mul_canonical_def = new_definition
 `candle_cv_fs_raw_mul_canonical x y =
    Cexp_if (Cexp_eq (Cexp_snd x) (Cexp_num 0))
      (Cexp_if (Cexp_eq (Cexp_snd y) (Cexp_num 0))
        (Cexp_pair
          (Cexp_mul (Cexp_fst x) (Cexp_fst y)) (Cexp_num 0))
        (Cexp_if (Cexp_eq (Cexp_fst y) (Cexp_num 0))
          (Cexp_pair
            (Cexp_num 0) (Cexp_mul (Cexp_fst x) (Cexp_snd y)))
          (candle_cv_fs_raw_mul_full x y)))
      (Cexp_if (Cexp_eq (Cexp_fst x) (Cexp_num 0))
        (Cexp_if (Cexp_eq (Cexp_snd y) (Cexp_num 0))
          (Cexp_pair
            (Cexp_num 0) (Cexp_mul (Cexp_snd x) (Cexp_fst y)))
          (Cexp_if (Cexp_eq (Cexp_fst y) (Cexp_num 0))
            (Cexp_pair
              (Cexp_mul (Cexp_snd x) (Cexp_snd y)) (Cexp_num 0))
            (candle_cv_fs_raw_mul_full x y)))
        (candle_cv_fs_raw_mul_full x y))`;;

let candle_cv_fs_raw_mul_full_correct = prove
 (`!x y.
     candle_cv_fs_raw_mul_full x y = candle_cv_fs_raw_mul x y`,
  REWRITE_TAC
    [candle_cv_fs_raw_mul_full_def;candle_cv_fs_raw_mul_def]);;

let candle_cv_fs_raw_mul_canonical_correct = prove
 (`!x y.
     candle_cv_fs_raw_mul_canonical x y = candle_cv_fs_raw_mul x y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_mul_canonical_def;cexp_eq_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]) THEN
  ASM_REWRITE_TAC
    [candle_cv_fs_raw_mul_full_correct;candle_cv_fs_raw_mul_def] THEN
  STRUCT_CASES_TAC (SPEC `Cexp_fst x:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `Cexp_snd x:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `Cexp_fst y:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `Cexp_snd y:cval` (cases "cval")) THEN
  ASM_REWRITE_TAC
    [cexp_mul_def;cexp_add_def;MULT_CLAUSES;ADD_CLAUSES]);;

let candle_cv_fs_raw_mul_canonical_redirect = prove
 (`!x y.
     candle_cv_fs_raw_mul x y = candle_cv_fs_raw_mul_canonical x y`,
  MESON_TAC[candle_cv_fs_raw_mul_canonical_correct]);;

let candle_cv_fs_canonical_raw_mul_compute_eqs =
  map SPEC_ALL
    [candle_cv_fs_raw_mul_full_def;
     candle_cv_fs_raw_mul_canonical_def;
     candle_cv_fs_raw_mul_canonical_redirect];;

print_endline
  "CANDLE_CV_FS_CANONICAL_MUL_SUPPORT_OK DEVELOPMENT_NON_RELEASE";;

end;;
