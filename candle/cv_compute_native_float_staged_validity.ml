(* ========================================================================== *)
(* Reflected validity checks for staged nonnegative native-float programs.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The staged evaluator used to prove every       *)
(* supplied rounding and exponent-alignment witness with ordinary rewriting  *)
(* before calling Kernel.compute.  This module evaluates that complete        *)
(* validity predicate inside the verified computation primitive and returns   *)
(* one Boolean cval.  The correctness theorem exposes the original ordinary   *)
(* predicate, so no Boolean or host-side plan is trusted.                      *)
(* ========================================================================== *)

needs "candle/cv_compute_native_float_staged_polynomial.ml";;

module Candle_cv_native_float_staged_validity = struct

open Candle_cv_native_float_core;;
open Candle_cv_native_float_staged;;
open Candle_cv_native_float_staged_fold;;
open Candle_cv_native_float_staged_polynomial;;

let candle_cv_nf_list_length_def = define
 `(candle_cv_nf_list_length (Cexp_num z) = Cexp_num 0) /\
  (candle_cv_nf_list_length (Cexp_pair h t) =
     Cexp_add (Cexp_num 1) (candle_cv_nf_list_length t))`;;

let candle_cv_nf_list_length_compute = prove
 (`!xs.
     candle_cv_nf_list_length xs =
     Cexp_if (Cexp_ispair xs)
       (Cexp_add (Cexp_num 1) (candle_cv_nf_list_length (Cexp_snd xs)))
       (Cexp_num 0)`,
  MATCH_MP_TAC cval_INDUCT THEN CONJ_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[candle_cv_nf_list_length_def; cexp_if_def;
                cexp_ispair_def; cexp_snd_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[candle_cv_nf_list_length_def; cexp_if_def;
                cexp_ispair_def; cexp_snd_def]]);;

let candle_cv_nf_list_length_correct = prove
 (`!xs:num list.
     candle_cv_nf_list_length (candle_nf_fuel xs) = Cexp_num (LENGTH xs)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_nf_fuel_def; candle_cv_nf_list_length_def; LENGTH];
    ASM_REWRITE_TAC[candle_nf_fuel_def; candle_cv_nf_list_length_def;
                    LENGTH; cexp_add_def; injectivity "cval"] THEN
    ARITH_TAC]);;

let candle_cv_nf_add_power_complete_def = new_definition
 `candle_cv_nf_add_power_complete power_fuel x y =
    Cexp_eq (candle_cv_nf_list_length power_fuel)
      (Cexp_if (Cexp_less (Cexp_snd x) (Cexp_snd y))
        (Cexp_sub (Cexp_snd y) (Cexp_snd x))
        (Cexp_sub (Cexp_snd x) (Cexp_snd y)))`;;

let candle_cv_nf_add_power_complete_correct = prove
 (`!power_fuel x y.
     candle_cv_nf_add_power_complete (candle_nf_fuel power_fuel)
       (candle_nf_pair x) (candle_nf_pair y) =
     Cexp_num
       (if candle_nf_add_power_complete power_fuel x y then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_nf_add_power_complete_def;
              candle_nf_add_power_complete_def;
              candle_cv_nf_list_length_correct; candle_nf_pair_def;
              cexp_snd_def; cexp_less_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_sub_def; cexp_eq_def;
                  injectivity "cval"]);;

let candle_cv_nf_staged_product_valid_def = define
 `(candle_cv_nf_staged_product_valid radix scale limit
      (Cexp_num z) acc = Cexp_num 1) /\
  (candle_cv_nf_staged_product_valid radix scale limit
      (Cexp_pair h t) acc =
     Cexp_if
       (Cexp_less
         (Cexp_add (Cexp_snd acc) (Cexp_snd (Cexp_snd h))) scale)
       (Cexp_num 0)
       (candle_cv_nf_staged_product_valid radix scale limit t
         (candle_cv_nf_scaled_mul_round_hi radix scale limit
           (Cexp_fst h) acc (Cexp_snd h))))`;;

let candle_cv_nf_staged_product_valid_compute = prove
 (`!radix scale limit steps acc.
     candle_cv_nf_staged_product_valid radix scale limit steps acc =
     Cexp_if (Cexp_ispair steps)
       (Cexp_if
         (Cexp_less
           (Cexp_add (Cexp_snd acc)
             (Cexp_snd (Cexp_snd (Cexp_fst steps)))) scale)
         (Cexp_num 0)
         (candle_cv_nf_staged_product_valid radix scale limit
           (Cexp_snd steps)
           (candle_cv_nf_scaled_mul_round_hi radix scale limit
             (Cexp_fst (Cexp_fst steps)) acc
             (Cexp_snd (Cexp_fst steps)))))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `steps:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_staged_product_valid_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_nf_staged_product_valid_correct = prove
 (`!steps radix scale limit acc.
     candle_cv_nf_staged_product_valid
       (Cexp_num radix) (Cexp_num scale) (Cexp_num limit)
       (candle_nf_staged_product_steps steps) (candle_nf_pair acc) =
     Cexp_num
       (if candle_nf_staged_product_valid radix scale limit steps acc
        then SUC 0 else 0)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_product_steps_def;
                candle_nf_staged_product_valid_def;
                candle_cv_nf_staged_product_valid_def] THEN
    NUM_REDUCE_TAC;
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_product_steps_def;
                candle_nf_staged_product_step_def;
                candle_nf_staged_product_valid_def;
                candle_cv_nf_staged_product_valid_def] THEN
    REWRITE_TAC[cexp_fst_def; cexp_snd_def] THEN
    REWRITE_TAC[candle_cv_nf_scaled_mul_round_hi_correct] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[candle_nf_pair_def; cexp_snd_def;
                cexp_add_def; cexp_less_def] THEN
    COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[cexp_if_def; NOT_LT] THEN
      REWRITE_TAC[injectivity "cval"] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[cexp_if_def; NOT_LT] THEN
      REWRITE_TAC[injectivity "cval"] THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let candle_cv_nf_staged_polynomial_valid_def = define
 `(candle_cv_nf_staged_polynomial_valid radix scale limit
      (Cexp_num z) acc = Cexp_num 1) /\
  (candle_cv_nf_staged_polynomial_valid radix scale limit
      (Cexp_pair h t) acc =
     Cexp_if
       (candle_cv_nf_staged_product_valid radix scale limit
         (Cexp_fst h) (Cexp_pair (Cexp_num 1) scale))
       (Cexp_if
         (candle_cv_nf_add_power_complete
           (Cexp_snd (Cexp_snd h)) acc
           (candle_cv_nf_staged_product radix scale limit
             (Cexp_fst h) (Cexp_pair (Cexp_num 1) scale)))
         (candle_cv_nf_staged_polynomial_valid radix scale limit t
           (candle_cv_nf_add_round_hi radix limit
             (Cexp_fst (Cexp_snd h)) (Cexp_snd (Cexp_snd h)) acc
             (candle_cv_nf_staged_product radix scale limit
               (Cexp_fst h) (Cexp_pair (Cexp_num 1) scale))))
         (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_nf_staged_polynomial_valid_compute = prove
 (`!radix scale limit jobs acc.
     candle_cv_nf_staged_polynomial_valid radix scale limit jobs acc =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if
         (candle_cv_nf_staged_product_valid radix scale limit
           (Cexp_fst (Cexp_fst jobs)) (Cexp_pair (Cexp_num 1) scale))
         (Cexp_if
           (candle_cv_nf_add_power_complete
             (Cexp_snd (Cexp_snd (Cexp_fst jobs))) acc
             (candle_cv_nf_staged_product radix scale limit
               (Cexp_fst (Cexp_fst jobs))
               (Cexp_pair (Cexp_num 1) scale)))
           (candle_cv_nf_staged_polynomial_valid radix scale limit
             (Cexp_snd jobs)
             (candle_cv_nf_add_round_hi radix limit
               (Cexp_fst (Cexp_snd (Cexp_fst jobs)))
               (Cexp_snd (Cexp_snd (Cexp_fst jobs))) acc
               (candle_cv_nf_staged_product radix scale limit
                 (Cexp_fst (Cexp_fst jobs))
                 (Cexp_pair (Cexp_num 1) scale))))
           (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_staged_polynomial_valid_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_nf_staged_polynomial_valid_correct = prove
 (`!jobs radix scale limit acc.
     candle_cv_nf_staged_polynomial_valid
       (Cexp_num radix) (Cexp_num scale) (Cexp_num limit)
       (candle_nf_staged_polynomial_jobs jobs) (candle_nf_pair acc) =
     Cexp_num
       (if candle_nf_staged_polynomial_valid radix scale limit jobs acc
        then SUC 0 else 0)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_polynomial_jobs_def;
                candle_nf_staged_polynomial_valid_def;
                candle_cv_nf_staged_polynomial_valid_def] THEN
    NUM_REDUCE_TAC;
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_polynomial_jobs_def;
                candle_nf_staged_polynomial_job_def;
                candle_nf_staged_polynomial_valid_def;
                candle_cv_nf_staged_polynomial_valid_def;
                candle_nf_staged_polynomial_one_rep;
                cexp_fst_def; cexp_snd_def;
                candle_cv_nf_staged_product_valid_correct;
                candle_cv_nf_staged_product_correct;
                candle_cv_nf_add_power_complete_correct;
                candle_cv_nf_add_round_hi_correct] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[cexp_if_def] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[cexp_if_def]]);;

let candle_cv_nf_staged_validity_compute_eqs =
  map SPEC_ALL
   [candle_cv_nf_list_length_compute;
    candle_cv_nf_add_power_complete_def;
    candle_cv_nf_staged_product_valid_compute;
    candle_cv_nf_staged_polynomial_valid_compute] @
  candle_cv_nf_staged_polynomial_compute_eqs;;

end;;
