(* ========================================================================== *)
(* Coarse reflected nonnegative polynomial evaluation and directed rounding.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. A list of monomials is evaluated exactly and   *)
(* rounded upward once behind one Kernel.compute call. This is the arithmetic *)
(* batch needed by Flyspeck's Taylor first/second-derivative error sums after  *)
(* their radix exponents have been aligned to one authenticated scale.         *)
(* ========================================================================== *)

needs "candle/cv_compute_native_float_core.ml";;

module Candle_cv_native_float_polynomial = struct

open Candle_cv_native_float_core;;

let candle_nf_num_list_def = define
 `(candle_nf_num_list ([]:num list) = Cexp_num 0) /\
  (candle_nf_num_list (CONS h t) =
     Cexp_pair (Cexp_num h) (candle_nf_num_list t))`;;

let candle_nf_num_lists_def = define
 `(candle_nf_num_lists ([]:(num list)list) = Cexp_num 0) /\
  (candle_nf_num_lists (CONS h t) =
     Cexp_pair (candle_nf_num_list h) (candle_nf_num_lists t))`;;

let candle_nf_product_def = define
 `(candle_nf_product ([]:num list) = 1) /\
  (candle_nf_product (CONS h t) = h * candle_nf_product t)`;;

let candle_nf_sum_products_def = define
 `(candle_nf_sum_products ([]:(num list)list) = 0) /\
  (candle_nf_sum_products (CONS h t) =
     candle_nf_product h + candle_nf_sum_products t)`;;

let candle_nf_polynomial_round_hi_def = new_definition
 `candle_nf_polynomial_round_hi radix limit fuel exponent terms =
    candle_nf_round_hi radix limit fuel
      (candle_nf_sum_products terms) exponent`;;

let candle_nf_polynomial_round_hi_sound = prove
 (`!fuel radix limit exponent terms. ~(radix = 0)
     ==> candle_nf_sum_products terms * radix EXP exponent <=
         FST
           (candle_nf_polynomial_round_hi
              radix limit fuel exponent terms) *
         radix EXP
           SND
             (candle_nf_polynomial_round_hi
                radix limit fuel exponent terms)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_nf_polynomial_round_hi_def] THEN
  MATCH_MP_TAC candle_nf_round_hi_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_nf_product_def = define
 `(candle_cv_nf_product (Cexp_num z) = Cexp_num 1) /\
  (candle_cv_nf_product (Cexp_pair h t) =
     Cexp_mul h (candle_cv_nf_product t))`;;

let candle_cv_nf_sum_products_def = define
 `(candle_cv_nf_sum_products (Cexp_num z) = Cexp_num 0) /\
  (candle_cv_nf_sum_products (Cexp_pair h t) =
     Cexp_add (candle_cv_nf_product h)
       (candle_cv_nf_sum_products t))`;;

let candle_cv_nf_polynomial_round_hi_def = new_definition
 `candle_cv_nf_polynomial_round_hi radix limit fuel exponent terms =
    candle_cv_nf_round_hi radix limit fuel
      (candle_cv_nf_sum_products terms) exponent`;;

let candle_cv_nf_product_compute = prove
 (`!xs.
     candle_cv_nf_product xs =
     Cexp_if (Cexp_ispair xs)
       (Cexp_mul (Cexp_fst xs)
         (candle_cv_nf_product (Cexp_snd xs)))
       (Cexp_num 1)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_product_def; cexp_if_def; cexp_fst_def;
              cexp_snd_def; cexp_ispair_def]);;

let candle_cv_nf_sum_products_compute = prove
 (`!terms.
     candle_cv_nf_sum_products terms =
     Cexp_if (Cexp_ispair terms)
       (Cexp_add (candle_cv_nf_product (Cexp_fst terms))
         (candle_cv_nf_sum_products (Cexp_snd terms)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `terms:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_sum_products_def; cexp_if_def; cexp_fst_def;
              cexp_snd_def; cexp_ispair_def]);;

let candle_cv_nf_product_correct = prove
 (`!xs:num list.
     candle_cv_nf_product (candle_nf_num_list xs) =
     Cexp_num (candle_nf_product xs)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_nf_num_list_def; candle_nf_product_def;
                  candle_cv_nf_product_def; cexp_mul_def]);;

let candle_cv_nf_sum_products_correct = prove
 (`!terms:(num list)list.
     candle_cv_nf_sum_products (candle_nf_num_lists terms) =
     Cexp_num (candle_nf_sum_products terms)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_nf_num_lists_def; candle_nf_sum_products_def;
                  candle_cv_nf_sum_products_def;
                  candle_cv_nf_product_correct; cexp_add_def]);;

let candle_cv_nf_polynomial_round_hi_correct = prove
 (`!fuel radix limit exponent terms.
     candle_cv_nf_polynomial_round_hi
       (Cexp_num radix) (Cexp_num limit) (candle_nf_fuel fuel)
       (Cexp_num exponent) (candle_nf_num_lists terms) =
     candle_nf_pair
       (candle_nf_polynomial_round_hi
          radix limit fuel exponent terms)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_nf_polynomial_round_hi_def;
              candle_nf_polynomial_round_hi_def;
              candle_cv_nf_sum_products_correct;
              candle_cv_nf_round_hi_correct]);;

let candle_cv_nf_polynomial_compute_eqs =
  map SPEC_ALL
   [candle_cv_nf_product_compute;
    candle_cv_nf_sum_products_compute;
    candle_cv_nf_polynomial_round_hi_def;
    candle_cv_nf_round_hi_compute];;

end;;
