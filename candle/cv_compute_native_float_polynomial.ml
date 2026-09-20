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

(* A real Flyspeck Taylor batch does not arrive with one common exponent.
   Preserve the complete authenticated (mantissa,exponent) input and align
   every monomial behind the reflected computation. *)

let candle_nf_monomial_mantissa_def = define
 `(candle_nf_monomial_mantissa ([]:(num#num)list) = 1) /\
  (candle_nf_monomial_mantissa (CONS h t) =
     FST h * candle_nf_monomial_mantissa t)`;;

let candle_nf_monomial_exponent_def = define
 `(candle_nf_monomial_exponent ([]:(num#num)list) = 0) /\
  (candle_nf_monomial_exponent (CONS h t) =
     SND h + candle_nf_monomial_exponent t)`;;

let candle_nf_monomial_value_def = new_definition
 `candle_nf_monomial_value radix factors =
    candle_nf_monomial_mantissa factors *
    radix EXP candle_nf_monomial_exponent factors`;;

let candle_nf_polynomial_value_def = define
 `(candle_nf_polynomial_value radix ([]:((num#num)list)list) = 0) /\
  (candle_nf_polynomial_value radix (CONS h t) =
     candle_nf_monomial_value radix h +
     candle_nf_polynomial_value radix t)`;;

let candle_nf_aligned_monomial_def = new_definition
 `candle_nf_aligned_monomial radix target factors =
    candle_nf_monomial_mantissa factors *
    radix EXP (candle_nf_monomial_exponent factors - target)`;;

let candle_nf_aligned_sum_def = define
 `(candle_nf_aligned_sum radix target ([]:((num#num)list)list) = 0) /\
  (candle_nf_aligned_sum radix target (CONS h t) =
     candle_nf_aligned_monomial radix target h +
     candle_nf_aligned_sum radix target t)`;;

let candle_nf_terms_above_def = define
 `(candle_nf_terms_above target ([]:((num#num)list)list) <=> T) /\
  (candle_nf_terms_above target (CONS h t) <=>
     target <= candle_nf_monomial_exponent h /\
     candle_nf_terms_above target t)`;;

let candle_nf_aligned_monomial_value = prove
 (`!radix target factors.
     target <= candle_nf_monomial_exponent factors
     ==> candle_nf_aligned_monomial radix target factors *
         radix EXP target =
         candle_nf_monomial_value radix factors`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_nf_aligned_monomial_def;
              candle_nf_monomial_value_def] THEN
  ONCE_REWRITE_TAC[GSYM MULT_ASSOC] THEN
  MATCH_MP_TAC (MESON[] `b = c ==> a * b = a * c:num`) THEN
  ONCE_REWRITE_TAC[GSYM EXP_ADD] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let candle_nf_aligned_sum_value = prove
 (`!terms radix target.
     candle_nf_terms_above target terms
     ==> candle_nf_aligned_sum radix target terms *
         radix EXP target =
         candle_nf_polynomial_value radix terms`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_nf_terms_above_def; candle_nf_aligned_sum_def;
              candle_nf_polynomial_value_def; MULT_CLAUSES;
              RIGHT_ADD_DISTRIB] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_nf_aligned_monomial_value]);;

let candle_nf_aligned_polynomial_round_hi_def = new_definition
 `candle_nf_aligned_polynomial_round_hi
    radix limit fuel target terms =
      candle_nf_round_hi radix limit fuel
        (candle_nf_aligned_sum radix target terms) target`;;

let candle_nf_aligned_polynomial_round_hi_sound = prove
 (`!fuel radix limit target terms.
     ~(radix = 0) /\ candle_nf_terms_above target terms
     ==> candle_nf_polynomial_value radix terms <=
         FST
           (candle_nf_aligned_polynomial_round_hi
              radix limit fuel target terms) *
         radix EXP
           SND
             (candle_nf_aligned_polynomial_round_hi
                radix limit fuel target terms)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_nf_aligned_polynomial_round_hi_def] THEN
  FIRST_ASSUM (fun th ->
    REWRITE_TAC[GSYM (MATCH_MP candle_nf_aligned_sum_value th)]) THEN
  MATCH_MP_TAC candle_nf_round_hi_sound THEN
  ASM_REWRITE_TAC[]);;

(* Exponent differences are supplied as authenticated unary fuel.  The
   reflected evaluator consumes that fuel, so radix powers and all large
   products/sums remain inside Kernel.compute. *)

let candle_nf_fueled_monomial_def = new_definition
 `candle_nf_fueled_monomial radix (item:num list#num list) =
    candle_nf_product (FST item) * radix EXP LENGTH (SND item)`;;

let candle_nf_fueled_sum_def = define
 `(candle_nf_fueled_sum radix ([]:(num list#num list)list) = 0) /\
  (candle_nf_fueled_sum radix (CONS h t) =
     candle_nf_fueled_monomial radix h +
     candle_nf_fueled_sum radix t)`;;

let candle_nf_fueled_alignment_def = define
 `(candle_nf_fueled_alignment target
      ([]:((num#num)list)list) ([]:(num list#num list)list) <=> T) /\
  (candle_nf_fueled_alignment target [] (CONS item items) <=> F) /\
  (candle_nf_fueled_alignment target (CONS factors terms) [] <=> F) /\
  (candle_nf_fueled_alignment target (CONS factors terms)
      (CONS item items) <=>
     candle_nf_product (FST item) =
       candle_nf_monomial_mantissa factors /\
     LENGTH (SND item) + target =
       candle_nf_monomial_exponent factors /\
     candle_nf_fueled_alignment target terms items)`;;

let candle_nf_fueled_monomial_value = prove
 (`!radix target factors item.
     candle_nf_product (FST item) =
       candle_nf_monomial_mantissa factors /\
     LENGTH (SND item) + target =
       candle_nf_monomial_exponent factors
     ==> candle_nf_fueled_monomial radix item * radix EXP target =
         candle_nf_monomial_value radix factors`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_nf_fueled_monomial_def;
              candle_nf_monomial_value_def] THEN
  ONCE_REWRITE_TAC[GSYM MULT_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM EXP_ADD] THEN
  ASM_REWRITE_TAC[]);;

let candle_nf_fueled_sum_value = prove
 (`!terms items radix target.
     candle_nf_fueled_alignment target terms items
     ==> candle_nf_fueled_sum radix items * radix EXP target =
         candle_nf_polynomial_value radix terms`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `items:(num list#num list)list` list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_nf_fueled_alignment_def;
                candle_nf_fueled_sum_def; candle_nf_polynomial_value_def;
                MULT_CLAUSES];
    REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `items:(num list#num list)list` list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_nf_fueled_alignment_def;
                candle_nf_fueled_sum_def;
                candle_nf_polynomial_value_def;
                RIGHT_ADD_DISTRIB] THEN
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[candle_nf_fueled_monomial_value]]);;

let candle_nf_fueled_polynomial_round_hi_def = new_definition
 `candle_nf_fueled_polynomial_round_hi
    radix limit fuel target items =
      candle_nf_round_hi radix limit fuel
        (candle_nf_fueled_sum radix items) target`;;

let candle_nf_fueled_polynomial_round_hi_sound = prove
 (`!fuel radix limit target terms items.
     ~(radix = 0) /\ candle_nf_fueled_alignment target terms items
     ==> candle_nf_polynomial_value radix terms <=
         FST
           (candle_nf_fueled_polynomial_round_hi
              radix limit fuel target items) *
         radix EXP
           SND
             (candle_nf_fueled_polynomial_round_hi
                radix limit fuel target items)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_nf_fueled_polynomial_round_hi_def] THEN
  FIRST_ASSUM (fun th ->
    REWRITE_TAC[GSYM (MATCH_MP candle_nf_fueled_sum_value th)]) THEN
  MATCH_MP_TAC candle_nf_round_hi_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_nf_fueled_item_def = new_definition
 `candle_nf_fueled_item (item:num list#num list) =
    Cexp_pair (candle_nf_num_list (FST item))
      (candle_nf_fuel (SND item))`;;

let candle_nf_fueled_items_def = define
 `(candle_nf_fueled_items ([]:(num list#num list)list) = Cexp_num 0) /\
  (candle_nf_fueled_items (CONS h t) =
     Cexp_pair (candle_nf_fueled_item h)
       (candle_nf_fueled_items t))`;;

let candle_cv_nf_power_fuel_def = define
 `(candle_cv_nf_power_fuel radix (Cexp_num z) = Cexp_num 1) /\
  (candle_cv_nf_power_fuel radix (Cexp_pair h t) =
     Cexp_mul radix (candle_cv_nf_power_fuel radix t))`;;

let candle_cv_nf_fueled_monomial_def = new_definition
 `candle_cv_nf_fueled_monomial radix item =
    Cexp_mul (candle_cv_nf_product (Cexp_fst item))
      (candle_cv_nf_power_fuel radix (Cexp_snd item))`;;

let candle_cv_nf_fueled_sum_def = define
 `(candle_cv_nf_fueled_sum radix (Cexp_num z) = Cexp_num 0) /\
  (candle_cv_nf_fueled_sum radix (Cexp_pair h t) =
     Cexp_add (candle_cv_nf_fueled_monomial radix h)
       (candle_cv_nf_fueled_sum radix t))`;;

let candle_cv_nf_fueled_polynomial_round_hi_def = new_definition
 `candle_cv_nf_fueled_polynomial_round_hi
    radix limit fuel target items =
      candle_cv_nf_round_hi radix limit fuel
        (candle_cv_nf_fueled_sum radix items) target`;;

let candle_cv_nf_power_fuel_compute = prove
 (`!radix fuel.
     candle_cv_nf_power_fuel radix fuel =
     Cexp_if (Cexp_ispair fuel)
       (Cexp_mul radix
         (candle_cv_nf_power_fuel radix (Cexp_snd fuel)))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `fuel:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_power_fuel_def; cexp_if_def;
              cexp_snd_def; cexp_ispair_def]);;

let candle_cv_nf_fueled_sum_compute = prove
 (`!radix items.
     candle_cv_nf_fueled_sum radix items =
     Cexp_if (Cexp_ispair items)
       (Cexp_add
         (candle_cv_nf_fueled_monomial radix (Cexp_fst items))
         (candle_cv_nf_fueled_sum radix (Cexp_snd items)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_fueled_sum_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_nf_power_fuel_correct = prove
 (`!fuel radix.
     candle_cv_nf_power_fuel (Cexp_num radix) (candle_nf_fuel fuel) =
     Cexp_num (radix EXP LENGTH fuel)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_nf_fuel_def; candle_cv_nf_power_fuel_def;
                  LENGTH; EXP; cexp_mul_def]);;

let candle_cv_nf_fueled_monomial_correct = prove
 (`!radix item.
     candle_cv_nf_fueled_monomial (Cexp_num radix)
       (candle_nf_fueled_item item) =
     Cexp_num (candle_nf_fueled_monomial radix item)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_nf_fueled_monomial_def;
              candle_nf_fueled_item_def;
              candle_nf_fueled_monomial_def;
              cexp_fst_def; cexp_snd_def;
              candle_cv_nf_product_correct;
              candle_cv_nf_power_fuel_correct; cexp_mul_def]);;

let candle_cv_nf_fueled_sum_correct = prove
 (`!items radix.
     candle_cv_nf_fueled_sum (Cexp_num radix)
       (candle_nf_fueled_items items) =
     Cexp_num (candle_nf_fueled_sum radix items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_nf_fueled_items_def; candle_nf_fueled_sum_def;
                  candle_cv_nf_fueled_sum_def;
                  candle_cv_nf_fueled_monomial_correct; cexp_add_def]);;

let candle_cv_nf_fueled_polynomial_round_hi_correct = prove
 (`!fuel radix limit target items.
     candle_cv_nf_fueled_polynomial_round_hi
       (Cexp_num radix) (Cexp_num limit) (candle_nf_fuel fuel)
       (Cexp_num target) (candle_nf_fueled_items items) =
     candle_nf_pair
       (candle_nf_fueled_polynomial_round_hi
          radix limit fuel target items)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_nf_fueled_polynomial_round_hi_def;
              candle_nf_fueled_polynomial_round_hi_def;
              candle_cv_nf_fueled_sum_correct;
              candle_cv_nf_round_hi_correct]);;

let candle_cv_nf_fueled_polynomial_compute_eqs =
  map SPEC_ALL
   [candle_cv_nf_product_compute;
    candle_cv_nf_power_fuel_compute;
    candle_cv_nf_fueled_monomial_def;
    candle_cv_nf_fueled_sum_compute;
    candle_cv_nf_fueled_polynomial_round_hi_def;
    candle_cv_nf_round_hi_compute];;

end;;
