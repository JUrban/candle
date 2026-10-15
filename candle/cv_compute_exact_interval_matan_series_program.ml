(* ========================================================================== *)
(* Reflected exact-rational program for the crossing-zero [matan] packet.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The analytic contracts live in the stable     *)
(* [cv_compute_exact_interval_matan_series.ml] layer.  This separate file     *)
(* implements the corresponding cval program and proves representation       *)
(* correctness, so program edits can be tested without rebuilding that       *)
(* analytic prerequisite.                                                     *)
(* ========================================================================== *)

(* Loaded after the stable analytic-jet checkpoint and
   [cv_compute_exact_interval_matan_series.ml]. *)

module Candle_cv_exact_interval_matan_series_program = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_inv;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_rational_normalize;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_square_core;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_exact_interval_matan_series;;

(* Literal cval coefficients. *)

let candle_cv_q_matan_zero_def = new_definition
 `candle_cv_q_matan_zero = candle_cv_q candle_q_matan_zero`;;
let candle_cv_q_matan_one_def = new_definition
 `candle_cv_q_matan_one = candle_cv_q candle_q_matan_one`;;
let candle_cv_q_matan_third_def = new_definition
 `candle_cv_q_matan_third = candle_cv_q candle_q_matan_third`;;
let candle_cv_q_matan_fifth_def = new_definition
 `candle_cv_q_matan_fifth = candle_cv_q candle_q_matan_fifth`;;
let candle_cv_q_matan_two_fifths_def = new_definition
 `candle_cv_q_matan_two_fifths = candle_cv_q candle_q_matan_two_fifths`;;
let candle_cv_q_matan_two_def = new_definition
 `candle_cv_q_matan_two = candle_cv_q candle_q_matan_two`;;
let candle_cv_q_matan_seven_def = new_definition
 `candle_cv_q_matan_seven = candle_cv_q candle_q_matan_seven`;;
let candle_cv_q_matan_nine_tenths_def = new_definition
 `candle_cv_q_matan_nine_tenths =
    candle_cv_q candle_q_matan_nine_tenths`;;
let candle_cv_q_matan_neg_one_fifth_def = new_definition
 `candle_cv_q_matan_neg_one_fifth =
    candle_cv_q candle_q_matan_neg_one_fifth`;;
let candle_cv_q_matan_thirteen_twentieths_def = new_definition
 `candle_cv_q_matan_thirteen_twentieths =
    candle_cv_q candle_q_matan_thirteen_twentieths`;;

let candle_cv_q_matan_literal_compute ordinary_def reflected_def =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[ordinary_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    reflected_def;;

let candle_cv_q_matan_zero_compute =
  candle_cv_q_matan_literal_compute
    candle_q_matan_zero_def candle_cv_q_matan_zero_def;;
let candle_cv_q_matan_one_compute =
  candle_cv_q_matan_literal_compute
    candle_q_matan_one_def candle_cv_q_matan_one_def;;
let candle_cv_q_matan_third_compute =
  candle_cv_q_matan_literal_compute
    candle_q_matan_third_def candle_cv_q_matan_third_def;;
let candle_cv_q_matan_fifth_compute =
  candle_cv_q_matan_literal_compute
    candle_q_matan_fifth_def candle_cv_q_matan_fifth_def;;
let candle_cv_q_matan_two_fifths_compute =
  candle_cv_q_matan_literal_compute
    candle_q_matan_two_fifths_def candle_cv_q_matan_two_fifths_def;;
let candle_cv_q_matan_two_compute =
  candle_cv_q_matan_literal_compute
    candle_q_matan_two_def candle_cv_q_matan_two_def;;
let candle_cv_q_matan_seven_compute =
  candle_cv_q_matan_literal_compute
    candle_q_matan_seven_def candle_cv_q_matan_seven_def;;
let candle_cv_q_matan_nine_tenths_compute =
  candle_cv_q_matan_literal_compute
    candle_q_matan_nine_tenths_def candle_cv_q_matan_nine_tenths_def;;
let candle_cv_q_matan_neg_one_fifth_compute =
  candle_cv_q_matan_literal_compute
    candle_q_matan_neg_one_fifth_def candle_cv_q_matan_neg_one_fifth_def;;
let candle_cv_q_matan_thirteen_twentieths_compute =
  candle_cv_q_matan_literal_compute
    candle_q_matan_thirteen_twentieths_def
    candle_cv_q_matan_thirteen_twentieths_def;;

(* Exact reflected preparation and interval results. *)

let candle_cv_q_matan_const_interval_def = new_definition
 `candle_cv_q_matan_const_interval q = Cexp_pair q q`;;

let candle_cv_q_matan_abs_upper_def = new_definition
 `candle_cv_q_matan_abs_upper input =
    candle_cv_q_max (Cexp_snd input)
      (candle_cv_q_neg (Cexp_fst input))`;;

let candle_cv_q_matan_u2_def = new_definition
 `candle_cv_q_matan_u2 input =
    candle_cv_q_mul_normalized
      (candle_cv_q_matan_abs_upper input)
      (candle_cv_q_matan_abs_upper input)`;;

let candle_cv_q_matan_u3_def = new_definition
 `candle_cv_q_matan_u3 input =
    candle_cv_q_mul_normalized
      (candle_cv_q_matan_u2 input)
      (candle_cv_q_matan_abs_upper input)`;;

let candle_cv_q_matan_r1_def = new_definition
 `candle_cv_q_matan_r1 input =
    candle_cv_q_add_normalized candle_cv_q_matan_one
      (candle_cv_q_neg (candle_cv_q_matan_abs_upper input))`;;

let candle_cv_q_matan_value_r2_def = new_definition
 `candle_cv_q_matan_value_r2 input =
    candle_cv_q_mul_normalized candle_cv_q_matan_seven
      (candle_cv_q_matan_r1 input)`;;

let candle_cv_q_matan_derivative_r2_def = new_definition
 `candle_cv_q_matan_derivative_r2 input =
    candle_cv_q_mul_normalized candle_cv_q_matan_two
      (candle_cv_q_matan_r1 input)`;;

let candle_cv_q_matan_value_error_def = new_definition
 `candle_cv_q_matan_value_error input =
    candle_cv_q_mul_normalized (candle_cv_q_matan_u3 input)
      (candle_cv_q_inv (candle_cv_q_matan_value_r2 input))`;;

let candle_cv_q_matan_derivative_error_def = new_definition
 `candle_cv_q_matan_derivative_error input =
    candle_cv_q_mul_normalized (candle_cv_q_matan_u2 input)
      (candle_cv_q_inv (candle_cv_q_matan_derivative_r2 input))`;;

let candle_cv_q_matan_value_poly_def = new_definition
 `candle_cv_q_matan_value_poly input =
    let x2 = candle_cv_q_interval_normalize
      (candle_cv_q_interval_square input) in
    candle_cv_q_interval_add_normalized
      (candle_cv_q_interval_add_normalized
        (candle_cv_q_matan_const_interval candle_cv_q_matan_one)
        (candle_cv_q_interval_mul_normalized
          (candle_cv_q_matan_const_interval
            (candle_cv_q_neg candle_cv_q_matan_third)) input))
      (candle_cv_q_interval_mul_normalized
        (candle_cv_q_matan_const_interval candle_cv_q_matan_fifth) x2)`;;

let candle_cv_q_matan_value_poly_compute =
  REWRITE_RULE[LET_DEF; LET_END_DEF] candle_cv_q_matan_value_poly_def;;

let candle_cv_q_matan_derivative_poly_def = new_definition
 `candle_cv_q_matan_derivative_poly input =
    candle_cv_q_interval_add_normalized
      (candle_cv_q_matan_const_interval
        (candle_cv_q_neg candle_cv_q_matan_third))
      (candle_cv_q_interval_mul_normalized
        (candle_cv_q_matan_const_interval candle_cv_q_matan_two_fifths)
        input)`;;

let candle_cv_q_matan_expand_error_def = new_definition
 `candle_cv_q_matan_expand_error bounds error =
    Cexp_pair
      (candle_cv_q_add_normalized (Cexp_fst bounds)
        (candle_cv_q_neg error))
      (candle_cv_q_add_normalized (Cexp_snd bounds) error)`;;

let candle_cv_q_interval_matan_series_def = new_definition
 `candle_cv_q_interval_matan_series input =
    candle_cv_q_matan_expand_error
      (candle_cv_q_matan_value_poly input)
      (candle_cv_q_matan_value_error input)`;;

let candle_cv_q_interval_dmatan_series_def = new_definition
 `candle_cv_q_interval_dmatan_series input =
    candle_cv_q_matan_expand_error
      (candle_cv_q_matan_derivative_poly input)
      (candle_cv_q_matan_derivative_error input)`;;

let candle_cv_q_interval_ddmatan_series_def = new_definition
 `candle_cv_q_interval_ddmatan_series (input:cval) =
    Cexp_pair
      (candle_cv_q_neg candle_cv_q_matan_thirteen_twentieths)
      candle_cv_q_matan_thirteen_twentieths`;;

(* A total cval Boolean for the exact numerator comparison. *)

let candle_cv_q_nonzero_flag_def = new_definition
 `candle_cv_q_nonzero_flag q =
    Cexp_if
      (Cexp_eq (Cexp_fst (Cexp_fst q)) (Cexp_snd (Cexp_fst q)))
      (Cexp_num 0) (Cexp_num 1)`;;

let candle_cv_q_interval_matan_series_domain_def = new_definition
 `candle_cv_q_interval_matan_series_domain input =
    Cexp_if (candle_cv_q_le (Cexp_fst input) (Cexp_snd input))
      (Cexp_if
        (candle_cv_q_le candle_cv_q_matan_neg_one_fifth
          (Cexp_fst input))
        (Cexp_if
          (candle_cv_q_le (candle_cv_q_matan_abs_upper input)
            candle_cv_q_matan_nine_tenths)
          (Cexp_if
            (candle_cv_q_nonzero_flag
              (candle_cv_q_matan_value_r2 input))
            (Cexp_if
              (candle_cv_q_nonzero_flag
                (candle_cv_q_matan_derivative_r2 input))
              (Cexp_num 1) (Cexp_num 0))
            (Cexp_num 0))
          (Cexp_num 0))
        (Cexp_num 0))
      (Cexp_num 0)`;;

let candle_cv_q_matan_series_compute_eqs =
  candle_cv_q_interval_square_compute_eqs @
  candle_cv_q_normalized_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_inv_def;
    candle_cv_q_interval_add_normalized_def;
    candle_cv_q_interval_mul_normalized_def;
    candle_cv_q_matan_zero_compute;
    candle_cv_q_matan_one_compute;
    candle_cv_q_matan_third_compute;
    candle_cv_q_matan_fifth_compute;
    candle_cv_q_matan_two_fifths_compute;
    candle_cv_q_matan_two_compute;
    candle_cv_q_matan_seven_compute;
    candle_cv_q_matan_nine_tenths_compute;
    candle_cv_q_matan_neg_one_fifth_compute;
    candle_cv_q_matan_thirteen_twentieths_compute;
    candle_cv_q_matan_const_interval_def;
    candle_cv_q_matan_abs_upper_def;
    candle_cv_q_matan_u2_def;
    candle_cv_q_matan_u3_def;
    candle_cv_q_matan_r1_def;
    candle_cv_q_matan_value_r2_def;
    candle_cv_q_matan_derivative_r2_def;
    candle_cv_q_matan_value_error_def;
    candle_cv_q_matan_derivative_error_def;
    candle_cv_q_matan_value_poly_compute;
    candle_cv_q_matan_derivative_poly_def;
    candle_cv_q_matan_expand_error_def;
    candle_cv_q_interval_matan_series_def;
    candle_cv_q_interval_dmatan_series_def;
    candle_cv_q_interval_ddmatan_series_def;
    candle_cv_q_nonzero_flag_def;
    candle_cv_q_interval_matan_series_domain_def];;

(* Representation correctness. *)

let candle_cv_q_matan_const_interval_correct = prove
 (`!q.
    candle_cv_q_matan_const_interval (candle_cv_q q) =
    candle_cv_q_interval (candle_q_matan_const_interval q)`,
  REWRITE_TAC[candle_cv_q_matan_const_interval_def;
              candle_q_matan_const_interval_def;
              candle_cv_q_interval_def; FST; SND]);;

let candle_cv_q_matan_abs_upper_correct = prove
 (`!input.
    candle_cv_q_matan_abs_upper (candle_cv_q_interval input) =
    candle_cv_q (candle_q_matan_abs_upper input)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_matan_abs_upper_def;
              candle_q_matan_abs_upper_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_neg_correct; candle_cv_q_max_correct]);;

let candle_cv_q_matan_u2_correct = prove
 (`!input.
    candle_cv_q_matan_u2 (candle_cv_q_interval input) =
    candle_cv_q (candle_q_matan_u2 input)`,
  REWRITE_TAC[candle_cv_q_matan_u2_def; candle_q_matan_u2_def;
              candle_cv_q_matan_abs_upper_correct;
              candle_cv_q_mul_normalized_correct]);;

let candle_cv_q_matan_u3_correct = prove
 (`!input.
    candle_cv_q_matan_u3 (candle_cv_q_interval input) =
    candle_cv_q (candle_q_matan_u3 input)`,
  REWRITE_TAC[candle_cv_q_matan_u3_def; candle_q_matan_u3_def;
              candle_cv_q_matan_u2_correct;
              candle_cv_q_matan_abs_upper_correct;
              candle_cv_q_mul_normalized_correct]);;

let candle_cv_q_matan_r1_correct = prove
 (`!input.
    candle_cv_q_matan_r1 (candle_cv_q_interval input) =
    candle_cv_q (candle_q_matan_r1 input)`,
  REWRITE_TAC[candle_cv_q_matan_r1_def; candle_q_matan_r1_def;
              candle_cv_q_matan_one_def;
              candle_cv_q_matan_abs_upper_correct;
              candle_cv_q_neg_correct;
              candle_cv_q_add_normalized_correct]);;

let candle_cv_q_matan_value_r2_correct = prove
 (`!input.
    candle_cv_q_matan_value_r2 (candle_cv_q_interval input) =
    candle_cv_q (candle_q_matan_value_r2 input)`,
  REWRITE_TAC[candle_cv_q_matan_value_r2_def;
              candle_q_matan_value_r2_def;
              candle_cv_q_matan_seven_def;
              candle_cv_q_matan_r1_correct;
              candle_cv_q_mul_normalized_correct]);;

let candle_cv_q_matan_derivative_r2_correct = prove
 (`!input.
    candle_cv_q_matan_derivative_r2 (candle_cv_q_interval input) =
    candle_cv_q (candle_q_matan_derivative_r2 input)`,
  REWRITE_TAC[candle_cv_q_matan_derivative_r2_def;
              candle_q_matan_derivative_r2_def;
              candle_cv_q_matan_two_def;
              candle_cv_q_matan_r1_correct;
              candle_cv_q_mul_normalized_correct]);;

let candle_cv_q_matan_value_error_correct = prove
 (`!input.
    candle_cv_q_matan_value_error (candle_cv_q_interval input) =
    candle_cv_q (candle_q_matan_value_error input)`,
  REWRITE_TAC[candle_cv_q_matan_value_error_def;
              candle_q_matan_value_error_def;
              candle_cv_q_matan_u3_correct;
              candle_cv_q_matan_value_r2_correct;
              candle_cv_q_inv_correct;
              candle_cv_q_mul_normalized_correct]);;

let candle_cv_q_matan_derivative_error_correct = prove
 (`!input.
    candle_cv_q_matan_derivative_error (candle_cv_q_interval input) =
    candle_cv_q (candle_q_matan_derivative_error input)`,
  REWRITE_TAC[candle_cv_q_matan_derivative_error_def;
              candle_q_matan_derivative_error_def;
              candle_cv_q_matan_u2_correct;
              candle_cv_q_matan_derivative_r2_correct;
              candle_cv_q_inv_correct;
              candle_cv_q_mul_normalized_correct]);;

let candle_cv_q_matan_value_poly_correct = prove
 (`!input.
    candle_cv_q_matan_value_poly (candle_cv_q_interval input) =
    candle_cv_q_interval (candle_q_matan_value_poly input)`,
  REWRITE_TAC[candle_cv_q_matan_value_poly_def;
              candle_q_matan_value_poly_def; LET_DEF; LET_END_DEF;
              candle_cv_q_interval_square_correct;
              candle_cv_q_interval_normalize_correct;
              candle_cv_q_matan_const_interval_correct;
              candle_cv_q_matan_one_def; candle_cv_q_matan_third_def;
              candle_cv_q_matan_fifth_def;
              candle_cv_q_neg_correct;
              candle_cv_q_interval_mul_normalized_correct;
              candle_cv_q_interval_add_normalized_correct]);;

let candle_cv_q_matan_derivative_poly_correct = prove
 (`!input.
    candle_cv_q_matan_derivative_poly (candle_cv_q_interval input) =
    candle_cv_q_interval (candle_q_matan_derivative_poly input)`,
  REWRITE_TAC[candle_cv_q_matan_derivative_poly_def;
              candle_q_matan_derivative_poly_def;
              candle_cv_q_matan_const_interval_correct;
              candle_cv_q_matan_third_def;
              candle_cv_q_matan_two_fifths_def;
              candle_cv_q_neg_correct;
              candle_cv_q_interval_mul_normalized_correct;
              candle_cv_q_interval_add_normalized_correct]);;

let candle_cv_q_matan_expand_error_correct = prove
 (`!bounds error.
    candle_cv_q_matan_expand_error
      (candle_cv_q_interval bounds) (candle_cv_q error) =
    candle_cv_q_interval (candle_q_matan_expand_error bounds error)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_matan_expand_error_def;
              candle_q_matan_expand_error_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_neg_correct;
              candle_cv_q_add_normalized_correct]);;

let candle_cv_q_interval_matan_series_correct = prove
 (`!input.
    candle_cv_q_interval_matan_series (candle_cv_q_interval input) =
    candle_cv_q_interval (candle_q_interval_matan_series input)`,
  REWRITE_TAC[candle_cv_q_interval_matan_series_def;
              candle_q_interval_matan_series_def;
              candle_cv_q_matan_value_poly_correct;
              candle_cv_q_matan_value_error_correct;
              candle_cv_q_matan_expand_error_correct]);;

let candle_cv_q_interval_dmatan_series_correct = prove
 (`!input.
    candle_cv_q_interval_dmatan_series (candle_cv_q_interval input) =
    candle_cv_q_interval (candle_q_interval_dmatan_series input)`,
  REWRITE_TAC[candle_cv_q_interval_dmatan_series_def;
              candle_q_interval_dmatan_series_def;
              candle_cv_q_matan_derivative_poly_correct;
              candle_cv_q_matan_derivative_error_correct;
              candle_cv_q_matan_expand_error_correct]);;

let candle_cv_q_interval_ddmatan_series_correct = prove
 (`!input.
    candle_cv_q_interval_ddmatan_series (candle_cv_q_interval input) =
    candle_cv_q_interval (candle_q_interval_ddmatan_series input)`,
  REWRITE_TAC[candle_cv_q_interval_ddmatan_series_def;
              candle_q_interval_ddmatan_series_def;
              candle_cv_q_matan_thirteen_twentieths_def;
              candle_cv_q_neg_correct;
              candle_cv_q_interval_def; FST; SND]);;

let candle_cv_q_nonzero_flag_correct = prove
 (`!q.
    candle_cv_q_nonzero_flag (candle_cv_q q) =
    Cexp_num (if candle_q_nonzero q then SUC 0 else 0)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_nonzero_flag_def; candle_q_nonzero_def;
              candle_cv_q_def; candle_cv_lc_z_def;
              cexp_fst_def; cexp_snd_def; cexp_eq_def; FST; SND;
              injectivity "cval"] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; injectivity "cval"] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_interval_matan_series_domain_correct = prove
 (`!input.
    candle_cv_q_interval_matan_series_domain
      (candle_cv_q_interval input) =
    Cexp_num
      (if candle_q_interval_matan_series_domain input then 1 else 0)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_matan_series_domain_def;
              candle_q_interval_matan_series_domain_def;
              candle_cv_q_matan_abs_upper_correct;
              candle_cv_q_matan_value_r2_correct;
              candle_cv_q_matan_derivative_r2_correct;
              candle_cv_q_nonzero_flag_correct] THEN
  REWRITE_TAC[candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_matan_neg_one_fifth_def;
              candle_cv_q_matan_nine_tenths_def;
              candle_cv_q_le_correct] THEN
  ASM_CASES_TAC `candle_q_le (FST input) (SND input)` THEN
  ASM_CASES_TAC
    `candle_q_le candle_q_matan_neg_one_fifth
       (FST (input:(((num#num)#num)#((num#num)#num))))` THEN
  ASM_CASES_TAC
    `candle_q_le (candle_q_matan_abs_upper input)
       candle_q_matan_nine_tenths` THEN
  ASM_CASES_TAC
    `candle_q_nonzero (candle_q_matan_value_r2 input)` THEN
  ASM_CASES_TAC
    `candle_q_nonzero (candle_q_matan_derivative_r2 input)` THEN
  ASM_REWRITE_TAC[cexp_if_def]);;

end;;
