(* ========================================================================== *)
(* Exact reflected interval data for the crossing-zero branch of [matan].    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This layer deliberately reuses Flyspeck's    *)
(* existing proved [matan], [dmatan], and [ddmatan] interval contracts.  It  *)
(* replaces their floating endpoint preparation by exact rational data, but  *)
(* does not introduce a second analytic argument.                             *)
(* ========================================================================== *)

(* Loaded after the stable analytic-jet and Flyspeck [matan_eval] checkpoint
   prerequisites.  Source-manifest registration is deferred until this
   focused proof packet is complete. *)

module Candle_cv_exact_interval_matan_series = struct

open Interval_arith;;
open Matan;;
open Matan_eval;;
open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_inv;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_rational_normalize;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_square_core;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;

let candle_q_matan_zero_def = new_definition
 `candle_q_matan_zero = (((0,0),0):(num#num)#num)`;;

let candle_q_matan_one_def = new_definition
 `candle_q_matan_one = (((1,0),0):(num#num)#num)`;;

let candle_q_matan_third_def = new_definition
 `candle_q_matan_third = (((1,0),2):(num#num)#num)`;;

let candle_q_matan_fifth_def = new_definition
 `candle_q_matan_fifth = (((1,0),4):(num#num)#num)`;;

let candle_q_matan_two_fifths_def = new_definition
 `candle_q_matan_two_fifths = (((2,0),4):(num#num)#num)`;;

let candle_q_matan_two_def = new_definition
 `candle_q_matan_two = (((2,0),0):(num#num)#num)`;;

let candle_q_matan_seven_def = new_definition
 `candle_q_matan_seven = (((7,0),0):(num#num)#num)`;;

let candle_q_matan_nine_tenths_def = new_definition
 `candle_q_matan_nine_tenths = (((9,0),9):(num#num)#num)`;;

let candle_q_matan_neg_one_fifth_def = new_definition
 `candle_q_matan_neg_one_fifth = (((0,1),4):(num#num)#num)`;;

let candle_q_matan_thirteen_twentieths_def = new_definition
 `candle_q_matan_thirteen_twentieths = (((13,0),19):(num#num)#num)`;;

let candle_q_matan_const_interval_def = new_definition
 `candle_q_matan_const_interval q =
    (q,q):(((num#num)#num)#((num#num)#num))`;;

let candle_q_matan_abs_upper_def = new_definition
 `candle_q_matan_abs_upper
    (input:(((num#num)#num)#((num#num)#num))) =
    candle_q_max (SND input) (candle_q_neg (FST input))`;;

let candle_q_matan_u2_def = new_definition
 `candle_q_matan_u2 input =
    candle_q_mul_normalized
      (candle_q_matan_abs_upper input)
      (candle_q_matan_abs_upper input)`;;

let candle_q_matan_u3_def = new_definition
 `candle_q_matan_u3 input =
    candle_q_mul_normalized
      (candle_q_matan_u2 input)
      (candle_q_matan_abs_upper input)`;;

let candle_q_matan_r1_def = new_definition
 `candle_q_matan_r1 input =
    candle_q_add_normalized candle_q_matan_one
      (candle_q_neg (candle_q_matan_abs_upper input))`;;

let candle_q_matan_value_r2_def = new_definition
 `candle_q_matan_value_r2 input =
    candle_q_mul_normalized candle_q_matan_seven
      (candle_q_matan_r1 input)`;;

let candle_q_matan_derivative_r2_def = new_definition
 `candle_q_matan_derivative_r2 input =
    candle_q_mul_normalized candle_q_matan_two
      (candle_q_matan_r1 input)`;;

let candle_q_matan_value_error_def = new_definition
 `candle_q_matan_value_error input =
    candle_q_mul_normalized (candle_q_matan_u3 input)
      (candle_q_inv (candle_q_matan_value_r2 input))`;;

let candle_q_matan_derivative_error_def = new_definition
 `candle_q_matan_derivative_error input =
    candle_q_mul_normalized (candle_q_matan_u2 input)
      (candle_q_inv (candle_q_matan_derivative_r2 input))`;;

let candle_q_matan_value_poly_def = new_definition
 `candle_q_matan_value_poly input =
    let x2 = candle_q_interval_normalize
      (candle_q_interval_square input) in
    candle_q_interval_add_normalized
      (candle_q_interval_add_normalized
        (candle_q_matan_const_interval candle_q_matan_one)
        (candle_q_interval_mul_normalized
          (candle_q_matan_const_interval
            (candle_q_neg candle_q_matan_third)) input))
      (candle_q_interval_mul_normalized
        (candle_q_matan_const_interval candle_q_matan_fifth) x2)`;;

let candle_q_matan_derivative_poly_def = new_definition
 `candle_q_matan_derivative_poly input =
    candle_q_interval_add_normalized
      (candle_q_matan_const_interval
        (candle_q_neg candle_q_matan_third))
      (candle_q_interval_mul_normalized
        (candle_q_matan_const_interval candle_q_matan_two_fifths)
        input)`;;

let candle_q_matan_expand_error_def = new_definition
 `candle_q_matan_expand_error
    (bounds:(((num#num)#num)#((num#num)#num)))
    (error:(num#num)#num) =
    (candle_q_add_normalized (FST bounds) (candle_q_neg error),
     candle_q_add_normalized (SND bounds) error)`;;

let candle_q_interval_matan_series_def = new_definition
 `candle_q_interval_matan_series input =
    candle_q_matan_expand_error
      (candle_q_matan_value_poly input)
      (candle_q_matan_value_error input)`;;

let candle_q_interval_dmatan_series_def = new_definition
 `candle_q_interval_dmatan_series input =
    candle_q_matan_expand_error
      (candle_q_matan_derivative_poly input)
      (candle_q_matan_derivative_error input)`;;

let candle_q_interval_ddmatan_series_def = new_definition
 `candle_q_interval_ddmatan_series
    (input:(((num#num)#num)#((num#num)#num))) =
    (candle_q_neg candle_q_matan_thirteen_twentieths,
     candle_q_matan_thirteen_twentieths)`;;

let candle_q_interval_matan_series_domain_def = new_definition
 `candle_q_interval_matan_series_domain input <=>
    candle_q_le (FST input) (SND input) /\
    candle_q_le candle_q_matan_neg_one_fifth (FST input) /\
    candle_q_le (candle_q_matan_abs_upper input)
      candle_q_matan_nine_tenths /\
    candle_q_nonzero (candle_q_matan_value_r2 input) /\
    candle_q_nonzero (candle_q_matan_derivative_r2 input)`;;

let candle_q_matan_constants_real = prove
 (`candle_q_real candle_q_matan_zero = &0 /\
   candle_q_real candle_q_matan_one = &1 /\
   candle_q_real candle_q_matan_third = &1 / &3 /\
   candle_q_real candle_q_matan_fifth = &1 / &5 /\
   candle_q_real candle_q_matan_two_fifths = &2 / &5 /\
   candle_q_real candle_q_matan_two = &2 /\
   candle_q_real candle_q_matan_seven = &7 /\
   candle_q_real candle_q_matan_nine_tenths = #0.9 /\
   candle_q_real candle_q_matan_neg_one_fifth = -- #0.2 /\
   candle_q_real candle_q_matan_thirteen_twentieths = #0.65`,
  REWRITE_TAC[candle_q_matan_zero_def; candle_q_matan_one_def;
              candle_q_matan_third_def; candle_q_matan_fifth_def;
              candle_q_matan_two_fifths_def; candle_q_matan_two_def;
              candle_q_matan_seven_def; candle_q_matan_nine_tenths_def;
              candle_q_matan_neg_one_fifth_def;
              candle_q_matan_thirteen_twentieths_def;
              candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let [candle_q_matan_zero_real;
     candle_q_matan_one_real;
     candle_q_matan_third_real;
     candle_q_matan_fifth_real;
     candle_q_matan_two_fifths_real;
     candle_q_matan_two_real;
     candle_q_matan_seven_real;
     candle_q_matan_nine_tenths_real;
     candle_q_matan_neg_one_fifth_real;
     candle_q_matan_thirteen_twentieths_real] =
  CONJUNCTS candle_q_matan_constants_real;;

let candle_q_matan_const_interval_sound = prove
 (`!q. candle_q_interval_contains (candle_q_matan_const_interval q)
          (candle_q_real q)`,
  REWRITE_TAC[candle_q_matan_const_interval_def;
              candle_q_interval_contains_def; FST; SND; REAL_LE_REFL]);;

let candle_q_matan_abs_upper_real = prove
  (`!input.
    candle_q_real (candle_q_matan_abs_upper input) =
    max (candle_q_real (SND input)) (--(candle_q_real (FST input)))`,
  REWRITE_TAC[candle_q_matan_abs_upper_def; candle_q_max_real;
              candle_q_real_neg]);;

let candle_q_matan_abs_upper_sound = prove
 (`!input x.
    candle_q_interval_contains input x
    ==> abs x <= candle_q_real (candle_q_matan_abs_upper input)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_q_matan_abs_upper_real; REAL_ABS_BOUNDS] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`candle_q_real (SND input):real`;
       `--(candle_q_real (FST input)):real`] REAL_MAX_MAX) THEN
  ASM_REAL_ARITH_TAC);;

let candle_q_matan_u2_real = prove
 (`!input. candle_q_real (candle_q_matan_u2 input) =
     candle_q_real (candle_q_matan_abs_upper input) *
     candle_q_real (candle_q_matan_abs_upper input)`,
  REWRITE_TAC[candle_q_matan_u2_def; candle_q_real_mul_normalized]);;

let candle_q_matan_u3_real = prove
 (`!input. candle_q_real (candle_q_matan_u3 input) =
     (candle_q_real (candle_q_matan_abs_upper input) *
      candle_q_real (candle_q_matan_abs_upper input)) *
     candle_q_real (candle_q_matan_abs_upper input)`,
  REWRITE_TAC[candle_q_matan_u3_def; candle_q_matan_u2_real;
              candle_q_real_mul_normalized]);;

let candle_q_matan_r1_real = prove
 (`!input. candle_q_real (candle_q_matan_r1 input) =
     &1 - candle_q_real (candle_q_matan_abs_upper input)`,
  REWRITE_TAC[candle_q_matan_r1_def; candle_q_real_add_normalized;
              candle_q_real_neg; candle_q_matan_one_real] THEN
  REAL_ARITH_TAC);;

let candle_q_matan_value_r2_real = prove
 (`!input. candle_q_real (candle_q_matan_value_r2 input) =
     &7 * (&1 - candle_q_real (candle_q_matan_abs_upper input))`,
  REWRITE_TAC[candle_q_matan_value_r2_def;
              candle_q_real_mul_normalized;
              candle_q_matan_seven_real; candle_q_matan_r1_real]);;

let candle_q_matan_derivative_r2_real = prove
 (`!input. candle_q_real (candle_q_matan_derivative_r2 input) =
     &2 * (&1 - candle_q_real (candle_q_matan_abs_upper input))`,
  REWRITE_TAC[candle_q_matan_derivative_r2_def;
              candle_q_real_mul_normalized;
              candle_q_matan_two_real; candle_q_matan_r1_real]);;

let candle_q_matan_value_error_real = prove
 (`!input.
    candle_q_nonzero (candle_q_matan_value_r2 input)
    ==> candle_q_real (candle_q_matan_value_error input) =
        ((candle_q_real (candle_q_matan_abs_upper input) *
          candle_q_real (candle_q_matan_abs_upper input)) *
         candle_q_real (candle_q_matan_abs_upper input)) /
        (&7 * (&1 - candle_q_real (candle_q_matan_abs_upper input)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_matan_value_error_def;
               candle_q_real_mul_normalized; candle_q_matan_u3_real;
               candle_q_inv_real; candle_q_matan_value_r2_real; real_div]);;

let candle_q_matan_derivative_error_real = prove
 (`!input.
    candle_q_nonzero (candle_q_matan_derivative_r2 input)
    ==> candle_q_real (candle_q_matan_derivative_error input) =
        (candle_q_real (candle_q_matan_abs_upper input) *
         candle_q_real (candle_q_matan_abs_upper input)) /
        (&2 * (&1 - candle_q_real (candle_q_matan_abs_upper input)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_matan_derivative_error_def;
               candle_q_real_mul_normalized; candle_q_matan_u2_real;
               candle_q_inv_real; candle_q_matan_derivative_r2_real;
               real_div]);;

let candle_q_matan_u2_bound = prove
 (`!input.
    candle_q_real (candle_q_matan_abs_upper input) *
      candle_q_real (candle_q_matan_abs_upper input) <=
    candle_q_real (candle_q_matan_u2 input)`,
  REWRITE_TAC[candle_q_matan_u2_real] THEN REAL_ARITH_TAC);;

let candle_q_matan_u3_bound = prove
 (`!input.
    candle_q_real (candle_q_matan_u2 input) *
      candle_q_real (candle_q_matan_abs_upper input) <=
    candle_q_real (candle_q_matan_u3 input)`,
  REWRITE_TAC[candle_q_matan_u3_real; candle_q_matan_u2_real] THEN
  REAL_ARITH_TAC);;

let candle_q_matan_r1_bound = prove
 (`!input.
    candle_q_real (candle_q_matan_r1 input) <=
    &1 - candle_q_real (candle_q_matan_abs_upper input)`,
  REWRITE_TAC[candle_q_matan_r1_real] THEN REAL_ARITH_TAC);;

let candle_q_matan_value_r2_bound = prove
 (`!input.
    candle_q_real (candle_q_matan_value_r2 input) <=
    &7 * candle_q_real (candle_q_matan_r1 input)`,
  REWRITE_TAC[candle_q_matan_value_r2_real;
              candle_q_matan_r1_real] THEN REAL_ARITH_TAC);;

let candle_q_matan_value_error_bound = prove
 (`!input.
    candle_q_nonzero (candle_q_matan_value_r2 input)
    ==> candle_q_real (candle_q_matan_u3 input) /
          candle_q_real (candle_q_matan_value_r2 input) <=
        candle_q_real (candle_q_matan_value_error input)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_matan_value_error_real;
               candle_q_matan_u3_real;
               candle_q_matan_value_r2_real] THEN
  REAL_ARITH_TAC);;

let candle_q_matan_value_lower_endpoint = prove
 (`!input.
    candle_q_real (FST (candle_q_interval_matan_series input)) <=
    candle_q_real (FST (candle_q_matan_value_poly input)) -
      candle_q_real (candle_q_matan_value_error input)`,
  REWRITE_TAC[candle_q_interval_matan_series_def;
              candle_q_matan_expand_error_def; FST;
              candle_q_real_add_normalized; candle_q_real_neg] THEN
  REAL_ARITH_TAC);;

let candle_q_matan_value_upper_endpoint = prove
 (`!input.
    candle_q_real (SND (candle_q_matan_value_poly input)) +
      candle_q_real (candle_q_matan_value_error input) <=
    candle_q_real (SND (candle_q_interval_matan_series input))`,
  REWRITE_TAC[candle_q_interval_matan_series_def;
              candle_q_matan_expand_error_def; SND;
              candle_q_real_add_normalized; candle_q_real_neg] THEN
  REAL_ARITH_TAC);;

let candle_q_matan_derivative_r2_bound = prove
 (`!input.
    candle_q_real (candle_q_matan_derivative_r2 input) <=
    &2 * candle_q_real (candle_q_matan_r1 input)`,
  REWRITE_TAC[candle_q_matan_derivative_r2_real;
              candle_q_matan_r1_real] THEN
  REAL_ARITH_TAC);;

let candle_q_matan_derivative_error_bound = prove
 (`!input.
    candle_q_nonzero (candle_q_matan_derivative_r2 input)
    ==> candle_q_real (candle_q_matan_u2 input) /
          candle_q_real (candle_q_matan_derivative_r2 input) <=
        candle_q_real (candle_q_matan_derivative_error input)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_matan_derivative_error_real;
               candle_q_matan_u2_real;
               candle_q_matan_derivative_r2_real] THEN
  REAL_ARITH_TAC);;

let candle_q_matan_derivative_lower_endpoint = prove
 (`!input.
    candle_q_real (FST (candle_q_interval_dmatan_series input)) <=
    candle_q_real (FST (candle_q_matan_derivative_poly input)) -
      candle_q_real (candle_q_matan_derivative_error input)`,
  REWRITE_TAC[candle_q_interval_dmatan_series_def;
              candle_q_matan_expand_error_def; FST;
              candle_q_real_add_normalized; candle_q_real_neg] THEN
  REAL_ARITH_TAC);;

let candle_q_matan_derivative_upper_endpoint = prove
 (`!input.
    candle_q_real (SND (candle_q_matan_derivative_poly input)) +
      candle_q_real (candle_q_matan_derivative_error input) <=
    candle_q_real (SND (candle_q_interval_dmatan_series input))`,
  REWRITE_TAC[candle_q_interval_dmatan_series_def;
              candle_q_matan_expand_error_def; SND;
              candle_q_real_add_normalized; candle_q_real_neg] THEN
  REAL_ARITH_TAC);;

let candle_q_matan_dd_constant_interval = prove
 (`interval_arith (#0.65)
     (candle_q_real candle_q_matan_thirteen_twentieths,
      candle_q_real candle_q_matan_thirteen_twentieths)`,
  REWRITE_TAC[interval_arith;
              candle_q_matan_thirteen_twentieths_real] THEN
  REAL_ARITH_TAC);;

let candle_q_matan_dd_neg_endpoint = prove
 (`candle_q_real (candle_q_neg candle_q_matan_thirteen_twentieths) =
   --(candle_q_real candle_q_matan_thirteen_twentieths)`,
  REWRITE_TAC[candle_q_real_neg]);;

let candle_q_matan_value_poly_sound = prove
 (`!input x.
    candle_q_interval_contains input x
    ==> candle_q_interval_contains (candle_q_matan_value_poly input)
          ((&1 - x / &3) + (x * x) / &5)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((&1 - x / &3) + (x * x) / &5) =
    (&1 + (--(&1 / &3)) * x) + (&1 / &5) * (x * x)`
  SUBST1_TAC THENL
   [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[candle_q_matan_value_poly_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
    CONJ_TAC THENL
     [MP_TAC (SPEC `candle_q_matan_one` candle_q_matan_const_interval_sound) THEN
      REWRITE_TAC[candle_q_matan_one_real];
      MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC
        (SPEC `candle_q_neg candle_q_matan_third`
          candle_q_matan_const_interval_sound) THEN
      REWRITE_TAC[candle_q_real_neg; candle_q_matan_third_real] THEN
      DISCH_THEN ACCEPT_TAC];
    MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
    CONJ_TAC THENL
     [MP_TAC (SPEC `candle_q_matan_fifth`
        candle_q_matan_const_interval_sound) THEN
      REWRITE_TAC[candle_q_matan_fifth_real] THEN
      DISCH_THEN ACCEPT_TAC;
      REWRITE_TAC[candle_q_interval_normalize_contains] THEN
      MATCH_MP_TAC candle_q_interval_square_sound THEN ASM_REWRITE_TAC[]]]);;

let candle_q_matan_derivative_poly_sound = prove
 (`!input x.
    candle_q_interval_contains input x
    ==> candle_q_interval_contains (candle_q_matan_derivative_poly input)
          (&2 * x / &5 - &1 / &3)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(&2 * x / &5 - &1 / &3) =
    --(&1 / &3) + (&2 / &5) * x`
  SUBST1_TAC THENL
   [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[candle_q_matan_derivative_poly_def] THEN
  MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
  CONJ_TAC THENL
   [MP_TAC
      (SPEC `candle_q_neg candle_q_matan_third`
        candle_q_matan_const_interval_sound) THEN
    REWRITE_TAC[candle_q_real_neg; candle_q_matan_third_real] THEN
    DISCH_THEN ACCEPT_TAC;
    MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC
      (SPEC `candle_q_matan_two_fifths`
        candle_q_matan_const_interval_sound) THEN
    REWRITE_TAC[candle_q_matan_two_fifths_real] THEN
    DISCH_THEN ACCEPT_TAC]);;

let candle_q_interval_matan_series_sound = prove
 (`!input x.
    candle_q_interval_matan_series_domain input /\
    candle_q_interval_contains input x
    ==> candle_q_interval_contains
          (candle_q_interval_matan_series input) (matan x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_matan_series_domain_def] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`input:(((num#num)#num)#((num#num)#num))`; `x:real`]
    candle_q_matan_value_poly_sound) THEN
  ASM_REWRITE_TAC[candle_q_interval_contains_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `interval_arith x
      (candle_q_real (FST input),candle_q_real (SND input))`
  ASSUME_TAC THENL
   [MP_TAC
      (ASSUME `candle_q_interval_contains input x`) THEN
    REWRITE_TAC[interval_arith; candle_q_interval_contains_def];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interval_arith ((&1 - x / &3) + (x * x) / &5)
      (candle_q_real (FST (candle_q_matan_value_poly input)),
       candle_q_real (SND (candle_q_matan_value_poly input)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[interval_arith]; ALL_TAC] THEN
  SUBGOAL_THEN
   `iabs (candle_q_real (FST input),candle_q_real (SND input)) =
    candle_q_real (candle_q_matan_abs_upper input)`
  ASSUME_TAC THENL
   [REWRITE_TAC[iabs; candle_q_matan_abs_upper_real]; ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_real (candle_q_matan_abs_upper input) <= #0.9`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_q_matan_nine_tenths_real;
                GSYM candle_q_le_real] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < candle_q_real (candle_q_matan_value_r2 input)`
  ASSUME_TAC THENL
   [REWRITE_TAC[candle_q_matan_value_r2_real] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_real (candle_q_matan_value_error input) =
    candle_q_real (candle_q_matan_u3 input) /
    candle_q_real (candle_q_matan_value_r2 input)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[candle_q_matan_value_error_real;
                 candle_q_matan_u3_real;
                 candle_q_matan_value_r2_real];
    ALL_TAC] THEN
  MP_TAC (SPEC `input:(((num#num)#num)#((num#num)#num))`
    candle_q_matan_u2_bound) THEN DISCH_TAC THEN
  MP_TAC (SPEC `input:(((num#num)#num)#((num#num)#num))`
    candle_q_matan_u3_bound) THEN DISCH_TAC THEN
  MP_TAC (SPEC `input:(((num#num)#num)#((num#num)#num))`
    candle_q_matan_r1_bound) THEN DISCH_TAC THEN
  MP_TAC (SPEC `input:(((num#num)#num)#((num#num)#num))`
    candle_q_matan_value_r2_bound) THEN DISCH_TAC THEN
  MP_TAC
    (MATCH_MP
      (SPEC `input:(((num#num)#num)#((num#num)#num))`
        candle_q_matan_value_error_bound)
      (ASSUME `candle_q_nonzero (candle_q_matan_value_r2 input)`)) THEN
  DISCH_TAC THEN
  MP_TAC (SPEC `input:(((num#num)#num)#((num#num)#num))`
    candle_q_matan_value_lower_endpoint) THEN DISCH_TAC THEN
  MP_TAC (SPEC `input:(((num#num)#num)#((num#num)#num))`
    candle_q_matan_value_upper_endpoint) THEN DISCH_TAC THEN
  let matan_th =
    INST
     [`candle_q_real
        (FST (input:(((num#num)#num)#((num#num)#num))))`,`lo:real`;
      `candle_q_real
        (SND (input:(((num#num)#num)#((num#num)#num))))`,`hi:real`;
      `candle_q_real (FST (candle_q_matan_value_poly input))`,`a:real`;
      `candle_q_real (SND (candle_q_matan_value_poly input))`,`b:real`;
      `candle_q_real (candle_q_matan_abs_upper input)`,`u:real`;
      `candle_q_real (candle_q_matan_u2 input)`,`u2:real`;
      `candle_q_real (candle_q_matan_u3 input)`,`u3:real`;
      `candle_q_real (candle_q_matan_r1 input)`,`r1:real`;
      `candle_q_real (candle_q_matan_value_r2 input)`,`r2:real`;
      `candle_q_real (candle_q_matan_value_error input)`,`e:real`;
      `candle_q_real (FST (candle_q_interval_matan_series input))`,
       `low:real`;
      `candle_q_real (SND (candle_q_interval_matan_series input))`,
       `high:real`]
     Matan_eval.matan_abs1 in
  let float7_eq =
    Arith_float.FLOAT_TO_NUM_CONV (Arith_float.mk_float 7 0) in
  let rewritten_matan_th =
    REWRITE_RULE[interval_arith]
      ((UNDISCH_ALL o
        PURE_REWRITE_RULE
          [EQ_CLAUSES; More_float.float1_eq; float7_eq] o
        DISCH_ALL) matan_th) in
  ACCEPT_TAC rewritten_matan_th);;

let candle_q_interval_dmatan_series_sound = prove
 (`!input x.
    candle_q_interval_matan_series_domain input /\
    candle_q_interval_contains input x
    ==> candle_q_interval_contains
          (candle_q_interval_dmatan_series input) (dmatan x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_matan_series_domain_def] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`input:(((num#num)#num)#((num#num)#num))`; `x:real`]
    candle_q_matan_derivative_poly_sound) THEN
  ASM_REWRITE_TAC[candle_q_interval_contains_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `interval_arith x
      (candle_q_real (FST input),candle_q_real (SND input))`
  ASSUME_TAC THENL
   [MP_TAC
      (ASSUME `candle_q_interval_contains input x`) THEN
    REWRITE_TAC[interval_arith; candle_q_interval_contains_def];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interval_arith (&2 * x / &5 - &1 / &3)
      (candle_q_real (FST (candle_q_matan_derivative_poly input)),
       candle_q_real (SND (candle_q_matan_derivative_poly input)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[interval_arith]; ALL_TAC] THEN
  SUBGOAL_THEN
   `iabs (candle_q_real (FST input),candle_q_real (SND input)) =
    candle_q_real (candle_q_matan_abs_upper input)`
  ASSUME_TAC THENL
   [REWRITE_TAC[iabs; candle_q_matan_abs_upper_real]; ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_real (candle_q_matan_abs_upper input) <= #0.9`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_q_matan_nine_tenths_real;
                GSYM candle_q_le_real] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < candle_q_real (candle_q_matan_derivative_r2 input)`
  ASSUME_TAC THENL
   [REWRITE_TAC[candle_q_matan_derivative_r2_real] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_real (candle_q_matan_derivative_error input) =
    candle_q_real (candle_q_matan_u2 input) /
    candle_q_real (candle_q_matan_derivative_r2 input)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[candle_q_matan_derivative_error_real;
                 candle_q_matan_u2_real;
                 candle_q_matan_derivative_r2_real];
    ALL_TAC] THEN
  MP_TAC (SPEC `input:(((num#num)#num)#((num#num)#num))`
    candle_q_matan_u2_bound) THEN DISCH_TAC THEN
  MP_TAC (SPEC `input:(((num#num)#num)#((num#num)#num))`
    candle_q_matan_r1_bound) THEN DISCH_TAC THEN
  MP_TAC (SPEC `input:(((num#num)#num)#((num#num)#num))`
    candle_q_matan_derivative_r2_bound) THEN DISCH_TAC THEN
  MP_TAC
    (MATCH_MP
      (SPEC `input:(((num#num)#num)#((num#num)#num))`
        candle_q_matan_derivative_error_bound)
      (ASSUME `candle_q_nonzero (candle_q_matan_derivative_r2 input)`)) THEN
  DISCH_TAC THEN
  MP_TAC (SPEC `input:(((num#num)#num)#((num#num)#num))`
    candle_q_matan_derivative_lower_endpoint) THEN DISCH_TAC THEN
  MP_TAC (SPEC `input:(((num#num)#num)#((num#num)#num))`
    candle_q_matan_derivative_upper_endpoint) THEN DISCH_TAC THEN
  let dmatan_th =
    INST
     [`candle_q_real
        (FST (input:(((num#num)#num)#((num#num)#num))))`,`lo:real`;
      `candle_q_real
        (SND (input:(((num#num)#num)#((num#num)#num))))`,`hi:real`;
      `candle_q_real
        (FST (candle_q_matan_derivative_poly input))`,`a:real`;
      `candle_q_real
        (SND (candle_q_matan_derivative_poly input))`,`b:real`;
      `candle_q_real (candle_q_matan_abs_upper input)`,`u:real`;
      `candle_q_real (candle_q_matan_u2 input)`,`u2:real`;
      `candle_q_real (candle_q_matan_r1 input)`,`r1:real`;
      `candle_q_real (candle_q_matan_derivative_r2 input)`,`r2:real`;
      `candle_q_real (candle_q_matan_derivative_error input)`,`e:real`;
      `candle_q_real (FST (candle_q_interval_dmatan_series input))`,
       `low:real`;
      `candle_q_real (SND (candle_q_interval_dmatan_series input))`,
       `high:real`]
     Matan_eval.dmatan_abs1 in
  let normalized_dmatan_th =
    (UNDISCH_ALL o
     PURE_REWRITE_RULE
       [EQ_CLAUSES; More_float.float1_eq; More_float.float2_eq] o
     DISCH_ALL) dmatan_th in
  ACCEPT_TAC (REWRITE_RULE[interval_arith] normalized_dmatan_th));;

let candle_q_interval_ddmatan_series_sound = prove
 (`!input x.
    candle_q_interval_matan_series_domain input /\
    candle_q_interval_contains input x
    ==> candle_q_interval_contains
          (candle_q_interval_ddmatan_series input) (ddmatan x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_matan_series_domain_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `interval_arith x
      (candle_q_real (FST input),candle_q_real (SND input))`
  ASSUME_TAC THENL
   [MP_TAC
      (ASSUME `candle_q_interval_contains input x`) THEN
    REWRITE_TAC[interval_arith; candle_q_interval_contains_def];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `-- #0.2 <=
    candle_q_real
      (FST (input:(((num#num)#num)#((num#num)#num))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_q_matan_neg_one_fifth_real;
                GSYM candle_q_le_real] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC candle_q_matan_dd_constant_interval THEN DISCH_TAC THEN
  MP_TAC candle_q_matan_dd_neg_endpoint THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_q_interval_ddmatan_series_def; FST; SND] THEN
  let ddmatan_th =
    INST
     [`candle_q_real
        (FST (input:(((num#num)#num)#((num#num)#num))))`,`lo:real`;
      `candle_q_real
        (SND (input:(((num#num)#num)#((num#num)#num))))`,`hi:real`;
      `candle_q_real candle_q_matan_thirteen_twentieths`,`a:real`;
      `candle_q_real candle_q_matan_thirteen_twentieths`,`b:real`;
      `candle_q_real
        (candle_q_neg candle_q_matan_thirteen_twentieths)`,`b2:real`]
     Matan_eval.ddmatan_ge_neg02 in
  let rewritten_ddmatan_th = REWRITE_RULE[interval_arith] ddmatan_th in
  ACCEPT_TAC rewritten_ddmatan_th);;

end;;
