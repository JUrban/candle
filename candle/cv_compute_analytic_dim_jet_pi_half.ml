(* ========================================================================== *)
(* Authenticated pi/2 interval and dimension-generic constant interval jet.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The interval is derived once from             *)
(* PI_APPROX_32.  Its value remains data during reflected checking while      *)
(* gradient and Hessian entries are exact zero intervals.                     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_dim_jet_atn.ml";;

module Candle_cv_analytic_dim_jet_pi_half = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;

let candle_q_pi_half_interval_def = new_definition
 `candle_q_pi_half_interval =
    ((((1686629713,0),1073741823),
      ((6746518853,0),4294967295)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_dim_jet_pi_half_def = new_definition
 `candle_q_dim_jet_pi_half boxes =
    candle_q_dim_jet_make candle_q_pi_half_interval
      (candle_q_dim_interval_zeros_like boxes)
      (candle_q_dim_interval_zero_matrix_like boxes boxes)`;;

let candle_cv_q_pi_half_interval_def = new_definition
 `candle_cv_q_pi_half_interval =
    candle_cv_q_interval candle_q_pi_half_interval`;;

let candle_cv_q_pi_half_interval_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_pi_half_interval_def;
                    candle_cv_q_interval_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    candle_cv_q_pi_half_interval_def;;

let candle_cv_q_dim_jet_pi_half_def = new_definition
 `candle_cv_q_dim_jet_pi_half boxes =
    candle_cv_q_dim_jet_make candle_cv_q_pi_half_interval
      (candle_cv_q_dim_interval_zeros boxes)
      (candle_cv_q_dim_interval_zero_matrix boxes boxes)`;;

let candle_cv_q_dim_jet_pi_half_compute_eqs =
  candle_cv_q_dim_jet_atn_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_pi_half_interval_compute;
    candle_cv_q_dim_jet_pi_half_def];;

let candle_cv_q_pi_half_interval_correct = prove
 (`candle_cv_q_pi_half_interval =
   candle_cv_q_interval candle_q_pi_half_interval`,
  REWRITE_TAC[candle_cv_q_pi_half_interval_def]);;

let candle_cv_q_dim_jet_pi_half_correct = prove
 (`!boxes.
     candle_cv_q_dim_jet_pi_half (candle_cv_q_interval_list boxes) =
     candle_cv_q_dim_jet_encode (candle_q_dim_jet_pi_half boxes)`,
  REWRITE_TAC[candle_cv_q_dim_jet_pi_half_def;
              candle_q_dim_jet_pi_half_def;
              candle_cv_q_pi_half_interval_correct;
              candle_cv_q_dim_interval_zeros_correct;
              candle_cv_q_dim_interval_zero_matrix_correct;
              candle_cv_q_dim_jet_make_correct]);;

let candle_q_pi_half_interval_sound = prove
 (`candle_q_interval_contains candle_q_pi_half_interval (pi / &2)`,
  REWRITE_TAC[candle_q_pi_half_interval_def;
              candle_q_interval_contains_def;
              candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  MP_TAC PI_APPROX_32 THEN
  REWRITE_TAC[REAL_ARITH `abs(x - a) <= e <=> a - e <= x /\ x <= a + e`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let candle_q_dim_jet_pi_half_shape = prove
 (`!boxes.
     candle_q_dim_jet_shape (LENGTH boxes)
       (candle_q_dim_jet_pi_half boxes)`,
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_pi_half_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_q_dim_interval_zeros_like_map; LENGTH_MAP;
              candle_q_dim_interval_zero_matrix_like_shape]);;

let candle_q_dim_jet_pi_half_components_sound = prove
 (`!boxes.
     candle_q_dim_jet_contains_components (LENGTH boxes)
       (candle_q_dim_jet_pi_half boxes) (pi / &2)
       (\i. &0) (\i j. &0)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def;
              candle_q_dim_jet_pi_half_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_zeros_like_lookup;
               candle_q_dim_interval_zero_matrix_like_lookup;
               candle_q_pi_half_interval_sound;
               candle_q_zero_interval_contains]);;

end;;
