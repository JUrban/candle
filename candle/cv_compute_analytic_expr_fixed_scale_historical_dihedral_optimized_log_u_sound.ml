(* ========================================================================== *)
(* Historical low-work dihedral instruction: logarithmic U derivative.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_integration_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound;;

(* A small distributivity fact avoids constructing a large generic ring
   certificate when matching the historical delta gradient to delta_x4. *)

let candle_hist_real_mul_signed_six_sum = prove
 (`!a b c d e f g.
     a * (--b + c + d + --e + f + g) =
     --(a * b) + a * c + a * d + --(a * e) + a * f + a * g`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_LNEG] THEN
  REAL_ARITH_TAC);;

let candle_fs_hist_delta_gradient_3_real_def = new_definition
 `candle_fs_hist_delta_gradient_3_real (values:num->real) =
    ITLIST (\x total:real. x + total)
      [--(values 0 * values 0);values 0 * values 1;
       values 0 * values 2;--(&2 * (values 0 * values 3));
       values 0 * values 4;values 0 * values 5;
       --(values 1 * values 2);values 1 * values 4;
       values 2 * values 5;--(values 4 * values 5)] (&0)`;;

let candle_fs_hist_delta_gradient_3_is_expanded = prove
 (`!values.
     EL 3 (candle_fs_hist_delta_gradient_real values) =
     candle_fs_hist_delta_gradient_3_real values`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_delta_gradient_real_def;
              candle_fs_hist_delta_gradient_3_real_def;
              num_CONV `3`; num_CONV `2`; num_CONV `1`;
              EL; HD; TL]);;

let candle_fs_hist_delta_x4_is_gradient_3_expanded = prove
 (`!values.
     candle_fs_hist_delta_x4_real values =
     candle_fs_hist_delta_gradient_3_real values`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_real_def;
              candle_fs_hist_delta_gradient_3_real_def;
              LET_DEF; LET_END_DEF; ITLIST; REAL_ADD_RID] THEN
  ONCE_REWRITE_TAC[candle_hist_real_mul_signed_six_sum] THEN
  REAL_ARITH_TAC);;

let candle_fs_hist_delta_gradient_3_is_delta_x4 = prove
 (`!values.
     EL 3 (candle_fs_hist_delta_gradient_real values) =
     candle_fs_hist_delta_x4_real values`,
  REWRITE_TAC[candle_fs_hist_delta_gradient_3_is_expanded;
              candle_fs_hist_delta_x4_is_gradient_3_expanded]);;

end;;
