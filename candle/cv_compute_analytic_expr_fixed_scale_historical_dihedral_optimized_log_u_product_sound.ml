(* ========================================================================== *)
(* Historical low-work dihedral: factored U-product derivative identities.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_product_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_sound;;

let candle_hist_four_mul_as_twice_twice = prove
 (`!x:real. &4 * x = &2 * (&2 * x)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(&4:real) = &2 + &2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_2]]);;

let candle_hist_twice_mul_neg_twice_plus_four_cancel = prove
 (`!x d:real.
     (d + d) * --(&2 * x) + (&4 * x) * d = &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_four_mul_as_twice_twice; REAL_MUL_2;
              REAL_ADD_RDISTRIB; REAL_MUL_RNEG;
              REAL_ADD_LDISTRIB;
              SPECL [`d:real`; `x:real`] REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_NEG_ADD; REAL_ADD_LINV]);;

let candle_fs_hist_u_product_gradient_polynomial_3 = prove
 (`!values.
     candle_fs_hist_u126_gradient_real values 3 *
       candle_fs_hist_u135_real values +
     candle_fs_hist_u126_real values *
       candle_fs_hist_u135_gradient_real values 3 =
     (candle_fs_hist_delta_x4_real values +
      candle_fs_hist_delta_x4_real values) *
       candle_fs_hist_delta_x4_derivative values 3 +
     candle_fs_hist_four_x0_real values *
       EL 3 (candle_fs_hist_delta_gradient_real values) +
     candle_fs_hist_delta_real values *
       candle_fs_hist_four_x0_gradient_real 3`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_u126_gradient_real_def;
              candle_fs_hist_u135_gradient_real_def;
              candle_fs_hist_delta_x4_derivative_def;
              candle_fs_hist_four_x0_real_def;
              candle_fs_hist_four_x0_gradient_real_def;
              candle_fs_hist_delta_gradient_3_is_delta_x4] THEN
  REWRITE_TAC[NUM_REDUCE_CONV `3 = 0`;
              NUM_REDUCE_CONV `3 = 1`;
              NUM_REDUCE_CONV `3 = 2`;
              NUM_REDUCE_CONV `3 = 4`;
              NUM_REDUCE_CONV `3 = 5`] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO;
              REAL_ADD_LID; REAL_ADD_RID;
              candle_hist_twice_mul_neg_twice_plus_four_cancel]);;

end;;
