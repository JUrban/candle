(* ========================================================================== *)
(* Semantic completion for reflected signed fixed-scale Taylor models.       *)
(*                                                                            *)
(* The fixed-scale arithmetic and structural conversion are proved in the    *)
(* substrate.  This file proves that the reconstructed whole-box value and   *)
(* gradient bounds retain the established universal Taylor semantics.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_complete_sound = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_sound;;

let candle_fs_gradient_bound_raw_def = new_definition
 `candle_fs_gradient_bound_raw radii center_interval interval_row =
    candle_fs_raw_interval_add
      (candle_lc_zscale candle_fs_scale (FST center_interval),
       candle_lc_zscale candle_fs_scale (SND center_interval))
      (candle_fs_raw_neg
         (candle_fs_dot_abs_upper radii interval_row),
       candle_fs_dot_abs_upper radii interval_row)`;;

let candle_fs_gradient_bound_def = new_definition
 `candle_fs_gradient_bound radii center_interval interval_row =
    candle_fs_raw_interval_round candle_fs_scale
      (candle_fs_gradient_bound_raw radii center_interval interval_row)`;;

let candle_fs_raw_product_scale_real = prove
 (`!z.
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (candle_lc_zscale candle_fs_scale z) = candle_fs_real z`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; candle_fs_real_def;
              candle_lc_zreal_scale; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC candle_fs_scale_pos THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN CONV_TAC REAL_FIELD);;

let candle_fs_raw_product_neg_real = prove
 (`!z.
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (candle_fs_raw_neg z) =
     --(candle_fs_raw_real (candle_fs_scale * candle_fs_scale) z)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; candle_fs_raw_neg_real;
              real_div; GSYM REAL_NEG_LMUL]);;

let candle_fs_gradient_bound_raw_real = prove
 (`!radii center_interval interval_row.
     let error =
       candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
         (candle_fs_dot_abs_upper radii interval_row) in
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (FST
         (candle_fs_gradient_bound_raw
           radii center_interval interval_row)) =
       candle_fs_real (FST center_interval) - error /\
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (SND
         (candle_fs_gradient_bound_raw
           radii center_interval interval_row)) =
       candle_fs_real (SND center_interval) + error`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; candle_fs_gradient_bound_raw_def;
              candle_fs_raw_interval_add_def; FST; SND;
              candle_fs_raw_product_add_real;
              candle_fs_raw_product_scale_real;
              candle_fs_raw_product_neg_real] THEN
  REAL_ARITH_TAC);;

let candle_fs_gradient_bound_contains = prove
 (`!radii values intervals center_interval target.
     ALL (\r. &0 <= candle_fs_real r) radii /\
     ALL2 candle_fs_interval_contains intervals values /\
     LENGTH radii = LENGTH values /\
     candle_fs_real (FST center_interval) -
       ITLIST2
         (\r y total. candle_fs_real r * abs y + total)
         radii values (&0) <= target /\
     target <= candle_fs_real (SND center_interval) +
       ITLIST2
         (\r y total. candle_fs_real r * abs y + total)
         radii values (&0)
     ==>
     candle_fs_interval_contains
       (candle_fs_gradient_bound radii center_interval intervals) target`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ITLIST2
      (\r y total. candle_fs_real r * abs y + total)
      radii values (&0)
    <= candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
         (candle_fs_dot_abs_upper radii intervals)`
   (LABEL_TAC "error_bound") THENL
   [MATCH_MP_TAC candle_fs_dot_abs_upper_sound THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_gradient_bound_def] THEN
  MATCH_MP_TAC candle_fs_raw_interval_round_sound THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC candle_fs_scale_pos;
    REWRITE_TAC[candle_fs_raw_interval_contains_def] THEN
    MP_TAC
      (SPECL
        [`radii:(num#num)list`;
         `center_interval:(num#num)#(num#num)`;
         `intervals:((num#num)#(num#num))list`]
        candle_fs_gradient_bound_raw_real) THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    ASM_REAL_ARITH_TAC]);;

let candle_fs_value_error_raw_def = new_definition
 `candle_fs_value_error_raw radii gradient hessian =
    candle_lc_zadd
      (candle_lc_zscale (2 * candle_fs_scale)
        (candle_fs_dot_abs_upper radii gradient))
      (candle_fs_weighted_rows_abs_upper radii radii hessian)`;;

let candle_fs_value_bound_raw_def = new_definition
 `candle_fs_value_bound_raw radii center_value gradient hessian =
    candle_fs_raw_interval_add
      (candle_lc_zscale candle_fs_two_scale_squared (FST center_value),
       candle_lc_zscale candle_fs_two_scale_squared (SND center_value))
      (candle_fs_raw_neg
         (candle_fs_value_error_raw radii gradient hessian),
       candle_fs_value_error_raw radii gradient hessian)`;;

let candle_fs_value_bound_def = new_definition
 `candle_fs_value_bound radii center_value gradient hessian =
    candle_fs_raw_interval_round candle_fs_two_scale_squared
      (candle_fs_value_bound_raw radii center_value gradient hessian)`;;

let candle_fs_value_denominator_pos = prove
 (`0 < candle_fs_two_scale_squared * candle_fs_scale`,
  REWRITE_TAC[candle_fs_two_scale_squared_def;
              candle_fs_scale_squared_def; LT_MULT;
              candle_fs_scale_pos; candle_fs_product_denominator_pos] THEN
  ARITH_TAC);;

let candle_fs_two_scale_squared_pos = prove
 (`0 < candle_fs_two_scale_squared`,
  MP_TAC candle_fs_value_denominator_pos THEN
  REWRITE_TAC[LT_MULT] THEN MESON_TAC[]);;

let candle_fs_raw_value_add_real = prove
 (`!x y.
     candle_fs_raw_real
       (candle_fs_two_scale_squared * candle_fs_scale)
       (candle_lc_zadd x y) =
     candle_fs_raw_real
       (candle_fs_two_scale_squared * candle_fs_scale) x +
     candle_fs_raw_real
       (candle_fs_two_scale_squared * candle_fs_scale) y`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC candle_fs_raw_add_real THEN
  MP_TAC candle_fs_value_denominator_pos THEN ARITH_TAC);;

let candle_fs_raw_value_neg_real = prove
 (`!z.
     candle_fs_raw_real
       (candle_fs_two_scale_squared * candle_fs_scale)
       (candle_fs_raw_neg z) =
     --(candle_fs_raw_real
       (candle_fs_two_scale_squared * candle_fs_scale) z)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; candle_fs_raw_neg_real;
              real_div; GSYM REAL_NEG_LMUL]);;

let candle_fs_raw_value_center_scale_real = prove
 (`!z.
     candle_fs_raw_real
       (candle_fs_two_scale_squared * candle_fs_scale)
       (candle_lc_zscale candle_fs_two_scale_squared z) =
     candle_fs_real z`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; candle_fs_real_def;
              candle_lc_zreal_scale; candle_fs_two_scale_squared_def;
              candle_fs_scale_squared_def;
              GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC candle_fs_scale_pos THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN CONV_TAC REAL_FIELD);;

let candle_fs_raw_value_gradient_scale_real = prove
 (`!z.
     candle_fs_raw_real
       (candle_fs_two_scale_squared * candle_fs_scale)
       (candle_lc_zscale (2 * candle_fs_scale) z) =
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale) z`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; candle_lc_zreal_scale;
              candle_fs_two_scale_squared_def;
              candle_fs_scale_squared_def;
              GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC candle_fs_scale_pos THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN CONV_TAC REAL_FIELD);;

let candle_fs_raw_value_hessian_real = prove
 (`!z.
     candle_fs_raw_real
       (candle_fs_two_scale_squared * candle_fs_scale) z =
     candle_fs_raw_real
       (candle_fs_scale * (candle_fs_scale * candle_fs_scale)) z / &2`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; candle_fs_two_scale_squared_def;
              candle_fs_scale_squared_def;
              GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC candle_fs_scale_pos THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN CONV_TAC REAL_FIELD);;

let candle_fs_value_error_raw_real = prove
 (`!radii gradient hessian.
     candle_fs_raw_real
       (candle_fs_two_scale_squared * candle_fs_scale)
       (candle_fs_value_error_raw radii gradient hessian) =
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (candle_fs_dot_abs_upper radii gradient) +
     candle_fs_raw_real
       (candle_fs_scale * (candle_fs_scale * candle_fs_scale))
       (candle_fs_weighted_rows_abs_upper radii radii hessian) / &2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_value_error_raw_def] THEN
  ONCE_REWRITE_TAC[candle_fs_raw_value_add_real] THEN
  ONCE_REWRITE_TAC[candle_fs_raw_value_gradient_scale_real] THEN
  ONCE_REWRITE_TAC[candle_fs_raw_value_hessian_real] THEN
  REFL_TAC);;

let candle_fs_value_bound_raw_real = prove
 (`!radii center_value gradient hessian.
     let error =
       candle_fs_raw_real
         (candle_fs_two_scale_squared * candle_fs_scale)
         (candle_fs_value_error_raw radii gradient hessian) in
     candle_fs_raw_real
       (candle_fs_two_scale_squared * candle_fs_scale)
       (FST
         (candle_fs_value_bound_raw
           radii center_value gradient hessian)) =
       candle_fs_real (FST center_value) - error /\
     candle_fs_raw_real
       (candle_fs_two_scale_squared * candle_fs_scale)
       (SND
         (candle_fs_value_bound_raw
           radii center_value gradient hessian)) =
       candle_fs_real (SND center_value) + error`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; candle_fs_value_bound_raw_def;
              candle_fs_raw_interval_add_def; FST; SND;
              candle_fs_raw_value_add_real;
              candle_fs_raw_value_center_scale_real;
              candle_fs_raw_value_neg_real] THEN
  REAL_ARITH_TAC);;

let candle_fs_value_bound_contains = prove
 (`!radii gradient_values gradient_intervals
       hessian_values hessian_intervals center_value target.
     ALL (\r. &0 <= candle_fs_real r) radii /\
     ALL2 candle_fs_interval_contains
       gradient_intervals gradient_values /\
     LENGTH radii = LENGTH gradient_values /\
     ALL2 (ALL2 candle_fs_interval_contains)
       hessian_intervals hessian_values /\
     LENGTH radii = LENGTH hessian_values /\
     ALL (\values. LENGTH radii = LENGTH values) hessian_values /\
     candle_fs_real (FST center_value) -
       (ITLIST2
          (\r y total. candle_fs_real r * abs y + total)
          radii gradient_values (&0) +
        ITLIST2
          (\w values total.
             candle_fs_real w *
             ITLIST2
               (\r y subtotal. candle_fs_real r * abs y + subtotal)
               radii values (&0) + total)
          radii hessian_values (&0) / &2) <= target /\
     target <= candle_fs_real (SND center_value) +
       (ITLIST2
          (\r y total. candle_fs_real r * abs y + total)
          radii gradient_values (&0) +
        ITLIST2
          (\w values total.
             candle_fs_real w *
             ITLIST2
               (\r y subtotal. candle_fs_real r * abs y + subtotal)
               radii values (&0) + total)
          radii hessian_values (&0) / &2)
     ==>
     candle_fs_interval_contains
       (candle_fs_value_bound
         radii center_value gradient_intervals hessian_intervals)
       target`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ITLIST2
      (\r y total. candle_fs_real r * abs y + total)
      radii gradient_values (&0)
    <= candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
         (candle_fs_dot_abs_upper radii gradient_intervals)`
   (LABEL_TAC "gradient_bound") THENL
   [MP_TAC
      (SPECL
        [`radii:(num#num)list`;
         `gradient_values:real list`;
         `gradient_intervals:((num#num)#(num#num))list`]
        candle_fs_dot_abs_upper_sound) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ITLIST2
      (\w values total.
         candle_fs_real w *
         ITLIST2
           (\r y subtotal. candle_fs_real r * abs y + subtotal)
           radii values (&0) + total)
      radii hessian_values (&0)
    <= candle_fs_raw_real
         (candle_fs_scale * (candle_fs_scale * candle_fs_scale))
         (candle_fs_weighted_rows_abs_upper
           radii radii hessian_intervals)`
   (LABEL_TAC "hessian_bound") THENL
   [MATCH_MP_TAC candle_fs_weighted_rows_abs_upper_sound THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_value_bound_def] THEN
  MATCH_MP_TAC
    (REWRITE_RULE[candle_fs_two_scale_squared_pos]
      (SPECL
        [`candle_fs_two_scale_squared`;
         `candle_fs_value_bound_raw
            radii center_value gradient_intervals hessian_intervals`;
         `target:real`]
        candle_fs_raw_interval_round_sound)) THEN
  REWRITE_TAC[candle_fs_raw_interval_contains_def] THEN
  MP_TAC
    (SPECL
      [`radii:(num#num)list`;
       `center_value:(num#num)#(num#num)`;
       `gradient_intervals:((num#num)#(num#num))list`;
       `hessian_intervals:(((num#num)#(num#num))list)list`]
      candle_fs_value_bound_raw_real) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF;
              candle_fs_value_error_raw_real] THEN
  ASM_REAL_ARITH_TAC);;

end;;
