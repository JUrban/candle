(* ========================================================================== *)
(* Soundness substrate for the historical Flyspeck dihedral instruction.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The executable historical kernel is useful    *)
(* only after each of its specialized fixed-scale operations is related to   *)
(* the universal analytic invariant.  This file starts at the smallest lossy *)
(* boundary: the direct reciprocal of a strictly positive canonical interval. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_compute.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_angle_polynomials_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_interval_inv_core;;
open Candle_cv_analytic_expr_taylor_model_sound;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_compute;;

(* This is the exact ordinary-HOL operation implemented by
   [candle_cv_fs_hist_positive_inv].  Its general representation keeps both
   signed endpoint components visible; the semantic theorem below deliberately
   admits only the positive canonical form used by the historical instruction. *)

let candle_fs_hist_positive_inv_def = new_definition
 `candle_fs_hist_positive_inv
    (value:(num#num)#(num#num)) =
    (candle_fs_floor_div (candle_fs_scale_squared,0)
       (FST (SND value)),
     candle_fs_ceil_div (candle_fs_scale_squared,0)
       (FST (FST value)))`;;

let candle_cv_fs_hist_positive_inv_correct = prove
 (`!value.
     candle_cv_fs_hist_positive_inv (candle_cv_fs_interval value) =
     candle_cv_fs_interval (candle_fs_hist_positive_inv value)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_positive_inv_def;
              candle_fs_hist_positive_inv_def;
              candle_cv_fs_interval_def;
              candle_cv_fs_scale_squared_correct;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_floor_div_def; candle_fs_floor_div_def;
              candle_cv_fs_ceil_div_def; candle_fs_ceil_div_def;
              cexp_less_def; cexp_if_def; cexp_sub_def; cexp_div_def;
              candle_cv_q_ceil_div_correct;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  SUBGOAL_THEN
    `~(candle_fs_scale_squared < 0)` ASSUME_TAC THENL
   [REWRITE_TAC[candle_fs_scale_squared_def] THEN ARITH_TAC;
    ASM_REWRITE_TAC[cexp_if_def; FST; SND; SUB_0]]);;

let candle_fs_hist_floor_inv_lower = prove
 (`!denominator. 0 < denominator
     ==> candle_fs_real
           (candle_fs_floor_div (candle_fs_scale_squared,0) denominator)
         <= inv (&denominator / &candle_fs_scale)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_real_def] THEN
  SUBGOAL_THEN `&0 < &(candle_fs_scale)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; candle_fs_scale_pos];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `(candle_lc_zreal (candle_fs_scale_squared,0) / &denominator) /
     &candle_fs_scale` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC candle_fs_floor_div_sound THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `&0 < &(denominator)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `(candle_lc_zreal (candle_fs_scale_squared,0) / &denominator) /
       &candle_fs_scale =
       inv (&denominator / &candle_fs_scale)` SUBST1_TAC THENL
     [REWRITE_TAC[candle_lc_zreal_def; candle_fs_scale_squared_def;
                  FST; SND; REAL_SUB_RZERO; GSYM REAL_OF_NUM_MUL] THEN
      CONV_TAC REAL_FIELD;
      REWRITE_TAC[REAL_LE_REFL]]]);;

let candle_fs_hist_inv_upper = prove
 (`!denominator. 0 < denominator
     ==> inv (&denominator / &candle_fs_scale)
         <= candle_fs_real
              (candle_fs_ceil_div
                (candle_fs_scale_squared,0) denominator)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_real_def] THEN
  SUBGOAL_THEN `&0 < &(candle_fs_scale)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; candle_fs_scale_pos];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `(candle_lc_zreal (candle_fs_scale_squared,0) / &denominator) /
     &candle_fs_scale` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < &(denominator)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `(candle_lc_zreal (candle_fs_scale_squared,0) / &denominator) /
       &candle_fs_scale =
       inv (&denominator / &candle_fs_scale)` SUBST1_TAC THENL
     [REWRITE_TAC[candle_lc_zreal_def; candle_fs_scale_squared_def;
                  FST; SND; REAL_SUB_RZERO; GSYM REAL_OF_NUM_MUL] THEN
      CONV_TAC REAL_FIELD;
      REWRITE_TAC[REAL_LE_REFL]];
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC candle_fs_ceil_div_sound THEN ASM_ARITH_TAC]);;

let candle_fs_hist_positive_inv_contains = prove
 (`!lower upper x.
     0 < lower /\ lower <= upper /\
     candle_fs_interval_contains ((lower,0),(upper,0)) x
     ==> candle_fs_interval_contains
           (candle_fs_hist_positive_inv ((lower,0),(upper,0)))
           (inv x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_fs_interval_contains_def;
                  candle_fs_real_def; candle_lc_zreal_def; FST; SND;
                  REAL_SUB_RZERO]) THEN
  REWRITE_TAC[candle_fs_hist_positive_inv_def;
              candle_fs_interval_contains_def; FST; SND] THEN
  SUBGOAL_THEN `&0 < &lower / &candle_fs_scale` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; candle_fs_scale_pos];
    ALL_TAC] THEN
  MP_TAC
    (SPECL [`&lower / &candle_fs_scale`;
            `&upper / &candle_fs_scale`; `x:real`]
      candle_real_interval_inv_positive) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv (&upper / &candle_fs_scale)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_fs_hist_floor_inv_lower THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv (&lower / &candle_fs_scale)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_fs_hist_inv_upper THEN ASM_REWRITE_TAC[]]);;

(* Positive canonical interval products remain positive canonical after the
   fixed-scale product and directed rounding.  Exposing this shape is needed
   before the historical direct reciprocal may soundly consume denominators
   such as [root_delta * root_four_x0] and [u126 * u135]. *)

let candle_fs_hist_zmul_positive = prove
 (`!a b. candle_q_zmul (a,0) (b,0) = (a * b,0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_zmul_def; FST; SND; MULT_CLAUSES; ADD_CLAUSES]);;

let candle_fs_hist_raw_min_positive_left = prove
 (`!a b. a <= b
     ==> candle_fs_raw_min (a,0) (b,0) = (a,0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_min_def; candle_fs_raw_le_def; FST; SND;
              ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_raw_max_positive_right = prove
 (`!a b. a <= b
     ==> candle_fs_raw_max (a,0) (b,0) = (b,0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_max_def; candle_fs_raw_le_def; FST; SND;
              ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_raw_interval_mul_positive_shape = prove
 (`!lower_left upper_left lower_right upper_right.
     lower_left <= upper_left /\ lower_right <= upper_right
     ==> candle_fs_raw_interval_mul
           ((lower_left,0),(upper_left,0))
           ((lower_right,0),(upper_right,0)) =
         ((lower_left * lower_right,0),
          (upper_left * upper_right,0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`lower_left:num`; `lower_left:num`;
       `lower_right:num`; `upper_right:num`] LE_MULT2) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`upper_left:num`; `upper_left:num`;
       `lower_right:num`; `upper_right:num`] LE_MULT2) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`lower_left:num`; `upper_left:num`;
       `lower_right:num`; `lower_right:num`] LE_MULT2) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`lower_left:num`; `upper_left:num`;
       `upper_right:num`; `upper_right:num`] LE_MULT2) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fs_raw_interval_mul_def;
              candle_fs_hist_zmul_positive; FST; SND] THEN
  ASM_REWRITE_TAC[candle_fs_raw_min_def; candle_fs_raw_max_def;
                  candle_fs_raw_le_def; FST; SND; ADD_CLAUSES]);;

let candle_fs_hist_interval_mul_positive_shape = prove
 (`!lower_left upper_left lower_right upper_right.
     lower_left <= upper_left /\ lower_right <= upper_right
     ==> candle_fs_angle_interval_mul
           ((lower_left,0),(upper_left,0))
           ((lower_right,0),(upper_right,0)) =
         (((lower_left * lower_right) DIV candle_fs_scale,0),
          (candle_q_ceil_div (upper_left * upper_right)
             candle_fs_scale,0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_angle_interval_mul_def;
              candle_fsn_interval_mul_def] THEN
  ASM_SIMP_TAC[candle_fs_hist_raw_interval_mul_positive_shape] THEN
  REWRITE_TAC[candle_fs_raw_interval_round_def;
              candle_fs_floor_div_def; candle_fs_ceil_div_def;
              FST; SND; ARITH_RULE `~(n < 0)`; SUB_0]);;

let candle_fs_hist_div_le_ceil_div = prove
 (`!numerator denominator.
     numerator DIV denominator <=
     candle_q_ceil_div numerator denominator`,
  REPEAT GEN_TAC THEN REWRITE_TAC[candle_q_ceil_div_def] THEN
  COND_CASES_TAC THEN ARITH_TAC);;

let candle_fs_hist_interval_mul_positive_order = prove
 (`!lower_left upper_left lower_right upper_right.
     lower_left <= upper_left /\ lower_right <= upper_right
     ==> (lower_left * lower_right) DIV candle_fs_scale <=
         candle_q_ceil_div (upper_left * upper_right)
           candle_fs_scale`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(upper_left * upper_right) DIV candle_fs_scale` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIV_MONO THEN MATCH_MP_TAC LE_MULT2 THEN
    ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC candle_fs_hist_div_le_ceil_div]);;

let candle_fs_hist_positive_product_inv_def = new_definition
 `candle_fs_hist_positive_product_inv left right =
    candle_fs_hist_positive_inv
      (candle_fs_angle_interval_mul left right)`;;

let candle_cv_fs_hist_positive_product_inv_correct = prove
 (`!left right.
     candle_cv_fs_hist_positive_inv
       (candle_cv_fs_angle_interval_mul
         (candle_cv_fs_interval left) (candle_cv_fs_interval right)) =
     candle_cv_fs_interval
       (candle_fs_hist_positive_product_inv left right)`,
  REWRITE_TAC[candle_fs_hist_positive_product_inv_def;
              candle_cv_fs_angle_interval_mul_correct;
              candle_cv_fs_hist_positive_inv_correct]);;

let candle_fs_hist_positive_product_inv_contains = prove
 (`!lower_left upper_left lower_right upper_right x y.
     lower_left <= upper_left /\ lower_right <= upper_right /\
     0 < (lower_left * lower_right) DIV candle_fs_scale /\
     candle_fs_interval_contains
       ((lower_left,0),(upper_left,0)) x /\
     candle_fs_interval_contains
       ((lower_right,0),(upper_right,0)) y
     ==> candle_fs_interval_contains
           (candle_fs_hist_positive_product_inv
             ((lower_left,0),(upper_left,0))
             ((lower_right,0),(upper_right,0)))
           (inv (x * y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `candle_fs_interval_contains
       (candle_fs_angle_interval_mul
         ((lower_left,0),(upper_left,0))
         ((lower_right,0),(upper_right,0)))
       (x * y)` ASSUME_TAC THENL
   [REWRITE_TAC[candle_fs_angle_interval_mul_def] THEN
    MATCH_MP_TAC candle_fsn_interval_mul_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (SPECL
      [`lower_left:num`; `upper_left:num`;
       `lower_right:num`; `upper_right:num`]
      candle_fs_hist_interval_mul_positive_order) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`lower_left:num`; `upper_left:num`;
       `lower_right:num`; `upper_right:num`]
      candle_fs_hist_interval_mul_positive_shape) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `candle_fs_interval_contains
       (((lower_left * lower_right) DIV candle_fs_scale,0),
        (candle_q_ceil_div (upper_left * upper_right)
           candle_fs_scale,0))
       (x * y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[candle_fs_hist_positive_product_inv_def] THEN
  MATCH_MP_TAC candle_fs_hist_positive_inv_contains THEN
  ASM_REWRITE_TAC[]);;

(* Package the complete historical quotient boundary.  The executable uses
   the outward-rounded product [root_delta * root_four_x0] and its checked
   positive reciprocal before multiplying by [-delta_x4].  Keeping that
   sequence as one ordinary-HOL operation lets the final arctangent proof
   consume the exact quotient it needs without rebuilding intermediate
   arithmetic theorems per certificate leaf. *)

let candle_fs_hist_quotient_def = new_definition
 `candle_fs_hist_quotient
      (delta_x4_interval:(num#num)#(num#num)) root_delta root_four_x0 =
    candle_fs_angle_interval_mul
      (candle_fs_interval_neg delta_x4_interval)
      (candle_fs_hist_positive_product_inv root_delta root_four_x0)`;;

let candle_cv_fs_hist_quotient_correct = prove
 (`!delta_x4_interval root_delta root_four_x0.
     candle_cv_fs_angle_interval_mul
       (candle_cv_fs_interval_neg
         (candle_cv_fs_interval delta_x4_interval))
       (candle_cv_fs_hist_positive_inv
         (candle_cv_fs_angle_interval_mul
           (candle_cv_fs_interval root_delta)
           (candle_cv_fs_interval root_four_x0))) =
     candle_cv_fs_interval
       (candle_fs_hist_quotient
         delta_x4_interval root_delta root_four_x0)`,
  REWRITE_TAC[candle_fs_hist_quotient_def;
              candle_fs_hist_positive_product_inv_def;
              candle_cv_fs_interval_neg_correct;
              candle_cv_fs_angle_interval_mul_correct;
              candle_cv_fs_hist_positive_product_inv_correct]);;

let candle_fs_hist_quotient_contains = prove
 (`!delta_x4_interval root_lower root_upper
      root_four_lower root_four_upper
      delta_x4_real root_real root_four_real.
     candle_fs_interval_contains delta_x4_interval delta_x4_real /\
     root_lower <= root_upper /\
     root_four_lower <= root_four_upper /\
     0 < (root_lower * root_four_lower) DIV candle_fs_scale /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0)) root_real /\
     candle_fs_interval_contains
       ((root_four_lower,0),(root_four_upper,0)) root_four_real
     ==> candle_fs_interval_contains
           (candle_fs_hist_quotient delta_x4_interval
             ((root_lower,0),(root_upper,0))
             ((root_four_lower,0),(root_four_upper,0)))
           (--delta_x4_real * inv (root_real * root_four_real))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_quotient_def;
              candle_fs_angle_interval_mul_def] THEN
  MATCH_MP_TAC candle_fsn_interval_mul_contains THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_interval_neg_sound THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_positive_product_inv_contains THEN
    ASM_REWRITE_TAC[]]);;

(* The historical arctangent kernel uses a fixed Horner series whose rational
   coefficients are rounded once to the 2^40 grid.  This ordinary-HOL helper
   is the exact operation represented by [candle_cv_fs_hist_rational_constant].
   Its containment theorem is general in the signed numerator and nonzero
   natural denominator, so the subsequent Horner proof can reuse it for every
   alternating coefficient without coefficient-specific arithmetic proofs. *)

let candle_fs_hist_rational_constant_def = new_definition
 `candle_fs_hist_rational_constant positive negative denominator =
    let numerator = candle_lc_zscale candle_fs_scale
      (positive,negative) in
    candle_fs_raw_interval_round denominator (numerator,numerator)`;;

let candle_cv_fs_hist_rational_constant_correct = prove
 (`!positive negative denominator.
     candle_cv_fs_hist_rational_constant
       (Cexp_num positive) (Cexp_num negative) (Cexp_num denominator) =
     candle_cv_fs_interval
       (candle_fs_hist_rational_constant
         positive negative denominator)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_rational_constant_def;
              LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `candle_cv_fs_raw_scale candle_cv_fs_scale
      (Cexp_pair (Cexp_num positive) (Cexp_num negative)) =
    candle_cv_lc_z
      (candle_lc_zscale candle_fs_scale (positive,negative))`
  SUBST1_TAC THENL
   [REWRITE_TAC[candle_cv_fs_scale_correct;
                candle_cv_fs_raw_scale_def;
                candle_cv_lc_z_def; candle_lc_zscale_def;
                cexp_fst_def; cexp_snd_def; cexp_mul_def; FST; SND];
    REWRITE_TAC[candle_fs_hist_rational_constant_def;
                candle_fs_raw_interval_round_def;
                LET_DEF; LET_END_DEF;
                candle_cv_fs_floor_div_correct;
                candle_cv_fs_ceil_div_correct;
                candle_cv_fs_interval_def; FST; SND]]);;

let candle_fs_hist_scale_cancel = prove
 (`!z denominator.
     ~(denominator = 0)
     ==> (&candle_fs_scale * z) /
           (&denominator * &candle_fs_scale) = z / &denominator`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&denominator = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&(candle_fs_scale) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    MP_TAC candle_fs_scale_pos THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
    [`~(&denominator = &0)`;
     `~(&(candle_fs_scale) = &0)`] THEN
  CONV_TAC REAL_FIELD);;

let candle_fs_hist_rational_constant_contains = prove
 (`!positive negative denominator.
     ~(denominator = 0)
     ==> candle_fs_interval_contains
           (candle_fs_hist_rational_constant
             positive negative denominator)
           (candle_lc_zreal (positive,negative) / &denominator)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fs_hist_rational_constant_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC candle_fs_raw_interval_round_sound THEN
  CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_SIMP_TAC[candle_fs_raw_interval_contains_def;
                 candle_fs_raw_real_def; FST; SND;
                 candle_lc_zreal_scale; GSYM REAL_OF_NUM_MUL;
                 candle_fs_hist_scale_cancel; REAL_LE_REFL]]);;

let candle_fs_hist_point_def = new_definition
 `candle_fs_hist_point (value:num#num) = (value,value)`;;

let candle_fs_hist_point_contains = prove
 (`!value.
     candle_fs_interval_contains
       (candle_fs_hist_point value) (candle_fs_real value)`,
  REWRITE_TAC[candle_fs_hist_point_def;
              candle_fs_interval_contains_def; FST; SND;
              REAL_LE_REFL]);;

let candle_cv_fs_hist_point_correct = prove
 (`!value.
     candle_cv_fs_hist_point (candle_cv_lc_z value) =
     candle_cv_fs_interval (candle_fs_hist_point value)`,
  REWRITE_TAC[candle_cv_fs_hist_point_def; candle_fs_hist_point_def;
              candle_cv_fs_interval_def; FST; SND]);;

let candle_fs_hist_atan_pos_lower_def = new_definition
 `candle_fs_hist_atan_pos_lower x =
    let point = candle_fs_hist_point x in
    let x2 = candle_fs_angle_interval_mul point point in
    let polynomial = candle_fs_hist_rational_constant 0 1 11 in
    let polynomial = candle_fs_interval_add
      (candle_fs_hist_rational_constant 1 0 9)
      (candle_fs_angle_interval_mul x2 polynomial) in
    let polynomial = candle_fs_interval_add
      (candle_fs_hist_rational_constant 0 1 7)
      (candle_fs_angle_interval_mul x2 polynomial) in
    let polynomial = candle_fs_interval_add
      (candle_fs_hist_rational_constant 1 0 5)
      (candle_fs_angle_interval_mul x2 polynomial) in
    let polynomial = candle_fs_interval_add
      (candle_fs_hist_rational_constant 0 1 3)
      (candle_fs_angle_interval_mul x2 polynomial) in
    candle_fs_angle_interval_mul point
      (candle_fs_interval_add candle_fs_interval_one
        (candle_fs_angle_interval_mul x2 polynomial))`;;

let candle_cv_fs_hist_atan_pos_lower_correct = prove
 (`!x.
     candle_cv_fs_hist_atan_pos_lower (candle_cv_lc_z x) =
     candle_cv_fs_interval (candle_fs_hist_atan_pos_lower x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_atan_pos_lower_def;
              candle_fs_hist_atan_pos_lower_def;
              LET_DEF; LET_END_DEF;
              candle_cv_fs_hist_point_correct;
              candle_cv_fs_hist_rational_constant_correct;
              candle_cv_fs_angle_interval_mul_correct;
              candle_cv_fs_interval_add_correct;
              candle_cv_fs_interval_one_correct]);;

let candle_fs_hist_atan_pos_lower_target_def = new_definition
 `candle_fs_hist_atan_pos_lower_target x =
    let x2 = x * x in
    x * (&1 + x2 *
      (candle_lc_zreal (0,1) / &3 + x2 *
        (candle_lc_zreal (1,0) / &5 + x2 *
          (candle_lc_zreal (0,1) / &7 + x2 *
            (candle_lc_zreal (1,0) / &9 + x2 *
              (candle_lc_zreal (0,1) / &11))))))`;;

let candle_fs_hist_angle_mul_contains = prove
 (`!left right x y.
     candle_fs_interval_contains left x /\
     candle_fs_interval_contains right y
     ==> candle_fs_interval_contains
           (candle_fs_angle_interval_mul left right) (x * y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_angle_interval_mul_def] THEN
  MATCH_ACCEPT_TAC candle_fsn_interval_mul_contains);;

let candle_fs_hist_horner_step_contains = prove
 (`!coefficient square tail coefficient_real square_real tail_real.
     candle_fs_interval_contains coefficient coefficient_real /\
     candle_fs_interval_contains square square_real /\
     candle_fs_interval_contains tail tail_real
     ==> candle_fs_interval_contains
           (candle_fs_interval_add coefficient
             (candle_fs_angle_interval_mul square tail))
           (coefficient_real + square_real * tail_real)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_interval_add_sound THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_atan_pos_lower_contains = prove
 (`!x.
     candle_fs_interval_contains
       (candle_fs_hist_atan_pos_lower x)
       (candle_fs_hist_atan_pos_lower_target (candle_fs_real x))`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_atan_pos_lower_def;
              candle_fs_hist_atan_pos_lower_target_def;
              LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `point = candle_fs_hist_point x` THEN
  ABBREV_TAC
    `square = candle_fs_angle_interval_mul point point` THEN
  ABBREV_TAC `xreal = candle_fs_real x` THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains point xreal` ASSUME_TAC THENL
   [EXPAND_TAC "point" THEN EXPAND_TAC "xreal" THEN
    MATCH_ACCEPT_TAC candle_fs_hist_point_contains;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains square (xreal * xreal)` ASSUME_TAC THENL
   [EXPAND_TAC "square" THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`0`; `1`; `11`]
    candle_fs_hist_rational_constant_contains) THEN
  MP_TAC(SPECL [`1`; `0`; `9`]
    candle_fs_hist_rational_constant_contains) THEN
  MP_TAC(SPECL [`0`; `1`; `7`]
    candle_fs_hist_rational_constant_contains) THEN
  MP_TAC(SPECL [`1`; `0`; `5`]
    candle_fs_hist_rational_constant_contains) THEN
  MP_TAC(SPECL [`0`; `1`; `3`]
    candle_fs_hist_rational_constant_contains) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC
   `p9 = candle_fs_interval_add
      (candle_fs_hist_rational_constant 1 0 9)
      (candle_fs_angle_interval_mul square
        (candle_fs_hist_rational_constant 0 1 11))` THEN
  ABBREV_TAC
   `r9 = candle_lc_zreal (1,0) / &9 +
      (xreal * xreal) * (candle_lc_zreal (0,1) / &11)` THEN
  SUBGOAL_THEN `candle_fs_interval_contains p9 r9` ASSUME_TAC THENL
   [EXPAND_TAC "p9" THEN EXPAND_TAC "r9" THEN
    MATCH_MP_TAC candle_fs_hist_horner_step_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `p7 = candle_fs_interval_add
      (candle_fs_hist_rational_constant 0 1 7)
      (candle_fs_angle_interval_mul square p9)` THEN
  ABBREV_TAC
   `r7 = candle_lc_zreal (0,1) / &7 + (xreal * xreal) * r9` THEN
  SUBGOAL_THEN `candle_fs_interval_contains p7 r7` ASSUME_TAC THENL
   [EXPAND_TAC "p7" THEN EXPAND_TAC "r7" THEN
    MATCH_MP_TAC candle_fs_hist_horner_step_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `p5 = candle_fs_interval_add
      (candle_fs_hist_rational_constant 1 0 5)
      (candle_fs_angle_interval_mul square p7)` THEN
  ABBREV_TAC
   `r5 = candle_lc_zreal (1,0) / &5 + (xreal * xreal) * r7` THEN
  SUBGOAL_THEN `candle_fs_interval_contains p5 r5` ASSUME_TAC THENL
   [EXPAND_TAC "p5" THEN EXPAND_TAC "r5" THEN
    MATCH_MP_TAC candle_fs_hist_horner_step_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `p3 = candle_fs_interval_add
      (candle_fs_hist_rational_constant 0 1 3)
      (candle_fs_angle_interval_mul square p5)` THEN
  ABBREV_TAC
   `r3 = candle_lc_zreal (0,1) / &3 + (xreal * xreal) * r5` THEN
  SUBGOAL_THEN `candle_fs_interval_contains p3 r3` ASSUME_TAC THENL
   [EXPAND_TAC "p3" THEN EXPAND_TAC "r3" THEN
    MATCH_MP_TAC candle_fs_hist_horner_step_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_interval_add_sound THEN
    CONJ_TAC THENL
     [MATCH_ACCEPT_TAC candle_fs_interval_one_contains;
      MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      ASM_REWRITE_TAC[]]]);;

let candle_fs_hist_atan_pos_lower_target_expanded = prove
 (`!x.
     candle_fs_hist_atan_pos_lower_target x =
     x - x pow 3 / &3 + x pow 5 / &5 - x pow 7 / &7 +
     x pow 9 / &9 - x pow 11 / &11`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_atan_pos_lower_target_def;
              candle_lc_zreal_def; FST; SND;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC REAL_RING);;

let candle_fs_hist_atan_pos_lower_sum_expanded = prove
 (`!x.
     sum (0..5)
       (\i. ((-- &1) pow i / &(2 * i + 1)) * x pow (2 * i + 1)) =
     x - x pow 3 / &3 + x pow 5 / &5 - x pow 7 / &7 +
     x pow 9 / &9 - x pow 11 / &11`,
  GEN_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  CONV_TAC (LAND_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC REAL_RING);;

let candle_fs_hist_atan_pos_lower_target_series = prove
 (`!x.
     candle_fs_hist_atan_pos_lower_target x =
     sum (0..5)
       (\i. ((-- &1) pow i / &(2 * i + 1)) * x pow (2 * i + 1))`,
  REWRITE_TAC[candle_fs_hist_atan_pos_lower_target_expanded;
              candle_fs_hist_atan_pos_lower_sum_expanded]);;

(* This is the first complete subterm used by both the first- and second-order
   historical instructions: [2 / root_four_x0].  Keeping the ordinary-HOL
   helper at the exact executable boundary makes the subsequent jet proof
   reuse one cval representation theorem and one semantic enclosure theorem. *)

let candle_fs_hist_two_over_positive_root_def = new_definition
 `candle_fs_hist_two_over_positive_root
      (positive_interval:(num#num)#(num#num)) =
    candle_fs_angle_interval_mul
      (candle_fs_angle_interval_scale 2 candle_fs_interval_one)
      (candle_fs_hist_positive_inv positive_interval)`;;

let candle_cv_fs_hist_two_over_positive_root_correct = prove
 (`!positive_interval.
     candle_cv_fs_angle_interval_mul
       (candle_cv_fs_angle_interval_scale
         (Cexp_num 2) candle_cv_fs_interval_one)
       (candle_cv_fs_hist_positive_inv
         (candle_cv_fs_interval positive_interval)) =
     candle_cv_fs_interval
       (candle_fs_hist_two_over_positive_root positive_interval)`,
  REWRITE_TAC[candle_fs_hist_two_over_positive_root_def;
              candle_cv_fs_interval_one_correct;
              candle_cv_fs_angle_interval_scale_correct;
              candle_cv_fs_hist_positive_inv_correct;
              candle_cv_fs_angle_interval_mul_correct]);;

let candle_fs_hist_two_over_positive_root_contains = prove
 (`!lower upper x.
     0 < lower /\ lower <= upper /\
     candle_fs_interval_contains ((lower,0),(upper,0)) x
     ==> candle_fs_interval_contains
           (candle_fs_hist_two_over_positive_root
             ((lower,0),(upper,0)))
           (&2 * inv x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_two_over_positive_root_def;
              candle_fs_angle_interval_mul_def] THEN
  MATCH_MP_TAC candle_fsn_interval_mul_contains THEN
  CONJ_TAC THENL
   [MP_TAC candle_fs_interval_one_contains THEN
    DISCH_THEN
      (MP_TAC o MATCH_MP
        (SPECL [`2`; `candle_fs_interval_one`; `&1`]
          candle_fs_angle_interval_scale_contains)) THEN
    REWRITE_TAC[REAL_MUL_RID];
    MATCH_MP_TAC candle_fs_hist_positive_inv_contains THEN
    ASM_REWRITE_TAC[]]);;

(* The companion recurring root subterm is [1 / (2 * positive_root)].  It is
   the derivative enclosure used by the supplied-square-root path. *)

let candle_fs_hist_inv_twice_positive_def = new_definition
 `candle_fs_hist_inv_twice_positive
      (positive_interval:(num#num)#(num#num)) =
    candle_fs_hist_positive_inv
      (candle_fs_angle_interval_scale 2 positive_interval)`;;

let candle_cv_fs_hist_inv_twice_positive_correct = prove
 (`!positive_interval.
     candle_cv_fs_hist_positive_inv
       (candle_cv_fs_angle_interval_scale
         (Cexp_num 2) (candle_cv_fs_interval positive_interval)) =
     candle_cv_fs_interval
       (candle_fs_hist_inv_twice_positive positive_interval)`,
  REWRITE_TAC[candle_fs_hist_inv_twice_positive_def;
              candle_cv_fs_angle_interval_scale_correct;
              candle_cv_fs_hist_positive_inv_correct]);;

let candle_fs_hist_inv_twice_positive_contains = prove
 (`!lower upper x.
     0 < lower /\ lower <= upper /\
     candle_fs_interval_contains ((lower,0),(upper,0)) x
     ==> candle_fs_interval_contains
           (candle_fs_hist_inv_twice_positive
             ((lower,0),(upper,0)))
           (inv (&2 * x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `candle_fs_interval_contains
       ((2 * lower,0),(2 * upper,0)) (&2 * x)` ASSUME_TAC THENL
   [MP_TAC
      (SPECL [`2:num`;
              `(((lower,0),(upper,0)):(num#num)#(num#num))`;
              `x:real`]
        candle_fs_angle_interval_scale_contains) THEN
    ASM_REWRITE_TAC[candle_fs_angle_interval_scale_def;
                    candle_lc_zscale_def; FST; SND; MULT_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_inv_twice_positive_def;
              candle_fs_angle_interval_scale_def;
              candle_lc_zscale_def; FST; SND; MULT_CLAUSES] THEN
  MATCH_MP_TAC candle_fs_hist_positive_inv_contains THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* This is the complete special-gradient scalar used by both historical
   orders: [numerator / (2 * positive_root)]. *)

let candle_fs_hist_over_twice_positive_def = new_definition
 `candle_fs_hist_over_twice_positive numerator positive_interval =
    candle_fs_angle_interval_mul numerator
      (candle_fs_hist_inv_twice_positive positive_interval)`;;

let candle_cv_fs_hist_over_twice_positive_correct = prove
 (`!numerator positive_interval.
     candle_cv_fs_angle_interval_mul
       (candle_cv_fs_interval numerator)
       (candle_cv_fs_hist_positive_inv
         (candle_cv_fs_angle_interval_scale
           (Cexp_num 2) (candle_cv_fs_interval positive_interval))) =
     candle_cv_fs_interval
       (candle_fs_hist_over_twice_positive
         numerator positive_interval)`,
  REWRITE_TAC[candle_fs_hist_over_twice_positive_def;
              candle_cv_fs_hist_inv_twice_positive_correct;
              candle_cv_fs_angle_interval_mul_correct]);;

let candle_fs_hist_over_twice_positive_contains = prove
 (`!numerator lower upper y x.
     candle_fs_interval_contains numerator y /\
     0 < lower /\ lower <= upper /\
     candle_fs_interval_contains ((lower,0),(upper,0)) x
     ==> candle_fs_interval_contains
           (candle_fs_hist_over_twice_positive
             numerator ((lower,0),(upper,0)))
           (y * inv (&2 * x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_over_twice_positive_def;
              candle_fs_angle_interval_mul_def] THEN
  MATCH_MP_TAC candle_fsn_interval_mul_contains THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_fs_hist_inv_twice_positive_contains THEN
  ASM_REWRITE_TAC[]);;

(* Lift the square-root derivative scalar through the generally proved list
   scale.  This is the complete [root_delta_gradient] construction shared by
   the first-order and supplied-square-root second-order paths. *)

let candle_fs_hist_positive_sqrt_gradient_def = new_definition
 `candle_fs_hist_positive_sqrt_gradient positive_interval gradient =
    candle_fsn_interval_list_scale
      (candle_fs_hist_inv_twice_positive positive_interval) gradient`;;

let candle_cv_fs_hist_positive_sqrt_gradient_correct = prove
 (`!positive_interval gradient.
     candle_cv_fsn_interval_list_scale
       (candle_cv_fs_hist_positive_inv
         (candle_cv_fs_angle_interval_scale
           (Cexp_num 2) (candle_cv_fs_interval positive_interval)))
       (candle_cv_fs_interval_list gradient) =
     candle_cv_fs_interval_list
       (candle_fs_hist_positive_sqrt_gradient
         positive_interval gradient)`,
  REWRITE_TAC[candle_fs_hist_positive_sqrt_gradient_def;
              candle_cv_fs_hist_inv_twice_positive_correct;
              candle_cv_fsn_interval_list_scale_correct]);;

let candle_fs_hist_positive_sqrt_gradient_contains = prove
 (`!lower upper x gradient gradient_values.
     0 < lower /\ lower <= upper /\
     candle_fs_interval_contains ((lower,0),(upper,0)) x /\
     ALL2 candle_fs_interval_contains gradient gradient_values
     ==> ALL2 candle_fs_interval_contains
           (candle_fs_hist_positive_sqrt_gradient
             ((lower,0),(upper,0)) gradient)
           (MAP (\g:real. inv (&2 * x) * g) gradient_values)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_positive_sqrt_gradient_def] THEN
  MATCH_MP_TAC candle_fsn_interval_list_scale_contains THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_fs_hist_inv_twice_positive_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_positive_sqrt_gradient_universal_contains = prove
 (`!root_lower root_upper input_real gradient gradient_real.
     0 < root_lower /\ root_lower <= root_upper /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0)) (sqrt input_real) /\
     ALL2 candle_fs_interval_contains gradient gradient_real
     ==> ALL2 candle_fs_interval_contains
           (candle_fs_hist_positive_sqrt_gradient
             ((root_lower,0),(root_upper,0)) gradient)
           (MAP
             (\g:real. inv (sqrt input_real + sqrt input_real) * g)
             gradient_real)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `x + x = &2 * x`] THEN
  MATCH_MP_TAC candle_fs_hist_positive_sqrt_gradient_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_sqrt_scalars_contains = prove
 (`!input_lower input_upper root_lower root_upper input_real root_real.
     0 < input_lower /\ input_lower <= input_upper /\
     0 < root_lower /\ root_lower <= root_upper /\
     candle_fs_interval_contains
       ((input_lower,0),(input_upper,0)) input_real /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0)) root_real
     ==> candle_fs_interval_contains
           (candle_fs_hist_inv_twice_positive
             ((root_lower,0),(root_upper,0)))
           (inv (&2 * root_real)) /\
         candle_fs_interval_contains
           (candle_fs_interval_neg
             (candle_fs_hist_inv_twice_positive
               ((input_lower,0),(input_upper,0))))
           (--inv (&2 * input_real))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_inv_twice_positive_contains THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_inv_twice_positive_contains THEN
    ASM_REWRITE_TAC[]]);;

(* The supplied-square-root evaluator uses a symmetry-aware six-by-six
   constructor rather than the generic matrix combinators.  Expose its exact
   ordinary-HOL operation before proving the analytic Hessian invariant. *)

let candle_fs_hist_sqrt_hessian_entry_def = new_definition
 `candle_fs_hist_sqrt_hessian_entry rowindex colindex derivative_value
      logarithmic_derivative input_gradient input_hessian =
    let scaled_row = candle_fs_angle_interval_mul
      logarithmic_derivative
      (candle_fs_interval_lookup rowindex input_gradient) in
    let inside = candle_fs_interval_add
      (candle_fs_angle_interval_mul
        (candle_fs_interval_lookup colindex input_gradient) scaled_row)
      (candle_fs_angle_matrix_lookup
        rowindex colindex input_hessian) in
    candle_fs_angle_interval_mul derivative_value inside`;;

let candle_fs_hist_sqrt_hessian_symmetric_entry_def = new_definition
 `candle_fs_hist_sqrt_hessian_symmetric_entry rowindex colindex
      derivative_value logarithmic_derivative input_gradient input_hessian =
    if colindex < rowindex then
      candle_fs_hist_sqrt_hessian_entry colindex rowindex derivative_value
        logarithmic_derivative input_gradient input_hessian
    else
      candle_fs_hist_sqrt_hessian_entry rowindex colindex derivative_value
        logarithmic_derivative input_gradient input_hessian`;;

let candle_fs_hist_sqrt_hessian_row_def = new_definition
 `candle_fs_hist_sqrt_hessian_row rowindex derivative_value
      logarithmic_derivative input_gradient input_hessian =
    [candle_fs_hist_sqrt_hessian_symmetric_entry rowindex 0 derivative_value
       logarithmic_derivative input_gradient input_hessian;
     candle_fs_hist_sqrt_hessian_symmetric_entry rowindex 1 derivative_value
       logarithmic_derivative input_gradient input_hessian;
     candle_fs_hist_sqrt_hessian_symmetric_entry rowindex 2 derivative_value
       logarithmic_derivative input_gradient input_hessian;
     candle_fs_hist_sqrt_hessian_symmetric_entry rowindex 3 derivative_value
       logarithmic_derivative input_gradient input_hessian;
     candle_fs_hist_sqrt_hessian_symmetric_entry rowindex 4 derivative_value
       logarithmic_derivative input_gradient input_hessian;
     candle_fs_hist_sqrt_hessian_symmetric_entry rowindex 5 derivative_value
       logarithmic_derivative input_gradient input_hessian]`;;

let candle_fs_hist_sqrt_hessian_def = new_definition
 `candle_fs_hist_sqrt_hessian derivative_value logarithmic_derivative
      input_gradient input_hessian =
    [candle_fs_hist_sqrt_hessian_row 0 derivative_value
       logarithmic_derivative input_gradient input_hessian;
     candle_fs_hist_sqrt_hessian_row 1 derivative_value
       logarithmic_derivative input_gradient input_hessian;
     candle_fs_hist_sqrt_hessian_row 2 derivative_value
       logarithmic_derivative input_gradient input_hessian;
     candle_fs_hist_sqrt_hessian_row 3 derivative_value
       logarithmic_derivative input_gradient input_hessian;
     candle_fs_hist_sqrt_hessian_row 4 derivative_value
       logarithmic_derivative input_gradient input_hessian;
     candle_fs_hist_sqrt_hessian_row 5 derivative_value
       logarithmic_derivative input_gradient input_hessian]`;;

(* The historical constructor indexes the input jet directly.  These small
   structural lemmas keep that implementation detail out of the analytic
   proof below. *)

let candle_fs_interval_lookup_el = prove
 (`!lookup_index intervals.
     lookup_index < LENGTH intervals
     ==> candle_fs_interval_lookup lookup_index intervals =
         EL lookup_index intervals`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_interval_lookup_def; LENGTH; EL; HD; TL;
                  LT; LT_SUC]);;

let candle_fs_angle_matrix_row_lookup_el = prove
 (`!rowindex matrixvalue.
     rowindex < LENGTH matrixvalue
     ==> candle_fs_angle_matrix_row_lookup rowindex matrixvalue =
         EL rowindex matrixvalue`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_angle_matrix_row_lookup_def; LENGTH; EL; HD; TL;
                  LT; LT_SUC]);;

let candle_fs_hist_all2_el_right = prove
 (`!P xs ys lookup_index.
     ALL2 P xs ys /\ lookup_index < LENGTH ys
     ==> P (EL lookup_index xs) (EL lookup_index ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; LENGTH; LT];
    LIST_INDUCT_TAC THENL
     [REWRITE_TAC[ALL2];
      INDUCT_TAC THEN
      ASM_REWRITE_TAC[ALL2; LENGTH; EL; HD; TL; LT_SUC] THEN
      ASM_MESON_TAC[]]]);;

let candle_fs_hist_all_el = prove
 (`!P items item_index.
     ALL P items /\ item_index < LENGTH items
     ==> P (EL item_index items)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LT];
    INDUCT_TAC THEN
    ASM_REWRITE_TAC[ALL; LENGTH; EL; HD; TL; LT_SUC] THEN
    ASM_MESON_TAC[]]);;

let candle_fs_hist_matrix_row_length = prove
 (`!n matrixvalue rowindex.
     ALL (\matrix_row:((num#num)#(num#num))list.
       LENGTH matrix_row = n) matrixvalue /\
     rowindex < LENGTH matrixvalue
     ==> LENGTH (EL rowindex matrixvalue) = n`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LT];
    INDUCT_TAC THEN
    ASM_REWRITE_TAC[ALL; LENGTH; EL; HD; TL; LT_SUC] THEN
    ASM_MESON_TAC[]]);;

let candle_fs_hist_interval_lookup_contains = prove
 (`!n intervals (values:num->real) lookup_index.
     LENGTH intervals = n /\
     ALL2 candle_fs_interval_contains intervals (list_of_seq values n) /\
     lookup_index < n
     ==> candle_fs_interval_contains
           (candle_fs_interval_lookup lookup_index intervals)
           (values lookup_index)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_lookup lookup_index intervals =
    EL lookup_index intervals`
  SUBST1_TAC THENL
   [MATCH_MP_TAC candle_fs_interval_lookup_el THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `EL lookup_index (list_of_seq (values:num->real) n) =
    values lookup_index`
  (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [MATCH_MP_TAC EL_LIST_OF_SEQ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_all2_el_right THEN
    ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ]]);;

let candle_fs_hist_matrix_row_contains = prove
 (`!n matrixvalue (values:num->num->real) rowindex.
     LENGTH matrixvalue = n /\
     ALL (\matrix_row. LENGTH matrix_row = n) matrixvalue /\
     ALL2 (ALL2 candle_fs_interval_contains) matrixvalue
       (list_of_seq (\i. list_of_seq (values i) n) n) /\
     rowindex < n
     ==> LENGTH (EL rowindex matrixvalue) = n /\
         ALL2 candle_fs_interval_contains (EL rowindex matrixvalue)
           (list_of_seq (values rowindex) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC
      (ISPECL
        [`n:num`; `matrixvalue:(((num#num)#(num#num))list)list`;
         `rowindex:num`]
        candle_fs_hist_matrix_row_length) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `EL rowindex
        (list_of_seq (\i. list_of_seq ((values:num->num->real) i) n) n) =
      list_of_seq (values rowindex) n`
    (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
     [MATCH_MP_TAC EL_LIST_OF_SEQ THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_fs_hist_all2_el_right THEN
      ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ]]]);;

let candle_fs_hist_matrix_lookup_contains = prove
 (`!n matrixvalue (values:num->num->real) rowindex colindex.
     LENGTH matrixvalue = n /\
     ALL (\matrix_row. LENGTH matrix_row = n) matrixvalue /\
     ALL2 (ALL2 candle_fs_interval_contains) matrixvalue
       (list_of_seq (\i. list_of_seq (values i) n) n) /\
     rowindex < n /\ colindex < n
     ==> candle_fs_interval_contains
           (candle_fs_angle_matrix_lookup rowindex colindex matrixvalue)
           (values rowindex colindex)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_angle_matrix_lookup_def] THEN
  ASM_MESON_TAC[candle_fs_angle_matrix_row_lookup_el;
                candle_fs_hist_matrix_row_contains;
                candle_fs_hist_interval_lookup_contains]);;

(* Local semantic contract for one supplied-square-root Hessian entry.  The
   scalar derivative enclosures are deliberately parameters here: subsequent
   instruction soundness only has to connect the historical root operations
   to the universal sqrt derivatives once. *)

let candle_fs_hist_sqrt_hessian_entry_contains = prove
 (`!n rowindex colindex derivative_value logarithmic_derivative
      input_gradient input_hessian derivative_real logarithmic_real
      (gradient_real:num->real) (hessian_real:num->num->real).
     rowindex < n /\ colindex < n /\
     LENGTH input_gradient = n /\
     LENGTH input_hessian = n /\
     ALL (\matrix_row. LENGTH matrix_row = n) input_hessian /\
     candle_fs_interval_contains derivative_value derivative_real /\
     candle_fs_interval_contains logarithmic_derivative logarithmic_real /\
     ALL2 candle_fs_interval_contains input_gradient
       (list_of_seq gradient_real n) /\
     ALL2 (ALL2 candle_fs_interval_contains) input_hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) n) n)
     ==> candle_fs_interval_contains
           (candle_fs_hist_sqrt_hessian_entry rowindex colindex
             derivative_value logarithmic_derivative input_gradient
             input_hessian)
           (derivative_real *
             (gradient_real colindex *
                (logarithmic_real * gradient_real rowindex) +
              hessian_real rowindex colindex))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_entry_def;
              candle_fs_angle_interval_mul_def;
              LET_DEF; LET_END_DEF] THEN
  ASM_MESON_TAC[candle_fsn_interval_mul_contains;
                candle_fs_interval_add_sound;
                candle_fs_hist_interval_lookup_contains;
                candle_fs_hist_matrix_lookup_contains]);;

(* The executable stores only the upper-triangular formula and mirrors it
   when building the six-by-six matrix.  Keep that exact executable component
   visible here; the later analytic bridge is responsible for using Hessian
   symmetry once to identify it with the standard chain-rule component. *)

let candle_fs_hist_sqrt_hessian_component_def = new_definition
 `candle_fs_hist_sqrt_hessian_component rowindex colindex derivative_real
      logarithmic_real (gradient_real:num->real)
      (hessian_real:num->num->real) =
    if colindex < rowindex then
      derivative_real *
        (gradient_real rowindex *
           (logarithmic_real * gradient_real colindex) +
         hessian_real colindex rowindex)
    else
      derivative_real *
        (gradient_real colindex *
           (logarithmic_real * gradient_real rowindex) +
         hessian_real rowindex colindex)`;;

let candle_fs_hist_sqrt_hessian_symmetric_entry_contains = prove
 (`!n rowindex colindex derivative_value logarithmic_derivative
      input_gradient input_hessian derivative_real logarithmic_real
      (gradient_real:num->real) (hessian_real:num->num->real).
     rowindex < n /\ colindex < n /\
     LENGTH input_gradient = n /\
     LENGTH input_hessian = n /\
     ALL (\matrix_row. LENGTH matrix_row = n) input_hessian /\
     candle_fs_interval_contains derivative_value derivative_real /\
     candle_fs_interval_contains logarithmic_derivative logarithmic_real /\
     ALL2 candle_fs_interval_contains input_gradient
       (list_of_seq gradient_real n) /\
     ALL2 (ALL2 candle_fs_interval_contains) input_hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) n) n)
     ==> candle_fs_interval_contains
           (candle_fs_hist_sqrt_hessian_symmetric_entry rowindex colindex
             derivative_value logarithmic_derivative input_gradient
             input_hessian)
           (candle_fs_hist_sqrt_hessian_component rowindex colindex
             derivative_real logarithmic_real gradient_real hessian_real)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_symmetric_entry_def;
              candle_fs_hist_sqrt_hessian_component_def] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC
      (SPEC `n:num` candle_fs_hist_sqrt_hessian_entry_contains) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC
      (SPEC `n:num` candle_fs_hist_sqrt_hessian_entry_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_sqrt_hessian_row_list_of_seq = prove
 (`!rowindex derivative_value logarithmic_derivative
      input_gradient input_hessian.
     candle_fs_hist_sqrt_hessian_row rowindex derivative_value
       logarithmic_derivative input_gradient input_hessian =
     list_of_seq
       (\colindex.
          candle_fs_hist_sqrt_hessian_symmetric_entry rowindex colindex
            derivative_value logarithmic_derivative input_gradient
            input_hessian) 6`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_row_def;
              num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND]);;

let candle_fs_hist_sqrt_hessian_list_of_seq = prove
 (`!derivative_value logarithmic_derivative input_gradient input_hessian.
     candle_fs_hist_sqrt_hessian derivative_value logarithmic_derivative
       input_gradient input_hessian =
     list_of_seq
       (\rowindex.
          candle_fs_hist_sqrt_hessian_row rowindex derivative_value
            logarithmic_derivative input_gradient input_hessian) 6`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_def;
              num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND]);;

let candle_fs_hist_sqrt_hessian_contains = prove
 (`!derivative_value logarithmic_derivative input_gradient input_hessian
      derivative_real logarithmic_real
      (gradient_real:num->real) (hessian_real:num->num->real).
     LENGTH input_gradient = 6 /\
     LENGTH input_hessian = 6 /\
     ALL (\matrix_row. LENGTH matrix_row = 6) input_hessian /\
     candle_fs_interval_contains derivative_value derivative_real /\
     candle_fs_interval_contains logarithmic_derivative logarithmic_real /\
     ALL2 candle_fs_interval_contains input_gradient
       (list_of_seq gradient_real 6) /\
     ALL2 (ALL2 candle_fs_interval_contains) input_hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) 6) 6)
     ==> ALL2 (ALL2 candle_fs_interval_contains)
           (candle_fs_hist_sqrt_hessian derivative_value
             logarithmic_derivative input_gradient input_hessian)
           (list_of_seq
             (\i. list_of_seq
               (\j. candle_fs_hist_sqrt_hessian_component i j
                 derivative_real logarithmic_real gradient_real
                 hessian_real) 6) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_list_of_seq;
              candle_all2_list_of_seq] THEN
  X_GEN_TAC `rowindex:num` THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_row_list_of_seq;
              candle_all2_list_of_seq] THEN
  X_GEN_TAC `colindex:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC
    (SPEC `6` candle_fs_hist_sqrt_hessian_symmetric_entry_contains) THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_sqrt_hessian_component_symmetric = prove
 (`!rowindex colindex derivative_real logarithmic_real
      (gradient_real:num->real) (hessian_real:num->num->real).
     (!i j. hessian_real i j = hessian_real j i)
     ==> candle_fs_hist_sqrt_hessian_component rowindex colindex
           derivative_real logarithmic_real gradient_real hessian_real =
         derivative_real *
           (gradient_real colindex *
              (logarithmic_real * gradient_real rowindex) +
            hessian_real rowindex colindex)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_component_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_AC]);;

let candle_fs_hist_sqrt_hessian_chain_contains = prove
 (`!derivative_value logarithmic_derivative input_gradient input_hessian
      derivative_real logarithmic_real
      (gradient_real:num->real) (hessian_real:num->num->real).
     LENGTH input_gradient = 6 /\
     LENGTH input_hessian = 6 /\
     ALL (\matrix_row. LENGTH matrix_row = 6) input_hessian /\
     candle_fs_interval_contains derivative_value derivative_real /\
     candle_fs_interval_contains logarithmic_derivative logarithmic_real /\
     ALL2 candle_fs_interval_contains input_gradient
       (list_of_seq gradient_real 6) /\
     ALL2 (ALL2 candle_fs_interval_contains) input_hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) 6) 6) /\
     (!i j. hessian_real i j = hessian_real j i)
     ==> ALL2 (ALL2 candle_fs_interval_contains)
           (candle_fs_hist_sqrt_hessian derivative_value
             logarithmic_derivative input_gradient input_hessian)
           (list_of_seq
             (\i. list_of_seq
               (\j. derivative_real *
                 (gradient_real j *
                    (logarithmic_real * gradient_real i) +
                  hessian_real i j)) 6) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_list_of_seq;
              candle_all2_list_of_seq] THEN
  X_GEN_TAC `rowindex:num` THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_row_list_of_seq;
              candle_all2_list_of_seq] THEN
  X_GEN_TAC `colindex:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `candle_fs_hist_sqrt_hessian_component rowindex colindex
      derivative_real logarithmic_real gradient_real hessian_real =
    derivative_real *
      (gradient_real colindex *
         (logarithmic_real * gradient_real rowindex) +
       hessian_real rowindex colindex)`
  (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
   [MATCH_MP_TAC candle_fs_hist_sqrt_hessian_component_symmetric THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPEC `6` candle_fs_hist_sqrt_hessian_symmetric_entry_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_positive_sqrt_hessian_contains = prove
 (`!input_lower input_upper root_lower root_upper input_real root_real
      input_gradient input_hessian
      (gradient_real:num->real) (hessian_real:num->num->real).
     0 < input_lower /\ input_lower <= input_upper /\
     0 < root_lower /\ root_lower <= root_upper /\
     candle_fs_interval_contains
       ((input_lower,0),(input_upper,0)) input_real /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0)) root_real /\
     LENGTH input_gradient = 6 /\
     LENGTH input_hessian = 6 /\
     ALL (\matrix_row. LENGTH matrix_row = 6) input_hessian /\
     ALL2 candle_fs_interval_contains input_gradient
       (list_of_seq gradient_real 6) /\
     ALL2 (ALL2 candle_fs_interval_contains) input_hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) 6) 6) /\
     (!i j. hessian_real i j = hessian_real j i)
     ==> ALL2 (ALL2 candle_fs_interval_contains)
           (candle_fs_hist_sqrt_hessian
             (candle_fs_hist_inv_twice_positive
               ((root_lower,0),(root_upper,0)))
             (candle_fs_interval_neg
               (candle_fs_hist_inv_twice_positive
                 ((input_lower,0),(input_upper,0))))
             input_gradient input_hessian)
           (list_of_seq
             (\i. list_of_seq
               (\j. inv (&2 * root_real) *
                 (gradient_real j *
                    ((--inv (&2 * input_real)) * gradient_real i) +
                  hessian_real i j)) 6) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`input_lower:num`; `input_upper:num`;
       `root_lower:num`; `root_upper:num`;
       `input_real:real`; `root_real:real`]
      candle_fs_hist_sqrt_scalars_contains) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_sqrt_hessian_chain_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_sqrt_chain_formula = prove
 (`!x gradient_i gradient_j hessian_ij.
     &0 < x
     ==> inv (&2 * sqrt x) *
           (gradient_j * ((--inv (&2 * x)) * gradient_i) + hessian_ij) =
         (--inv ((sqrt x + sqrt x) * (x + x))) *
           (gradient_i * gradient_j) +
         inv (sqrt x + sqrt x) * hessian_ij`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt x` ASSUME_TAC THENL
   [MP_TAC (SPEC `x:real` SQRT_LT_0) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(sqrt x = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INV_MUL; REAL_ARITH `y + y = &2 * y`] THEN
  CONV_TAC REAL_RING);;

let candle_cv_fs_hist_sqrt_hessian_entry_correct = prove
 (`!rowindex colindex derivative_value logarithmic_derivative
      input_gradient input_hessian.
     rowindex < LENGTH input_hessian
     ==>
     candle_cv_fs_hist_sqrt_hessian_entry
       (Cexp_num rowindex) (Cexp_num colindex)
       (candle_cv_fs_interval derivative_value)
       (candle_cv_fs_interval logarithmic_derivative)
       (candle_cv_fs_interval_list input_gradient)
       (candle_cv_fs_interval_matrix input_hessian) =
     candle_cv_fs_interval
       (candle_fs_hist_sqrt_hessian_entry rowindex colindex
         derivative_value logarithmic_derivative input_gradient
         input_hessian)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_sqrt_hessian_entry_def;
              candle_fs_hist_sqrt_hessian_entry_def;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_angle_interval_mul_correct;
              candle_cv_fs_interval_add_correct;
              LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `candle_cv_fs_angle_matrix_lookup
      (Cexp_num rowindex) (Cexp_num colindex)
      (candle_cv_fs_interval_matrix input_hessian) =
    candle_cv_fs_interval
      (candle_fs_angle_matrix_lookup
        rowindex colindex input_hessian)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC candle_cv_fs_angle_matrix_lookup_correct THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_cv_fs_angle_interval_mul_correct;
                candle_cv_fs_interval_add_correct]]);;

let candle_cv_fs_hist_sqrt_hessian_symmetric_entry_correct = prove
 (`!rowindex colindex derivative_value logarithmic_derivative
      input_gradient input_hessian.
     rowindex < LENGTH input_hessian /\
     colindex < LENGTH input_hessian
     ==>
     candle_cv_fs_hist_sqrt_hessian_symmetric_entry
       (Cexp_num rowindex) (Cexp_num colindex)
       (candle_cv_fs_interval derivative_value)
       (candle_cv_fs_interval logarithmic_derivative)
       (candle_cv_fs_interval_list input_gradient)
       (candle_cv_fs_interval_matrix input_hessian) =
     candle_cv_fs_interval
       (candle_fs_hist_sqrt_hessian_symmetric_entry rowindex colindex
         derivative_value logarithmic_derivative input_gradient
         input_hessian)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_sqrt_hessian_symmetric_entry_def;
              candle_fs_hist_sqrt_hessian_symmetric_entry_def;
              cexp_less_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def] THEN
  MATCH_MP_TAC candle_cv_fs_hist_sqrt_hessian_entry_correct THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_fs_hist_sqrt_hessian_row_correct = prove
 (`!rowindex derivative_value logarithmic_derivative
      input_gradient input_hessian.
     LENGTH input_hessian = 6 /\ rowindex < 6
     ==>
     candle_cv_fs_hist_sqrt_hessian_row
       (Cexp_num rowindex)
       (candle_cv_fs_interval derivative_value)
       (candle_cv_fs_interval logarithmic_derivative)
       (candle_cv_fs_interval_list input_gradient)
       (candle_cv_fs_interval_matrix input_hessian) =
     candle_cv_fs_interval_list
       (candle_fs_hist_sqrt_hessian_row rowindex derivative_value
         logarithmic_derivative input_gradient input_hessian)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL [`rowindex:num`; `0`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_symmetric_entry_correct) THEN
  MP_TAC
    (SPECL [`rowindex:num`; `1`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_symmetric_entry_correct) THEN
  MP_TAC
    (SPECL [`rowindex:num`; `2`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_symmetric_entry_correct) THEN
  MP_TAC
    (SPECL [`rowindex:num`; `3`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_symmetric_entry_correct) THEN
  MP_TAC
    (SPECL [`rowindex:num`; `4`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_symmetric_entry_correct) THEN
  MP_TAC
    (SPECL [`rowindex:num`; `5`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_symmetric_entry_correct) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_hist_sqrt_hessian_row_def;
                  candle_fs_hist_sqrt_hessian_row_def;
                  candle_cv_fs_angle_six_correct]);;

let candle_cv_fs_hist_sqrt_hessian_correct = prove
 (`!derivative_value logarithmic_derivative input_gradient input_hessian.
     LENGTH input_hessian = 6
     ==>
     candle_cv_fs_hist_sqrt_hessian
       (candle_cv_fs_interval derivative_value)
       (candle_cv_fs_interval logarithmic_derivative)
       (candle_cv_fs_interval_list input_gradient)
       (candle_cv_fs_interval_matrix input_hessian) =
     candle_cv_fs_interval_matrix
       (candle_fs_hist_sqrt_hessian derivative_value
         logarithmic_derivative input_gradient input_hessian)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL [`0`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_row_correct) THEN
  MP_TAC
    (SPECL [`1`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_row_correct) THEN
  MP_TAC
    (SPECL [`2`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_row_correct) THEN
  MP_TAC
    (SPECL [`3`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_row_correct) THEN
  MP_TAC
    (SPECL [`4`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_row_correct) THEN
  MP_TAC
    (SPECL [`5`; `derivative_value:(num#num)#(num#num)`;
            `logarithmic_derivative:(num#num)#(num#num)`;
            `input_gradient:((num#num)#(num#num))list`;
            `input_hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_hist_sqrt_hessian_row_correct) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_hist_sqrt_hessian_def;
                  candle_fs_hist_sqrt_hessian_def;
                  candle_cv_fs_angle_matrix_six_correct]);;

(* Package the supplied-root square-root operation at the same jet boundary
   used by the generic nonlinear checker.  This is deliberately the whole
   value/gradient/Hessian operation: proving more isolated scalar identities
   would not yet authorize the low-work historical instruction. *)

let candle_fs_hist_second_make_def = new_definition
 `candle_fs_hist_second_make value gradient hessian =
    (value,(gradient,hessian))`;;

let candle_fs_hist_second_value_def = new_definition
 `candle_fs_hist_second_value second = FST second`;;

let candle_fs_hist_second_gradient_def = new_definition
 `candle_fs_hist_second_gradient second = FST (SND second)`;;

let candle_fs_hist_second_hessian_def = new_definition
 `candle_fs_hist_second_hessian second = SND (SND second)`;;

let candle_cv_fs_hist_second_def = new_definition
 `candle_cv_fs_hist_second second =
    Cexp_pair
      (candle_cv_fs_interval (candle_fs_hist_second_value second))
      (Cexp_pair
        (candle_cv_fs_interval_list
          (candle_fs_hist_second_gradient second))
        (candle_cv_fs_interval_matrix
          (candle_fs_hist_second_hessian second)))`;;

let candle_fs_hist_second_sqrt_supplied_def = new_definition
 `candle_fs_hist_second_sqrt_supplied input root_value =
    let input_value = candle_fs_hist_second_value input in
    let input_gradient = candle_fs_hist_second_gradient input in
    let input_hessian = candle_fs_hist_second_hessian input in
    let derivative_value = candle_fs_hist_inv_twice_positive root_value in
    let logarithmic_derivative = candle_fs_interval_neg
      (candle_fs_hist_inv_twice_positive input_value) in
    candle_fs_hist_second_make root_value
      (candle_fsn_interval_list_scale derivative_value input_gradient)
      (candle_fs_hist_sqrt_hessian derivative_value logarithmic_derivative
        input_gradient input_hessian)`;;

let candle_cv_fs_hist_second_sqrt_supplied_correct = prove
 (`!input_value input_gradient input_hessian root_value.
     LENGTH input_hessian = 6
     ==>
     candle_cv_fs_hist_second_sqrt_supplied
       (candle_cv_fs_hist_second
         (candle_fs_hist_second_make input_value input_gradient
           input_hessian))
       (candle_cv_fs_interval root_value) =
     candle_cv_fs_hist_second
       (candle_fs_hist_second_sqrt_supplied
         (candle_fs_hist_second_make input_value input_gradient
           input_hessian)
         root_value)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_second_sqrt_supplied_def;
              candle_fs_hist_second_sqrt_supplied_def;
              candle_cv_fs_hist_second_def;
              candle_cv_fs_hist_second_make_def;
              candle_cv_fs_hist_second_value_def;
              candle_cv_fs_hist_second_gradient_def;
              candle_cv_fs_hist_second_hessian_def;
              candle_fs_hist_second_make_def;
              candle_fs_hist_second_value_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_hessian_def;
              candle_cv_fs_hist_inv_twice_positive_correct;
              candle_cv_fs_interval_neg_correct;
              candle_cv_fsn_interval_list_scale_correct;
              cexp_fst_def; cexp_snd_def; LET_DEF; LET_END_DEF] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC candle_cv_fs_hist_sqrt_hessian_correct THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_sqrt_hessian_shape = prove
 (`!derivative_value logarithmic_derivative input_gradient input_hessian.
     LENGTH
       (candle_fs_hist_sqrt_hessian derivative_value
         logarithmic_derivative input_gradient input_hessian) = 6 /\
     ALL (\row. LENGTH row = 6)
       (candle_fs_hist_sqrt_hessian derivative_value
         logarithmic_derivative input_gradient input_hessian)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_def;
              candle_fs_hist_sqrt_hessian_row_def; LENGTH; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_positive_sqrt_hessian_universal_contains = prove
 (`!input_lower input_upper root_lower root_upper input_real
      input_gradient input_hessian
      (gradient_real:num->real) (hessian_real:num->num->real).
     0 < input_lower /\ input_lower <= input_upper /\
     0 < root_lower /\ root_lower <= root_upper /\
     &0 < input_real /\
     candle_fs_interval_contains
       ((input_lower,0),(input_upper,0)) input_real /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0)) (sqrt input_real) /\
     LENGTH input_gradient = 6 /\
     LENGTH input_hessian = 6 /\
     ALL (\matrix_row. LENGTH matrix_row = 6) input_hessian /\
     ALL2 candle_fs_interval_contains input_gradient
       (list_of_seq gradient_real 6) /\
     ALL2 (ALL2 candle_fs_interval_contains) input_hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) 6) 6) /\
     (!i j. hessian_real i j = hessian_real j i)
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_sqrt_hessian
         (candle_fs_hist_inv_twice_positive
           ((root_lower,0),(root_upper,0)))
         (candle_fs_interval_neg
           (candle_fs_hist_inv_twice_positive
             ((input_lower,0),(input_upper,0))))
         input_gradient input_hessian)
       (list_of_seq
         (\i. list_of_seq
           (\j.
              (--inv
                ((sqrt input_real + sqrt input_real) *
                 (input_real + input_real))) *
                (gradient_real i * gradient_real j) +
              inv (sqrt input_real + sqrt input_real) *
                hessian_real i j) 6) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`input_lower:num`; `input_upper:num`;
       `root_lower:num`; `root_upper:num`;
       `input_real:real`; `sqrt input_real`]
      candle_fs_hist_sqrt_scalars_contains) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_list_of_seq;
              candle_all2_list_of_seq] THEN
  X_GEN_TAC `rowindex:num` THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fs_hist_sqrt_hessian_row_list_of_seq;
              candle_all2_list_of_seq] THEN
  X_GEN_TAC `colindex:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(--inv
      ((sqrt input_real + sqrt input_real) *
       (input_real + input_real))) *
      (gradient_real rowindex * gradient_real colindex) +
    inv (sqrt input_real + sqrt input_real) *
      hessian_real rowindex colindex =
    candle_fs_hist_sqrt_hessian_component rowindex colindex
      (inv (&2 * sqrt input_real)) (--inv (&2 * input_real))
      gradient_real hessian_real`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_sqrt_chain_formula;
                  candle_fs_hist_sqrt_hessian_component_symmetric];
    MATCH_MP_TAC
      (SPEC `6` candle_fs_hist_sqrt_hessian_symmetric_entry_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_second_to_q_def = new_definition
 `candle_fs_hist_second_to_q second =
    candle_fs_first_to_q
      (candle_fs_first_make
        (candle_fs_hist_second_value second)
        (candle_fs_hist_second_gradient second))
      (candle_fs_hist_second_hessian second)`;;

let candle_fs_hist_second_sqrt_supplied_components = prove
 (`!input_lower input_upper root_lower root_upper input_real
      input_gradient input_hessian
      (gradient_real:num->real) (hessian_real:num->num->real).
     0 < input_lower /\ input_lower <= input_upper /\
     0 < root_lower /\ root_lower <= root_upper /\
     &0 < input_real /\
     candle_fs_interval_contains
       ((input_lower,0),(input_upper,0)) input_real /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0)) (sqrt input_real) /\
     LENGTH input_gradient = 6 /\
     LENGTH input_hessian = 6 /\
     ALL (\matrix_row. LENGTH matrix_row = 6) input_hessian /\
     ALL2 candle_fs_interval_contains input_gradient
       (list_of_seq gradient_real 6) /\
     ALL2 (ALL2 candle_fs_interval_contains) input_hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) 6) 6) /\
     (!i j. hessian_real i j = hessian_real j i)
     ==>
     candle_q_dim_jet_contains_components 6
       (candle_fs_hist_second_to_q
         (candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_second_make
             ((input_lower,0),(input_upper,0))
             input_gradient input_hessian)
           ((root_lower,0),(root_upper,0))))
       (sqrt input_real)
       (\i. inv (sqrt input_real + sqrt input_real) * gradient_real i)
       (\i j.
          (--inv
            ((sqrt input_real + sqrt input_real) *
             (input_real + input_real))) *
            (gradient_real i * gradient_real j) +
          inv (sqrt input_real + sqrt input_real) * hessian_real i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_second_to_q_def] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REWRITE_TAC[candle_fs_first_to_q_shape] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_fs_hist_second_sqrt_supplied_def;
                    candle_fs_hist_second_make_def;
                    candle_fs_hist_second_value_def;
                    candle_fs_hist_second_gradient_def;
                    candle_fs_hist_second_hessian_def;
                    candle_fs_first_make_def;
                    candle_fs_first_gradient_def;
                    candle_fsn_interval_list_scale_length;
                    LET_DEF; LET_END_DEF];
    REWRITE_TAC[candle_fs_hist_second_sqrt_supplied_def;
                candle_fs_hist_second_make_def;
                candle_fs_hist_second_value_def;
                candle_fs_hist_second_gradient_def;
                candle_fs_hist_second_hessian_def;
                candle_fs_first_make_def;
                candle_fs_first_gradient_def;
                LET_DEF; LET_END_DEF] THEN
    MESON_TAC[candle_fs_hist_sqrt_hessian_shape];
    REWRITE_TAC[candle_fs_hist_second_sqrt_supplied_def;
                candle_fs_hist_second_make_def;
                candle_fs_hist_second_value_def;
                candle_fs_hist_second_gradient_def;
                candle_fs_hist_second_hessian_def;
                candle_fs_first_make_def;
                candle_fs_first_gradient_def;
                LET_DEF; LET_END_DEF] THEN
    MESON_TAC[candle_fs_hist_sqrt_hessian_shape];
    ASM_REWRITE_TAC[candle_fs_hist_second_sqrt_supplied_def;
                    candle_fs_hist_second_make_def;
                    candle_fs_hist_second_value_def;
                    candle_fs_hist_second_gradient_def;
                    candle_fs_hist_second_hessian_def;
                    candle_fs_first_make_def;
                    candle_fs_first_value_def;
                    LET_DEF; LET_END_DEF];
    REWRITE_TAC[candle_fs_hist_second_sqrt_supplied_def;
                candle_fs_hist_second_make_def;
                candle_fs_hist_second_value_def;
                candle_fs_hist_second_gradient_def;
                candle_fs_hist_second_hessian_def;
                candle_fs_first_make_def;
                candle_fs_first_gradient_def;
                LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[GSYM candle_map_scale_list_of_seq] THEN
    REWRITE_TAC[GSYM candle_fs_hist_positive_sqrt_gradient_def] THEN
    MATCH_MP_TAC candle_fs_hist_positive_sqrt_gradient_universal_contains THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_hist_second_sqrt_supplied_def;
                candle_fs_hist_second_make_def;
                candle_fs_hist_second_value_def;
                candle_fs_hist_second_gradient_def;
                candle_fs_hist_second_hessian_def;
                LET_DEF; LET_END_DEF] THEN
    MATCH_MP_TAC
      candle_fs_hist_positive_sqrt_hessian_universal_contains THEN
    ASM_REWRITE_TAC[]]);;

end;;
