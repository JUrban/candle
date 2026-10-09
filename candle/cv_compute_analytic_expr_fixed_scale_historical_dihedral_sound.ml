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

end;;
