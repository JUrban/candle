(* ========================================================================== *)
(* Soundness substrate for reflected signed fixed-scale arithmetic.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The executable backend is useful only after   *)
(* these representation and real-semantics results are lifted through        *)
(* intervals, jets, and the polynomial interpreter.  This file begins that   *)
(* reusable proof; no theorem here is tied to a particular Flyspeck formula.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;

module Candle_cv_analytic_expr_fixed_scale_sound = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_sound;;
open Candle_cv_analytic_expr_fixed_scale_compute;;

(* -------------------------------------------------------------------------- *)
(* Ordinary HOL representation.                                               *)
(* -------------------------------------------------------------------------- *)

let candle_fs_scale_def = new_definition
 `candle_fs_scale = 1000000000000`;;

let candle_fs_real_def = new_definition
 `candle_fs_real (z:num#num) = candle_lc_zreal z / &candle_fs_scale`;;

let candle_fs_raw_neg_def = new_definition
 `candle_fs_raw_neg (z:num#num) = (SND z,FST z)`;;

let candle_fs_canonical_def = new_definition
 `candle_fs_canonical (z:num#num) =
    if FST z < SND z then (0,SND z - FST z)
    else (FST z - SND z,0)`;;

let candle_fs_add_def = new_definition
 `candle_fs_add (x:num#num) y =
    candle_fs_canonical (candle_lc_zadd x y)`;;

let candle_fs_floor_div_def = new_definition
 `candle_fs_floor_div (z:num#num) denominator =
    if FST z < SND z then
      (0,candle_q_ceil_div (SND z - FST z) denominator)
    else ((FST z - SND z) DIV denominator,0)`;;

let candle_fs_ceil_div_def = new_definition
 `candle_fs_ceil_div (z:num#num) denominator =
    if FST z < SND z then
      (0,(SND z - FST z) DIV denominator)
    else (candle_q_ceil_div (FST z - SND z) denominator,0)`;;

let candle_fs_to_q_def = new_definition
 `candle_fs_to_q (z:num#num) = (z,candle_fs_scale - 1)`;;

(* -------------------------------------------------------------------------- *)
(* Computed-value representation theorems.                                    *)
(* -------------------------------------------------------------------------- *)

let candle_cv_fs_scale_correct = prove
 (`candle_cv_fs_scale = Cexp_num candle_fs_scale`,
  REWRITE_TAC[candle_cv_fs_scale_def; candle_fs_scale_def]);;

let candle_cv_fs_zero_correct = prove
 (`candle_cv_fs_zero = candle_cv_lc_z (0,0)`,
  REWRITE_TAC[candle_cv_fs_zero_def; candle_cv_lc_z_def; FST; SND]);;

let candle_cv_fs_one_correct = prove
 (`candle_cv_fs_one = candle_cv_lc_z (candle_fs_scale,0)`,
  REWRITE_TAC[candle_cv_fs_one_def; candle_cv_fs_scale_correct;
              candle_cv_lc_z_def; FST; SND]);;

let candle_cv_fs_raw_add_correct = prove
 (`!x y.
     candle_cv_fs_raw_add (candle_cv_lc_z x) (candle_cv_lc_z y) =
     candle_cv_lc_z (candle_lc_zadd x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_add_def; candle_cv_lc_z_def;
              candle_lc_zadd_def; cexp_fst_def; cexp_snd_def;
              cexp_add_def; FST; SND]);;

let candle_cv_fs_raw_neg_correct = prove
 (`!z.
     candle_cv_fs_raw_neg (candle_cv_lc_z z) =
     candle_cv_lc_z (candle_fs_raw_neg z)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_neg_def; candle_cv_lc_z_def;
              candle_fs_raw_neg_def; cexp_fst_def; cexp_snd_def;
              FST; SND]);;

let candle_cv_fs_raw_mul_correct = prove
 (`!x y.
     candle_cv_fs_raw_mul (candle_cv_lc_z x) (candle_cv_lc_z y) =
     candle_cv_lc_z (candle_q_zmul x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_mul_def; candle_cv_lc_z_def;
              candle_q_zmul_def; cexp_fst_def; cexp_snd_def;
              cexp_add_def; cexp_mul_def; FST; SND]);;

let candle_cv_fs_raw_scale_correct = prove
 (`!factor z.
     candle_cv_fs_raw_scale (Cexp_num factor) (candle_cv_lc_z z) =
     candle_cv_lc_z (candle_lc_zscale factor z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_scale_def; candle_cv_lc_z_def;
              candle_lc_zscale_def; cexp_fst_def; cexp_snd_def;
              cexp_mul_def; FST; SND]);;

let candle_cv_fs_canonical_correct = prove
 (`!z.
     candle_cv_fs_canonical (candle_cv_lc_z z) =
     candle_cv_lc_z (candle_fs_canonical z)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_canonical_def; candle_fs_canonical_def;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              cexp_less_def; FST; SND] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_sub_def]);;

let candle_cv_fs_add_correct = prove
 (`!x y.
     candle_cv_fs_add (candle_cv_lc_z x) (candle_cv_lc_z y) =
     candle_cv_lc_z (candle_fs_add x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_add_def; candle_fs_add_def;
              candle_cv_fs_raw_add_correct;
              candle_cv_fs_canonical_correct]);;

let candle_cv_fs_neg_correct = prove
 (`!z.
     candle_cv_fs_neg (candle_cv_lc_z z) =
     candle_cv_lc_z (candle_fs_raw_neg z)`,
  REWRITE_TAC[candle_cv_fs_neg_def; candle_cv_fs_raw_neg_correct]);;

let candle_cv_fs_floor_div_correct = prove
 (`!z denominator.
     candle_cv_fs_floor_div
       (candle_cv_lc_z z) (Cexp_num denominator) =
     candle_cv_lc_z (candle_fs_floor_div z denominator)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_floor_div_def; candle_fs_floor_div_def;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              cexp_less_def; FST; SND] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_sub_def; cexp_div_def;
                  candle_cv_q_ceil_div_correct]);;

let candle_cv_fs_ceil_div_correct = prove
 (`!z denominator.
     candle_cv_fs_ceil_div
       (candle_cv_lc_z z) (Cexp_num denominator) =
     candle_cv_lc_z (candle_fs_ceil_div z denominator)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_ceil_div_def; candle_fs_ceil_div_def;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              cexp_less_def; FST; SND] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_sub_def; cexp_div_def;
                  candle_cv_q_ceil_div_correct]);;

let candle_cv_fs_to_q_correct = prove
 (`!z.
     candle_cv_fs_to_q (candle_cv_lc_z z) =
     candle_cv_q (candle_fs_to_q z)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_to_q_def; candle_fs_to_q_def;
              candle_cv_q_def; candle_cv_fs_scale_correct;
              candle_cv_lc_z_def; candle_fs_scale_def;
              cexp_sub_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* -------------------------------------------------------------------------- *)
(* Real denotation.                                                           *)
(* -------------------------------------------------------------------------- *)

let candle_fs_scale_pos = prove
 (`0 < candle_fs_scale`,
  REWRITE_TAC[candle_fs_scale_def] THEN ARITH_TAC);;

let candle_fs_raw_neg_real = prove
 (`!z. candle_lc_zreal (candle_fs_raw_neg z) = --(candle_lc_zreal z)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_neg_def; candle_lc_zreal_def; FST; SND] THEN
  REAL_ARITH_TAC);;

let candle_fs_canonical_real = prove
 (`!z. candle_lc_zreal (candle_fs_canonical z) = candle_lc_zreal z`,
  REWRITE_TAC[FORALL_PAIR_THM; candle_fs_canonical_def;
              candle_lc_zreal_def; FST; SND] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LZERO] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_OF_NUM_SUB_CASES] THEN
    ASM_REWRITE_TAC[GSYM NOT_LT];
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_OF_NUM_SUB_CASES] THEN
    ASM_REWRITE_TAC[GSYM NOT_LT]]);;

let candle_fs_add_real = prove
 (`!x y. candle_fs_real (candle_fs_add x y) =
         candle_fs_real x + candle_fs_real y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_real_def; candle_fs_add_def;
              candle_fs_canonical_real; candle_lc_zreal_add;
              real_div; REAL_ADD_RDISTRIB]);;

let candle_fs_raw_neg_real_scaled = prove
 (`!z. candle_fs_real (candle_fs_raw_neg z) = --(candle_fs_real z)`,
  REWRITE_TAC[candle_fs_real_def; candle_fs_raw_neg_real;
              real_div; GSYM REAL_NEG_LMUL]);;

let candle_fs_to_q_real = prove
 (`!z. candle_q_real (candle_fs_to_q z) = candle_fs_real z`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_real_def; candle_q_den_def;
              candle_fs_to_q_def; candle_fs_real_def; FST; SND] THEN
  SUBGOAL_THEN `SUC (candle_fs_scale - 1) = candle_fs_scale`
    SUBST1_TAC THENL
   [MP_TAC candle_fs_scale_pos THEN ARITH_TAC;
    REFL_TAC]);;

(* Directed division is the only lossy scalar boundary in the polynomial     *)
(* backend.  These lemmas are independent of the chosen Taylor scale.        *)

let candle_nat_floor_div_le = prove
 (`!numerator denominator. ~(denominator = 0)
     ==> &((numerator DIV denominator):num) <=
         &numerator / &denominator`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < denominator` ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT] THEN
  MATCH_MP_TAC (REAL_ARITH `y * x <= z ==> x * y <= z`) THEN
  MP_TAC (SPECL [`numerator:num`; `denominator:num`] DIV_MUL_LE) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL]);;

let candle_nat_le_ceil_div = prove
 (`!numerator denominator. ~(denominator = 0)
     ==> &numerator / &denominator <=
         &(candle_q_ceil_div numerator denominator)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < denominator` ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT] THEN
  MP_TAC
    (SPECL [`denominator:num`; `numerator:num`]
      candle_q_ceil_div_step) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL]);;

let candle_fs_floor_div_sound = prove
 (`!z denominator. ~(denominator = 0)
     ==> candle_lc_zreal (candle_fs_floor_div z denominator) <=
         candle_lc_zreal z / &denominator`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fs_floor_div_def; candle_lc_zreal_def; FST; SND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND] THENL
   [SUBGOAL_THEN `&(p2 - p1) = &p2 - &p1` ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_OF_NUM_SUB; LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC (SPECL [`(p2 - p1):num`; `denominator:num`]
      candle_nat_le_ceil_div) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&(p1 - p2) = &p1 - &p2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT];
      ALL_TAC] THEN
    MP_TAC (SPECL [`(p1 - p2):num`; `denominator:num`]
      candle_nat_floor_div_le) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC]);;

let candle_fs_ceil_div_sound = prove
 (`!z denominator. ~(denominator = 0)
     ==> candle_lc_zreal z / &denominator <=
         candle_lc_zreal (candle_fs_ceil_div z denominator)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fs_ceil_div_def; candle_lc_zreal_def; FST; SND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND] THENL
   [SUBGOAL_THEN `&(p2 - p1) = &p2 - &p1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB; LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC (SPECL [`(p2 - p1):num`; `denominator:num`]
      candle_nat_floor_div_le) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&(p1 - p2) = &p1 - &p2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT];
      ALL_TAC] THEN
    MP_TAC (SPECL [`(p1 - p2):num`; `denominator:num`]
      candle_nat_le_ceil_div) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC]);;

end;;
