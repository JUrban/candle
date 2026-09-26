(* ========================================================================== *)
(* Soundness substrate for reflected signed fixed-scale arithmetic.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The executable backend is useful only after   *)
(* these representation and real-semantics results are lifted through        *)
(* intervals, jets, and the polynomial interpreter.  This file begins that   *)
(* reusable proof; no theorem here is tied to a particular Flyspeck formula.  *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_mul_core.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;

module Candle_cv_analytic_expr_fixed_scale_sound = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_mul_core;;
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

let candle_fs_raw_real_def = new_definition
 `candle_fs_raw_real denominator (z:num#num) =
    candle_lc_zreal z / &denominator`;;

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

let candle_fs_raw_le_def = new_definition
 `candle_fs_raw_le (x:num#num) y <=>
    FST x + SND y <= FST y + SND x`;;

let candle_fs_raw_min_def = new_definition
 `candle_fs_raw_min (x:num#num) y =
    if candle_fs_raw_le x y then x else y`;;

let candle_fs_raw_max_def = new_definition
 `candle_fs_raw_max (x:num#num) y =
    if candle_fs_raw_le x y then y else x`;;

let candle_fs_raw_abs_def = new_definition
 `candle_fs_raw_abs (z:num#num) =
    candle_fs_raw_max z (candle_fs_raw_neg z)`;;

let candle_fs_of_q_lower_def = new_definition
 `candle_fs_of_q_lower (q:(num#num)#num) =
    FST (candle_q_fixed_round_lower q)`;;

let candle_fs_of_q_upper_def = new_definition
 `candle_fs_of_q_upper (q:(num#num)#num) =
    FST (candle_q_fixed_round_upper q)`;;

let candle_cv_fs_interval_def = new_definition
 `candle_cv_fs_interval (i:(num#num)#(num#num)) =
    Cexp_pair (candle_cv_lc_z (FST i)) (candle_cv_lc_z (SND i))`;;

let candle_fs_interval_zero_def = new_definition
 `candle_fs_interval_zero = ((0,0),(0,0))`;;

let candle_fs_interval_one_def = new_definition
 `candle_fs_interval_one =
    ((candle_fs_scale,0),(candle_fs_scale,0))`;;

let candle_fs_interval_of_q_def = new_definition
 `candle_fs_interval_of_q
    (i:((num#num)#num)#((num#num)#num)) =
    (candle_fs_of_q_lower (FST i),
     candle_fs_of_q_upper (SND i))`;;

let candle_fs_interval_constant_def = new_definition
 `candle_fs_interval_constant (q:(num#num)#num) =
    (candle_fs_of_q_lower q,candle_fs_of_q_upper q)`;;

let candle_fs_interval_neg_def = new_definition
 `candle_fs_interval_neg (i:(num#num)#(num#num)) =
    (candle_fs_raw_neg (SND i),candle_fs_raw_neg (FST i))`;;

let candle_fs_interval_add_def = new_definition
 `candle_fs_interval_add (x:(num#num)#(num#num)) y =
    (candle_fs_add (FST x) (FST y),
     candle_fs_add (SND x) (SND y))`;;

let candle_fs_raw_interval_neg_def = new_definition
 `candle_fs_raw_interval_neg (i:(num#num)#(num#num)) =
    (candle_fs_raw_neg (SND i),candle_fs_raw_neg (FST i))`;;

let candle_fs_raw_interval_add_def = new_definition
 `candle_fs_raw_interval_add (x:(num#num)#(num#num)) y =
    (candle_lc_zadd (FST x) (FST y),
     candle_lc_zadd (SND x) (SND y))`;;

let candle_fs_raw_interval_mul_def = new_definition
 `candle_fs_raw_interval_mul (x:(num#num)#(num#num)) y =
    (candle_fs_raw_min
      (candle_fs_raw_min
        (candle_q_zmul (FST x) (FST y))
        (candle_q_zmul (FST x) (SND y)))
      (candle_fs_raw_min
        (candle_q_zmul (SND x) (FST y))
        (candle_q_zmul (SND x) (SND y))),
     candle_fs_raw_max
      (candle_fs_raw_max
        (candle_q_zmul (FST x) (FST y))
        (candle_q_zmul (FST x) (SND y)))
      (candle_fs_raw_max
        (candle_q_zmul (SND x) (FST y))
        (candle_q_zmul (SND x) (SND y))))`;;

let candle_fs_raw_interval_round_def = new_definition
 `candle_fs_raw_interval_round denominator
    (i:(num#num)#(num#num)) =
    (candle_fs_floor_div (FST i) denominator,
     candle_fs_ceil_div (SND i) denominator)`;;

let candle_fs_interval_abs_upper_def = new_definition
 `candle_fs_interval_abs_upper (i:(num#num)#(num#num)) =
    candle_fs_raw_max
      (candle_fs_raw_abs (FST i))
      (candle_fs_raw_abs (SND i))`;;

let candle_fs_interval_contains_def = new_definition
 `candle_fs_interval_contains (i:(num#num)#(num#num)) (x:real) <=>
    candle_fs_real (FST i) <= x /\ x <= candle_fs_real (SND i)`;;

let candle_fs_raw_interval_contains_def = new_definition
 `candle_fs_raw_interval_contains denominator
    (i:(num#num)#(num#num)) (x:real) <=>
    candle_fs_raw_real denominator (FST i) <= x /\
    x <= candle_fs_raw_real denominator (SND i)`;;

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

let candle_cv_fs_raw_le_correct = prove
 (`!x y.
     candle_cv_fs_raw_le (candle_cv_lc_z x) (candle_cv_lc_z y) =
     Cexp_num (if candle_fs_raw_le x y then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_le_def; candle_fs_raw_le_def;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              cexp_add_def; cexp_less_def; FST; SND;
              GSYM ADD1; LT_SUC_LE]);;

let candle_cv_fs_raw_min_correct = prove
 (`!x y.
     candle_cv_fs_raw_min (candle_cv_lc_z x) (candle_cv_lc_z y) =
     candle_cv_lc_z (candle_fs_raw_min x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_min_def; candle_fs_raw_min_def;
              candle_cv_fs_raw_le_correct] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]);;

let candle_cv_fs_raw_max_correct = prove
 (`!x y.
     candle_cv_fs_raw_max (candle_cv_lc_z x) (candle_cv_lc_z y) =
     candle_cv_lc_z (candle_fs_raw_max x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_max_def; candle_fs_raw_max_def;
              candle_cv_fs_raw_le_correct] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]);;

let candle_cv_fs_raw_abs_correct = prove
 (`!z.
     candle_cv_fs_raw_abs (candle_cv_lc_z z) =
     candle_cv_lc_z (candle_fs_raw_abs z)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_abs_def; candle_fs_raw_abs_def;
              candle_cv_fs_raw_neg_correct;
              candle_cv_fs_raw_max_correct]);;

let candle_cv_fs_of_q_lower_correct = prove
 (`!q.
     candle_cv_fs_of_q_lower (candle_cv_q q) =
     candle_cv_lc_z (candle_fs_of_q_lower q)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_of_q_lower_def; candle_fs_of_q_lower_def;
              candle_cv_q_fixed_round_lower_correct;
              candle_cv_q_def; cexp_fst_def]);;

let candle_cv_fs_of_q_upper_correct = prove
 (`!q.
     candle_cv_fs_of_q_upper (candle_cv_q q) =
     candle_cv_lc_z (candle_fs_of_q_upper q)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_of_q_upper_def; candle_fs_of_q_upper_def;
              candle_cv_q_fixed_round_upper_correct;
              candle_cv_q_def; cexp_fst_def]);;

let candle_cv_fs_interval_zero_correct = prove
 (`candle_cv_fs_interval_zero =
   candle_cv_fs_interval candle_fs_interval_zero`,
  REWRITE_TAC[candle_cv_fs_interval_zero_def;
              candle_fs_interval_zero_def; candle_cv_fs_interval_def;
              candle_cv_fs_zero_correct; FST; SND]);;

let candle_cv_fs_interval_one_correct = prove
 (`candle_cv_fs_interval_one =
   candle_cv_fs_interval candle_fs_interval_one`,
  REWRITE_TAC[candle_cv_fs_interval_one_def;
              candle_fs_interval_one_def; candle_cv_fs_interval_def;
              candle_cv_fs_one_correct; FST; SND]);;

let candle_cv_fs_interval_of_q_correct = prove
 (`!i.
     candle_cv_fs_interval_of_q (candle_cv_q_interval i) =
     candle_cv_fs_interval (candle_fs_interval_of_q i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_interval_of_q_def;
              candle_fs_interval_of_q_def;
              candle_cv_q_interval_def; candle_cv_fs_interval_def;
              cexp_fst_def; cexp_snd_def;
              candle_cv_fs_of_q_lower_correct;
              candle_cv_fs_of_q_upper_correct; FST; SND]);;

let candle_cv_fs_interval_constant_correct = prove
 (`!q.
     candle_cv_fs_interval_constant (candle_cv_q q) =
     candle_cv_fs_interval (candle_fs_interval_constant q)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_interval_constant_def;
              candle_fs_interval_constant_def;
              candle_cv_fs_interval_def;
              candle_cv_fs_of_q_lower_correct;
              candle_cv_fs_of_q_upper_correct; FST; SND]);;

let candle_cv_fs_interval_neg_correct = prove
 (`!i.
     candle_cv_fs_interval_neg (candle_cv_fs_interval i) =
     candle_cv_fs_interval (candle_fs_interval_neg i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_interval_neg_def;
              candle_fs_interval_neg_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_neg_correct; FST; SND]);;

let candle_cv_fs_interval_add_correct = prove
 (`!x y.
     candle_cv_fs_interval_add
       (candle_cv_fs_interval x) (candle_cv_fs_interval y) =
     candle_cv_fs_interval (candle_fs_interval_add x y)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_interval_add_def;
              candle_fs_interval_add_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_add_correct; FST; SND]);;

let candle_cv_fs_raw_interval_neg_correct = prove
 (`!i.
     candle_cv_fs_raw_interval_neg (candle_cv_fs_interval i) =
     candle_cv_fs_interval (candle_fs_raw_interval_neg i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_neg_def;
              candle_fs_raw_interval_neg_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_raw_neg_correct; FST; SND]);;

let candle_cv_fs_raw_interval_add_correct = prove
 (`!x y.
     candle_cv_fs_raw_interval_add
       (candle_cv_fs_interval x) (candle_cv_fs_interval y) =
     candle_cv_fs_interval (candle_fs_raw_interval_add x y)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_add_def;
              candle_fs_raw_interval_add_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_raw_add_correct; FST; SND]);;

let candle_cv_fs_raw_interval_mul_correct = prove
 (`!x y.
     candle_cv_fs_raw_interval_mul
       (candle_cv_fs_interval x) (candle_cv_fs_interval y) =
     candle_cv_fs_interval (candle_fs_raw_interval_mul x y)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_mul_def;
              candle_fs_raw_interval_mul_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_raw_mul_correct;
              candle_cv_fs_raw_min_correct;
              candle_cv_fs_raw_max_correct; FST; SND]);;

let candle_cv_fs_raw_interval_round_correct = prove
 (`!denominator i.
     candle_cv_fs_raw_interval_round
       (Cexp_num denominator) (candle_cv_fs_interval i) =
     candle_cv_fs_interval (candle_fs_raw_interval_round denominator i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_round_def;
              candle_fs_raw_interval_round_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_floor_div_correct;
              candle_cv_fs_ceil_div_correct; FST; SND]);;

let candle_cv_fs_interval_abs_upper_correct = prove
 (`!i.
     candle_cv_fs_interval_abs_upper (candle_cv_fs_interval i) =
     candle_cv_lc_z (candle_fs_interval_abs_upper i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_interval_abs_upper_def;
              candle_fs_interval_abs_upper_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_raw_abs_correct;
              candle_cv_fs_raw_max_correct; FST; SND]);;

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

let candle_fs_raw_le_real = prove
 (`!x y. candle_fs_raw_le x y <=>
         candle_lc_zreal x <= candle_lc_zreal y`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_le_def; candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  EQ_TAC THEN REAL_ARITH_TAC);;

let candle_fs_raw_le_scaled = prove
 (`!denominator x y. 0 < denominator
     ==> (candle_fs_raw_le x y <=>
          candle_fs_raw_real denominator x <=
          candle_fs_raw_real denominator y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LT;
               candle_fs_raw_le_real]);;

let candle_fs_raw_min_real = prove
 (`!denominator x y. 0 < denominator
     ==> candle_fs_raw_real denominator (candle_fs_raw_min x y) =
         min (candle_fs_raw_real denominator x)
             (candle_fs_raw_real denominator y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_min_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC
    (SPECL [`denominator:num`; `x:num#num`; `y:num#num`]
      candle_fs_raw_le_scaled) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let candle_fs_raw_max_real = prove
 (`!denominator x y. 0 < denominator
     ==> candle_fs_raw_real denominator (candle_fs_raw_max x y) =
         max (candle_fs_raw_real denominator x)
             (candle_fs_raw_real denominator y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_max_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC
    (SPECL [`denominator:num`; `x:num#num`; `y:num#num`]
      candle_fs_raw_le_scaled) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let candle_fs_product_denominator_pos = prove
 (`0 < candle_fs_scale * candle_fs_scale`,
  REWRITE_TAC[LT_MULT; candle_fs_scale_pos]);;

let candle_fs_raw_product_real = prove
 (`!x y.
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (candle_q_zmul x y) =
     candle_fs_real x * candle_fs_real y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; candle_fs_real_def;
              candle_q_zreal_mul; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC candle_fs_scale_pos THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  CONV_TAC REAL_FIELD);;

let candle_fs_raw_product_min_real = prove
 (`!x y.
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (candle_fs_raw_min x y) =
     min
       (candle_fs_raw_real (candle_fs_scale * candle_fs_scale) x)
       (candle_fs_raw_real (candle_fs_scale * candle_fs_scale) y)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC candle_fs_raw_min_real THEN
  MATCH_ACCEPT_TAC candle_fs_product_denominator_pos);;

let candle_fs_raw_product_max_real = prove
 (`!x y.
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (candle_fs_raw_max x y) =
     max
       (candle_fs_raw_real (candle_fs_scale * candle_fs_scale) x)
       (candle_fs_raw_real (candle_fs_scale * candle_fs_scale) y)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC candle_fs_raw_max_real THEN
  MATCH_ACCEPT_TAC candle_fs_product_denominator_pos);;

let candle_fs_raw_interval_mul_sound = prove
 (`!i j x y.
     candle_fs_interval_contains i x /\
     candle_fs_interval_contains j y
     ==> candle_fs_raw_interval_contains
           (candle_fs_scale * candle_fs_scale)
           (candle_fs_raw_interval_mul i j) (x * y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_raw_interval_contains_def;
              candle_fs_raw_interval_mul_def;
              candle_fs_raw_product_min_real;
              candle_fs_raw_product_max_real;
              candle_fs_raw_product_real; FST; SND] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC candle_real_interval_mul THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_fixed_make_real = prove
 (`!positive negative.
     candle_fs_real (positive,negative) =
     candle_q_real (candle_q_fixed_make positive negative)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_fixed_make_real; candle_fs_real_def;
              candle_lc_zreal_def; candle_fs_scale_def;
              candle_q_taylor_model_scale_def; FST; SND]);;

let candle_fs_of_q_lower_real = prove
 (`!q. candle_fs_real (candle_fs_of_q_lower q) =
       candle_q_real (candle_q_fixed_round_lower q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_of_q_lower_def;
              candle_q_fixed_round_lower_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_make_def; FST;
                  candle_fs_fixed_make_real]);;

let candle_fs_of_q_upper_real = prove
 (`!q. candle_fs_real (candle_fs_of_q_upper q) =
       candle_q_real (candle_q_fixed_round_upper q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_of_q_upper_def;
              candle_q_fixed_round_upper_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_make_def; FST;
                  candle_fs_fixed_make_real]);;

let candle_fs_of_q_lower_sound = prove
 (`!q. candle_fs_real (candle_fs_of_q_lower q) <= candle_q_real q`,
  REWRITE_TAC[candle_fs_of_q_lower_real;
              candle_q_fixed_round_lower_sound]);;

let candle_fs_of_q_upper_sound = prove
 (`!q. candle_q_real q <= candle_fs_real (candle_fs_of_q_upper q)`,
  REWRITE_TAC[candle_fs_of_q_upper_real;
              candle_q_fixed_round_upper_sound]);;

let candle_fs_interval_of_q_sound = prove
 (`!i x. candle_q_interval_contains i x
         ==> candle_fs_interval_contains (candle_fs_interval_of_q i) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_fs_interval_contains_def;
              candle_fs_interval_of_q_def; FST; SND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC
      (SPEC
        `FST (i:((num#num)#num)#((num#num)#num))`
        candle_fs_of_q_lower_sound) THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC
      (SPEC
        `SND (i:((num#num)#num)#((num#num)#num))`
        candle_fs_of_q_upper_sound) THEN
    ASM_REAL_ARITH_TAC]);;

let candle_fs_interval_constant_sound = prove
 (`!q. candle_fs_interval_contains
         (candle_fs_interval_constant q) (candle_q_real q)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_interval_constant_def; FST; SND;
              candle_fs_of_q_lower_sound; candle_fs_of_q_upper_sound]);;

let candle_fs_interval_neg_sound = prove
 (`!i x. candle_fs_interval_contains i x
         ==> candle_fs_interval_contains (candle_fs_interval_neg i) (--x)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_interval_neg_def; candle_fs_raw_neg_real_scaled;
              FST; SND] THEN
  REAL_ARITH_TAC);;

let candle_fs_interval_add_sound = prove
 (`!i j x y.
     candle_fs_interval_contains i x /\
     candle_fs_interval_contains j y
     ==> candle_fs_interval_contains (candle_fs_interval_add i j) (x + y)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_interval_add_def; candle_fs_add_real;
              FST; SND] THEN
  REAL_ARITH_TAC);;

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

let candle_fs_raw_real_divide = prove
 (`!denominator z. 0 < denominator
     ==> candle_fs_raw_real (denominator * candle_fs_scale) z =
         (candle_lc_zreal z / &denominator) / &candle_fs_scale`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC candle_fs_scale_pos THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  CONV_TAC REAL_FIELD);;

let candle_fs_floor_div_scaled_sound = prove
 (`!z denominator. 0 < denominator
     ==> candle_fs_real (candle_fs_floor_div z denominator) <=
         candle_fs_raw_real (denominator * candle_fs_scale) z`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_fs_real_def; candle_fs_raw_real_divide] THEN
  SUBGOAL_THEN `&0 < &(candle_fs_scale)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; candle_fs_scale_pos];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC candle_fs_floor_div_sound THEN ASM_ARITH_TAC);;

let candle_fs_ceil_div_scaled_sound = prove
 (`!z denominator. 0 < denominator
     ==> candle_fs_raw_real (denominator * candle_fs_scale) z <=
         candle_fs_real (candle_fs_ceil_div z denominator)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_fs_real_def; candle_fs_raw_real_divide] THEN
  SUBGOAL_THEN `&0 < &(candle_fs_scale)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; candle_fs_scale_pos];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC candle_fs_ceil_div_sound THEN ASM_ARITH_TAC);;

let candle_fs_raw_interval_round_sound = prove
 (`!denominator i x. 0 < denominator /\
     candle_fs_raw_interval_contains
       (denominator * candle_fs_scale) i x
     ==> candle_fs_interval_contains
           (candle_fs_raw_interval_round denominator i) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_interval_contains_def;
              candle_fs_interval_contains_def;
              candle_fs_raw_interval_round_def; FST; SND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `candle_fs_raw_real (denominator * candle_fs_scale)
        (FST (i:(num#num)#(num#num)))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_fs_floor_div_scaled_sound THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `candle_fs_raw_real (denominator * candle_fs_scale)
        (SND (i:(num#num)#(num#num)))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_fs_ceil_div_scaled_sound THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_interval_mul_sound = prove
 (`!i j x y.
     candle_fs_interval_contains i x /\
     candle_fs_interval_contains j y
     ==> candle_fs_interval_contains
           (candle_fs_raw_interval_round candle_fs_scale
             (candle_fs_raw_interval_mul i j))
           (x * y)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_raw_interval_round_sound THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC candle_fs_scale_pos;
    MATCH_MP_TAC candle_fs_raw_interval_mul_sound THEN
    ASM_REWRITE_TAC[]]);;

end;;
