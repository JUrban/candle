(* ========================================================================== *)
(* Proof-producing exact rationals for reflected Flyspeck certificate checks. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. Load after the linear-combination realization. *)
(* A rational is ((positive,negative),denominator_predecessor), so its        *)
(* denominator is structurally SUC denominator_predecessor and can never be   *)
(* zero. No floating result or untrusted ML arithmetic authorizes a theorem.  *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination_realize.ml";;

module Candle_cv_exact_rational_core = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;

(* -------------------------------------------------------------------------- *)
(* Ordinary exact arithmetic and its real denotation.                         *)
(* -------------------------------------------------------------------------- *)

let candle_q_den_def = new_definition
 `candle_q_den (q:(num#num)#num) = SUC (SND q)`;;

let candle_q_den_product_pred_def = new_definition
 `candle_q_den_product_pred (d1:num) (d2:num) = d1 + d2 + d1 * d2`;;

let candle_q_den_product = prove
 (`!d1 d2.
     SUC (candle_q_den_product_pred d1 d2) = SUC d1 * SUC d2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_den_product_pred_def] THEN
  CONV_TAC NUM_RING);;

let candle_q_zmul_def = new_definition
 `candle_q_zmul (x:num#num) (y:num#num) =
    (FST x * FST y + SND x * SND y,
     FST x * SND y + SND x * FST y)`;;

let candle_q_add_def = new_definition
 `candle_q_add (x:(num#num)#num) (y:(num#num)#num) =
    (candle_lc_zadd
       (candle_lc_zscale (candle_q_den y) (FST x))
       (candle_lc_zscale (candle_q_den x) (FST y)),
     candle_q_den_product_pred (SND x) (SND y))`;;

let candle_q_mul_def = new_definition
 `candle_q_mul (x:(num#num)#num) (y:(num#num)#num) =
    (candle_q_zmul (FST x) (FST y),
     candle_q_den_product_pred (SND x) (SND y))`;;

let candle_q_neg_def = new_definition
 `candle_q_neg (x:(num#num)#num) =
    ((SND (FST x),FST (FST x)),SND x)`;;

let candle_q_real_def = new_definition
 `candle_q_real (q:(num#num)#num) =
    candle_lc_zreal (FST q) / &(candle_q_den q)`;;

let candle_q_zreal_mul = prove
 (`!x y.
     candle_lc_zreal (candle_q_zmul x y) =
     candle_lc_zreal x * candle_lc_zreal y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_lc_zreal_def; candle_q_zmul_def;
              GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  REAL_ARITH_TAC);;

let candle_q_real_add = prove
 (`!x y.
     candle_q_real (candle_q_add x y) =
     candle_q_real x + candle_q_real y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_real_def; candle_q_add_def; candle_q_den_def;
              candle_q_den_product; candle_lc_zreal_add;
              candle_lc_zreal_scale; GSYM REAL_OF_NUM_MUL] THEN
  CONV_TAC REAL_FIELD);;

let candle_q_real_mul = prove
 (`!x y.
     candle_q_real (candle_q_mul x y) =
     candle_q_real x * candle_q_real y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_real_def; candle_q_mul_def; candle_q_den_def;
              candle_q_den_product; candle_q_zreal_mul;
              GSYM REAL_OF_NUM_MUL] THEN
  CONV_TAC REAL_FIELD);;

let candle_q_real_neg = prove
 (`!x. candle_q_real (candle_q_neg x) = --(candle_q_real x)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_real_def; candle_q_neg_def;
              candle_q_den_def; candle_lc_zreal_def; FST; SND; real_div] THEN
  CONV_TAC REAL_RING);;

(* Exact interval addition and negation are the first operations shared by    *)
(* Taylor bounds and the LP rational-normalization boundary.                  *)

let candle_q_interval_add_def = new_definition
 `candle_q_interval_add
    (x:((num#num)#num)#((num#num)#num)) y =
    (candle_q_add (FST x) (FST y),
     candle_q_add (SND x) (SND y))`;;

let candle_q_interval_neg_def = new_definition
 `candle_q_interval_neg
    (x:((num#num)#num)#((num#num)#num)) =
    (candle_q_neg (SND x),candle_q_neg (FST x))`;;

let candle_q_interval_contains_def = new_definition
 `candle_q_interval_contains
    (i:((num#num)#num)#((num#num)#num)) (x:real) <=>
    candle_q_real (FST i) <= x /\ x <= candle_q_real (SND i)`;;

let candle_q_interval_add_sound = prove
 (`!i j x y.
     candle_q_interval_contains i x /\
     candle_q_interval_contains j y
     ==> candle_q_interval_contains (candle_q_interval_add i j) (x + y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_q_interval_add_def; candle_q_real_add] THEN
  REAL_ARITH_TAC);;

let candle_q_interval_neg_sound = prove
 (`!i x.
     candle_q_interval_contains i x
     ==> candle_q_interval_contains (candle_q_interval_neg i) (--x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_q_interval_neg_def; candle_q_real_neg] THEN
  REAL_ARITH_TAC);;

(* -------------------------------------------------------------------------- *)
(* cval representation and verified evaluator program.                       *)
(* -------------------------------------------------------------------------- *)

let candle_cv_q_def = new_definition
 `candle_cv_q (q:(num#num)#num) =
    Cexp_pair (candle_cv_lc_z (FST q)) (Cexp_num (SND q))`;;

let candle_cv_q_decode_def = define
 `(candle_cv_q_decode (Cexp_num n) = (((0,0),0):(num#num)#num)) /\
  (candle_cv_q_decode (Cexp_pair z d) =
     (candle_cv_lc_z_decode z,candle_cv_lc_num_decode d))`;;

let candle_cv_q_roundtrip = prove
 (`!q:(num#num)#num. candle_cv_q_decode (candle_cv_q q) = q`,
  REWRITE_TAC[candle_cv_q_decode_def; candle_cv_q_def;
              candle_cv_lc_z_roundtrip; candle_cv_lc_num_decode_def]);;

let candle_cv_q_den_def = new_definition
 `candle_cv_q_den q = Cexp_add (Cexp_snd q) (Cexp_num 1)`;;

let candle_cv_q_den_product_pred_def = new_definition
 `candle_cv_q_den_product_pred d1 d2 =
    Cexp_add (Cexp_add d1 d2) (Cexp_mul d1 d2)`;;

let candle_cv_q_zmul_def = new_definition
 `candle_cv_q_zmul x y =
    Cexp_pair
      (Cexp_add
        (Cexp_mul (Cexp_fst x) (Cexp_fst y))
        (Cexp_mul (Cexp_snd x) (Cexp_snd y)))
      (Cexp_add
        (Cexp_mul (Cexp_fst x) (Cexp_snd y))
        (Cexp_mul (Cexp_snd x) (Cexp_fst y)))`;;

let candle_cv_q_add_def = new_definition
 `candle_cv_q_add x y =
    Cexp_pair
      (candle_cv_lc_zadd
        (candle_cv_lc_zscale (candle_cv_q_den y) (Cexp_fst x))
        (candle_cv_lc_zscale (candle_cv_q_den x) (Cexp_fst y)))
      (candle_cv_q_den_product_pred (Cexp_snd x) (Cexp_snd y))`;;

let candle_cv_q_mul_def = new_definition
 `candle_cv_q_mul x y =
    Cexp_pair
      (candle_cv_q_zmul (Cexp_fst x) (Cexp_fst y))
      (candle_cv_q_den_product_pred (Cexp_snd x) (Cexp_snd y))`;;

let candle_cv_q_neg_def = new_definition
 `candle_cv_q_neg x =
    Cexp_pair
      (Cexp_pair (Cexp_snd (Cexp_fst x)) (Cexp_fst (Cexp_fst x)))
      (Cexp_snd x)`;;

let candle_cv_q_compute_eqs = map SPEC_ALL
 [candle_cv_lc_zadd_def;
  candle_cv_lc_zscale_def;
  candle_cv_q_den_def;
  candle_cv_q_den_product_pred_def;
  candle_cv_q_zmul_def;
  candle_cv_q_add_def;
  candle_cv_q_mul_def;
  candle_cv_q_neg_def];;

let candle_cv_q_den_correct = prove
 (`!q. candle_cv_q_den (candle_cv_q q) = Cexp_num (candle_q_den q)`,
  REWRITE_TAC[candle_cv_q_den_def; candle_cv_q_def; candle_q_den_def;
              cexp_snd_def; cexp_add_def; ADD1]);;

let candle_cv_q_den_product_pred_correct = prove
 (`!d1 d2.
     candle_cv_q_den_product_pred (Cexp_num d1) (Cexp_num d2) =
     Cexp_num (candle_q_den_product_pred d1 d2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_den_product_pred_def;
              candle_q_den_product_pred_def; cexp_add_def; cexp_mul_def] THEN
  AP_TERM_TAC THEN CONV_TAC NUM_RING);;

let candle_cv_q_zmul_correct = prove
 (`!x y.
     candle_cv_q_zmul (candle_cv_lc_z x) (candle_cv_lc_z y) =
     candle_cv_lc_z (candle_q_zmul x y)`,
  REWRITE_TAC[candle_cv_q_zmul_def; candle_cv_lc_z_def;
              candle_q_zmul_def; cexp_fst_def; cexp_snd_def;
              cexp_add_def; cexp_mul_def]);;

let candle_cv_q_add_correct = prove
 (`!x y.
     candle_cv_q_add (candle_cv_q x) (candle_cv_q y) =
     candle_cv_q (candle_q_add x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_add_def; candle_cv_q_def; candle_q_add_def;
              cexp_fst_def; cexp_snd_def; candle_cv_q_den_correct;
              candle_cv_lc_zscale_correct; candle_cv_lc_zadd_correct;
              candle_cv_q_den_product_pred_correct]);;

let candle_cv_q_mul_correct = prove
 (`!x y.
     candle_cv_q_mul (candle_cv_q x) (candle_cv_q y) =
     candle_cv_q (candle_q_mul x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_mul_def; candle_cv_q_def; candle_q_mul_def;
              cexp_fst_def; cexp_snd_def; candle_cv_q_zmul_correct;
              candle_cv_q_den_product_pred_correct]);;

let candle_cv_q_neg_correct = prove
 (`!x.
     candle_cv_q_neg (candle_cv_q x) = candle_cv_q (candle_q_neg x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_neg_def; candle_cv_q_def; candle_q_neg_def;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def]);;

end;;
