(* ========================================================================== *)
(* Proved ordering and extrema for reflected exact rationals.                 *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. Comparison is exact cross multiplication; the *)
(* structurally positive denominator representation discharges every sign    *)
(* side condition used by the real-semantics theorem.                         *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_rational_core.ml";;

module Candle_cv_exact_rational_order_core = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;

let candle_q_le_def = new_definition
 `candle_q_le (x:(num#num)#num) y <=>
    FST (FST x) * candle_q_den y + SND (FST y) * candle_q_den x <=
    FST (FST y) * candle_q_den x + SND (FST x) * candle_q_den y`;;

let candle_q_min_def = new_definition
 `candle_q_min (x:(num#num)#num) y =
    if candle_q_le x y then x else y`;;

let candle_q_max_def = new_definition
 `candle_q_max (x:(num#num)#num) y =
    if candle_q_le x y then y else x`;;

let candle_q_den_pos = prove
 (`!q:(num#num)#num. 0 < candle_q_den q`,
  REWRITE_TAC[candle_q_den_def] THEN ARITH_TAC);;

let candle_real_div_mul = prove
 (`!b dx dy:real. b / dy * dx = (b * dx) / dy`,
  REWRITE_TAC[real_div; REAL_MUL_AC]);;

let candle_real_div_le_div = prove
 (`!a b dx dy:real.
     &0 < dx /\ &0 < dy
     ==> (a / dx <= b / dy <=> a * dy <= b * dx)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [candle_real_div_mul] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ]);;

let candle_q_le_real = prove
 (`!x y.
     candle_q_le x y <=> candle_q_real x <= candle_q_real y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_le_def; candle_q_real_def;
              candle_lc_zreal_def] THEN
  SUBGOAL_THEN `&0 < &(candle_q_den x)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN MATCH_ACCEPT_TAC candle_q_den_pos;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(candle_q_den y)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN MATCH_ACCEPT_TAC candle_q_den_pos;
    ALL_TAC] THEN
  ASM_SIMP_TAC[candle_real_div_le_div] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              REAL_SUB_RDISTRIB] THEN
  REAL_ARITH_TAC);;

let candle_q_min_real = prove
 (`!x y.
     candle_q_real (candle_q_min x y) =
     min (candle_q_real x) (candle_q_real y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[candle_q_min_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`x:(num#num)#num`; `y:(num#num)#num`]
    candle_q_le_real) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let candle_q_max_real = prove
 (`!x y.
     candle_q_real (candle_q_max x y) =
     max (candle_q_real x) (candle_q_real y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[candle_q_max_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (SPECL [`x:(num#num)#num`; `y:(num#num)#num`]
    candle_q_le_real) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let candle_cv_q_le_def = new_definition
 `candle_cv_q_le x y =
    Cexp_less
      (Cexp_add
        (Cexp_mul (Cexp_fst (Cexp_fst x)) (candle_cv_q_den y))
        (Cexp_mul (Cexp_snd (Cexp_fst y)) (candle_cv_q_den x)))
      (Cexp_add
        (Cexp_add
          (Cexp_mul (Cexp_fst (Cexp_fst y)) (candle_cv_q_den x))
          (Cexp_mul (Cexp_snd (Cexp_fst x)) (candle_cv_q_den y)))
        (Cexp_num 1))`;;

let candle_cv_q_min_def = new_definition
 `candle_cv_q_min x y = Cexp_if (candle_cv_q_le x y) x y`;;

let candle_cv_q_max_def = new_definition
 `candle_cv_q_max x y = Cexp_if (candle_cv_q_le x y) y x`;;

let candle_cv_q_order_compute_eqs =
  candle_cv_q_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_le_def;
    candle_cv_q_min_def;
    candle_cv_q_max_def];;

let candle_cv_q_le_correct = prove
 (`!x y.
     candle_cv_q_le (candle_cv_q x) (candle_cv_q y) =
     Cexp_num (if candle_q_le x y then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_le_def; candle_cv_q_def; candle_q_le_def;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_den_correct;
              cexp_mul_def; cexp_add_def; cexp_less_def;
              GSYM ADD1; LT_SUC_LE]);;

let candle_cv_q_min_correct = prove
 (`!x y.
     candle_cv_q_min (candle_cv_q x) (candle_cv_q y) =
     candle_cv_q (candle_q_min x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_min_def; candle_q_min_def;
              candle_cv_q_le_correct] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]);;

let candle_cv_q_max_correct = prove
 (`!x y.
     candle_cv_q_max (candle_cv_q x) (candle_cv_q y) =
     candle_cv_q (candle_q_max x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_max_def; candle_q_max_def;
              candle_cv_q_le_correct] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]);;

end;;
