(* ========================================================================== *)
(* Proof-producing square operation for exact reflected intervals.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Generic interval multiplication is sound for *)
(* x*x but forgets that both operands are the same value.  Intersecting its  *)
(* lower bound with the universal x^2 >= 0 fact recovers that dependency      *)
(* without trusting an ML-side sign or alias decision.                        *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_mul_core.ml";;

module Candle_cv_exact_interval_square_core = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;

let candle_q_interval_square_def = new_definition
 `candle_q_interval_square
    (i:((num#num)#num)#((num#num)#num)) =
    (candle_q_max (((0,0),0):(num#num)#num)
       (FST (candle_q_interval_mul i i)),
     SND (candle_q_interval_mul i i))`;;

let candle_real_square_tighten = prove
 (`!lo hi x:real.
     lo <= x * x /\ x * x <= hi
     ==> max (&0) lo <= x * x /\ x * x <= hi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_MAX_LE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LE_SQUARE]);;

let candle_q_interval_square_sound = prove
 (`!i x.
     candle_q_interval_contains i x
     ==> candle_q_interval_contains (candle_q_interval_square i) (x * x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `candle_q_interval_contains (candle_q_interval_mul i i) (x * x)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_interval_mul_sound THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_q_interval_square_def;FST;SND;
              candle_q_max_real] THEN
  REWRITE_TAC[candle_q_real_def;candle_q_den_def;
              candle_lc_zreal_def;real_div;REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  REWRITE_TAC[REAL_SUB_REFL;REAL_ADD_LID;REAL_INV_1;REAL_MUL_LZERO] THEN
  MATCH_MP_TAC candle_real_square_tighten THEN
  UNDISCH_TAC
    `candle_q_interval_contains (candle_q_interval_mul i i) (x * x)` THEN
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_q_real_def;candle_q_den_def;
              candle_lc_zreal_def;real_div] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC]);;

let candle_cv_q_interval_square_def = new_definition
 `candle_cv_q_interval_square i =
    Cexp_pair
      (candle_cv_q_max
        (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0))
        (Cexp_fst (candle_cv_q_interval_mul i i)))
      (Cexp_snd (candle_cv_q_interval_mul i i))`;;

let candle_cv_q_interval_square_compute_eqs =
  candle_cv_q_interval_mul_compute_eqs @
  map SPEC_ALL [candle_cv_q_interval_square_def];;

let candle_cv_q_zero_literal = prove
 (`Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0) =
   candle_cv_q (((0,0),0):(num#num)#num)`,
  REWRITE_TAC[candle_cv_q_def;
              Candle_cv_linear_combination_core.candle_cv_lc_z_def]);;

let candle_cv_q_interval_square_correct = prove
 (`!i.
     candle_cv_q_interval_square (candle_cv_q_interval i) =
     candle_cv_q_interval (candle_q_interval_square i)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_square_def;
              candle_q_interval_square_def;
              candle_cv_q_interval_mul_correct;
              candle_cv_q_zero_literal;
              candle_cv_q_interval_def;cexp_fst_def;cexp_snd_def;
              candle_cv_q_max_correct]);;

end;;
