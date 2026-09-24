(* ========================================================================== *)
(* Proof-producing reciprocal for exact reflected intervals.                 *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The endpoint operation is deliberately        *)
(* separate from its domain predicate.  A computed inverse can authorize a   *)
(* real enclosure only when the reflected predicate proves that the complete *)
(* input interval lies strictly on one side of zero.                          *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_rational_inv.ml";;
needs "candle/cv_compute_whole_box_taylor.ml";;

module Candle_cv_exact_interval_inv_core = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_exact_rational_inv;;

let candle_q_interval_not_zero_def = new_definition
 `candle_q_interval_not_zero
    (i:((num#num)#num)#((num#num)#num)) <=>
    ~candle_q_le (FST i) candle_q_zero \/
    ~candle_q_le candle_q_zero (SND i)`;;

let candle_q_interval_inv_def = new_definition
 `candle_q_interval_inv
    (i:((num#num)#num)#((num#num)#num)) =
    (candle_q_inv (SND i),candle_q_inv (FST i))`;;

let candle_q_interval_not_zero_real = prove
 (`!i. candle_q_interval_not_zero i <=>
       &0 < candle_q_real (FST i) \/
       candle_q_real (SND i) < &0`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_not_zero_def; candle_q_le_real;
              candle_q_zero_def; candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let candle_real_inv_antitone_negative = prove
 (`!x y:real. x <= y /\ y < &0 ==> inv y <= inv x`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`--y:real`; `--x:real`] REAL_LE_INV2) THEN
  ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_INV_NEG] THEN REAL_ARITH_TAC]);;

let candle_real_interval_inv_positive = prove
 (`!lo hi x:real.
     &0 < lo /\ lo <= x /\ x <= hi
     ==> inv hi <= inv x /\ inv x <= inv lo`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]);;

let candle_real_interval_inv_negative = prove
 (`!lo hi x:real.
     hi < &0 /\ lo <= x /\ x <= hi
     ==> inv hi <= inv x /\ inv x <= inv lo`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC candle_real_inv_antitone_negative THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_real_inv_antitone_negative THEN
    ASM_REAL_ARITH_TAC]);;

let candle_real_interval_inv = prove
 (`!lo hi x:real.
     (&0 < lo \/ hi < &0) /\ lo <= x /\ x <= hi
     ==> inv hi <= inv x /\ inv x <= inv lo`,
  MESON_TAC[candle_real_interval_inv_positive;
            candle_real_interval_inv_negative]);;

let candle_real_interval_endpoints_nonzero = prove
 (`!lo hi x:real.
     (&0 < lo \/ hi < &0) /\ lo <= x /\ x <= hi
     ==> ~(lo = &0) /\ ~(hi = &0)`,
  REAL_ARITH_TAC);;

let candle_q_interval_inv_sound = prove
 (`!i x.
     candle_q_interval_not_zero i /\ candle_q_interval_contains i x
     ==> candle_q_interval_contains (candle_q_interval_inv i) (inv x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_not_zero_real;
              candle_q_interval_contains_def;
              candle_q_interval_inv_def; FST; SND] THEN
  MESON_TAC[candle_real_interval_endpoints_nonzero;
            candle_q_nonzero_real; candle_q_inv_real;
            candle_real_interval_inv]);;

let candle_cv_q_interval_not_zero_def = new_definition
 `candle_cv_q_interval_not_zero i =
    Cexp_if (candle_cv_q_le (Cexp_fst i) candle_cv_q_zero)
      (Cexp_if (candle_cv_q_le candle_cv_q_zero (Cexp_snd i))
        (Cexp_num 0) (Cexp_num 1))
      (Cexp_num 1)`;;

let candle_cv_q_interval_inv_def = new_definition
 `candle_cv_q_interval_inv i =
    Cexp_pair
      (candle_cv_q_inv (Cexp_snd i))
      (candle_cv_q_inv (Cexp_fst i))`;;

let candle_cv_q_interval_inv_compute_eqs =
  candle_cv_q_order_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_inv_def;
    candle_cv_q_zero_compute;
    candle_cv_q_interval_not_zero_def;
    candle_cv_q_interval_inv_def];;

let candle_cv_q_interval_not_zero_correct = prove
 (`!i.
     candle_cv_q_interval_not_zero (candle_cv_q_interval i) =
     Cexp_num (if candle_q_interval_not_zero i then 1 else 0)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_not_zero_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_zero_def; candle_q_interval_not_zero_def;
              candle_cv_q_le_correct] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]));;

let candle_cv_q_interval_inv_correct = prove
 (`!i.
     candle_cv_q_interval_inv (candle_cv_q_interval i) =
     candle_cv_q_interval (candle_q_interval_inv i)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_inv_def;
              candle_cv_q_interval_def; candle_q_interval_inv_def;
              cexp_fst_def; cexp_snd_def; candle_cv_q_inv_correct]);;

end;;
