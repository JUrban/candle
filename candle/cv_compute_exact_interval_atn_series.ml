(* ========================================================================== *)
(* Reflected exact interval bounds for arctangent on (-1,1).                 *)
(*                                                                            *)
(* The action-296 Flyspeck source keeps the arctangent argument in this small *)
(* range.  Fixed odd/even alternating sums therefore give a compact first    *)
(* certificate without range reduction.  All endpoint arithmetic is exact   *)
(* rational data; the analytic fact is discharged once by the existing       *)
(* Flyspeck arctangent-series theorems.                                       *)
(* ========================================================================== *)

(* The exact-rational and interval support is supplied by the sealed analytic
   driver checkpoint used by this focused prototype. *)
needs "trig/atn.hl";;

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_rational_normalize;;
open Candle_cv_exact_interval_core;;
open Atn;;

let candle_q_atn_zero_def = new_definition
 `candle_q_atn_zero = (((0,0),0):(num#num)#num)`;;

let candle_q_atn_one_def = new_definition
 `candle_q_atn_one = (((1,0),0):(num#num)#num)`;;

let candle_q_atn_neg_one_def = new_definition
 `candle_q_atn_neg_one = (((0,1),0):(num#num)#num)`;;

let candle_q_atn_third_def = new_definition
 `candle_q_atn_third = (((1,0),2):(num#num)#num)`;;

let candle_q_atn_fifth_def = new_definition
 `candle_q_atn_fifth = (((1,0),4):(num#num)#num)`;;

let candle_q_atn_seventh_def = new_definition
 `candle_q_atn_seventh = (((1,0),6):(num#num)#num)`;;

let candle_q_atn_ninth_def = new_definition
 `candle_q_atn_ninth = (((1,0),8):(num#num)#num)`;;

let candle_q_atn_eleventh_def = new_definition
 `candle_q_atn_eleventh = (((1,0),10):(num#num)#num)`;;

let candle_q_atn_thirteenth_def = new_definition
 `candle_q_atn_thirteenth = (((1,0),12):(num#num)#num)`;;

let candle_q_atn_pos_lower_def = new_definition
 `candle_q_atn_pos_lower x =
    let x2 = candle_q_mul_normalized x x in
    candle_q_mul_normalized x
      (candle_q_add_normalized candle_q_atn_one
        (candle_q_mul_normalized x2
          (candle_q_add_normalized (candle_q_neg candle_q_atn_third)
            (candle_q_mul_normalized x2
              (candle_q_add_normalized candle_q_atn_fifth
                (candle_q_mul_normalized x2
                  (candle_q_add_normalized
                    (candle_q_neg candle_q_atn_seventh)
                    (candle_q_mul_normalized x2
                      (candle_q_add_normalized candle_q_atn_ninth
                        (candle_q_mul_normalized x2
                          (candle_q_neg candle_q_atn_eleventh)))))))))))`;;

let candle_q_atn_pos_upper_def = new_definition
 `candle_q_atn_pos_upper x =
    let x2 = candle_q_mul_normalized x x in
    candle_q_mul_normalized x
      (candle_q_add_normalized candle_q_atn_one
        (candle_q_mul_normalized x2
          (candle_q_add_normalized (candle_q_neg candle_q_atn_third)
            (candle_q_mul_normalized x2
              (candle_q_add_normalized candle_q_atn_fifth
                (candle_q_mul_normalized x2
                  (candle_q_add_normalized
                    (candle_q_neg candle_q_atn_seventh)
                    (candle_q_mul_normalized x2
                      (candle_q_add_normalized candle_q_atn_ninth
                        (candle_q_mul_normalized x2
                          (candle_q_add_normalized
                            (candle_q_neg candle_q_atn_eleventh)
                            (candle_q_mul_normalized x2
                              candle_q_atn_thirteenth))))))))))))`;;

let candle_q_atn_lower_def = new_definition
 `candle_q_atn_lower x =
    if candle_q_le candle_q_atn_zero x then
      candle_q_atn_pos_lower x
    else candle_q_neg (candle_q_atn_pos_upper (candle_q_neg x))`;;

let candle_q_atn_upper_def = new_definition
 `candle_q_atn_upper x =
    if candle_q_le candle_q_atn_zero x then
      candle_q_atn_pos_upper x
    else candle_q_neg (candle_q_atn_pos_lower (candle_q_neg x))`;;

let candle_q_interval_atn_series_def = new_definition
 `candle_q_interval_atn_series
    (input:((num#num)#num)#((num#num)#num)) =
    (candle_q_atn_lower (FST input),
     candle_q_atn_upper (SND input))`;;

let candle_q_interval_atn_series_domain_def = new_definition
 `candle_q_interval_atn_series_domain
    (input:((num#num)#num)#((num#num)#num)) <=>
    candle_q_le (FST input) (SND input) /\
    ~candle_q_le (FST input) candle_q_atn_neg_one /\
    ~candle_q_le candle_q_atn_one (SND input)`;;

let candle_q_atn_zero_real = prove
 (`candle_q_real candle_q_atn_zero = &0`,
  REWRITE_TAC[candle_q_atn_zero_def; candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_q_atn_one_real = prove
 (`candle_q_real candle_q_atn_one = &1`,
  REWRITE_TAC[candle_q_atn_one_def; candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_q_atn_neg_one_real = prove
 (`candle_q_real candle_q_atn_neg_one = -- &1`,
  REWRITE_TAC[candle_q_atn_neg_one_def; candle_q_real_def;
              candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let candle_q_atn_pos_lower_real = prove
 (`!x.
     candle_q_real (candle_q_atn_pos_lower x) =
     sum (0..5)
       (\i. ((-- &1) pow i / &(2 * i + 1)) *
            candle_q_real x pow (2 * i + 1))`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_atn_pos_lower_def; LET_DEF; LET_END_DEF;
              candle_q_real_add_normalized;
              candle_q_real_mul_normalized; candle_q_real_neg;
              candle_q_atn_one_def; candle_q_atn_third_def;
              candle_q_atn_fifth_def; candle_q_atn_seventh_def;
              candle_q_atn_ninth_def; candle_q_atn_eleventh_def] THEN
  REWRITE_TAC[
              candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND;
              SUM_CLAUSES_NUMSEG; LE_0] THEN
  CONV_TAC (RAND_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC REAL_RING);;

let candle_q_atn_pos_upper_real = prove
 (`!x.
     candle_q_real (candle_q_atn_pos_upper x) =
     sum (0..6)
       (\i. ((-- &1) pow i / &(2 * i + 1)) *
            candle_q_real x pow (2 * i + 1))`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_atn_pos_upper_def; LET_DEF; LET_END_DEF;
              candle_q_real_add_normalized;
              candle_q_real_mul_normalized; candle_q_real_neg;
              candle_q_atn_one_def; candle_q_atn_third_def;
              candle_q_atn_fifth_def; candle_q_atn_seventh_def;
              candle_q_atn_ninth_def; candle_q_atn_eleventh_def;
              candle_q_atn_thirteenth_def] THEN
  REWRITE_TAC[
              candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND;
              SUM_CLAUSES_NUMSEG; LE_0] THEN
  CONV_TAC (RAND_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC REAL_RING);;

let candle_atn_neg_alt = prove
 (`!x. atn x = --(atn (--x))`,
  GEN_TAC THEN REWRITE_TAC[GSYM ATN_NEG; REAL_NEG_NEG]);;

let candle_q_atn_lower_sound = prove
 (`!x.
     ~candle_q_le x candle_q_atn_neg_one /\
     ~candle_q_le candle_q_atn_one x
     ==> candle_q_real (candle_q_atn_lower x) <= atn (candle_q_real x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_atn_lower_def] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[candle_q_atn_pos_lower_real] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC
      (REWRITE_RULE[candle_q_le_real; candle_q_atn_zero_real;
                    candle_q_atn_neg_one_real; candle_q_atn_one_real]) THEN
    MATCH_MP_TAC
      (SPECL [`candle_q_real x`; `5`] atn_poly_pos_lower_bound) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[candle_q_real_neg; candle_q_atn_pos_upper_real] THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC[candle_atn_neg_alt] THEN
    REWRITE_TAC[REAL_LE_NEG2] THEN
    RULE_ASSUM_TAC
      (REWRITE_RULE[candle_q_le_real; candle_q_atn_zero_real;
                    candle_q_atn_neg_one_real; candle_q_atn_one_real]) THEN
    MATCH_MP_TAC
      (SPECL [`--(candle_q_real x)`; `6`] atn_poly_pos_upper_bound) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC]);;

let candle_q_atn_upper_sound = prove
 (`!x.
     ~candle_q_le x candle_q_atn_neg_one /\
     ~candle_q_le candle_q_atn_one x
     ==> atn (candle_q_real x) <= candle_q_real (candle_q_atn_upper x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_atn_upper_def] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[candle_q_atn_pos_upper_real] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC
      (REWRITE_RULE[candle_q_le_real; candle_q_atn_zero_real;
                    candle_q_atn_neg_one_real; candle_q_atn_one_real]) THEN
    MATCH_MP_TAC
      (SPECL [`candle_q_real x`; `6`] atn_poly_pos_upper_bound) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[candle_q_real_neg; candle_q_atn_pos_lower_real] THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC[candle_atn_neg_alt] THEN
    REWRITE_TAC[REAL_LE_NEG2] THEN
    RULE_ASSUM_TAC
      (REWRITE_RULE[candle_q_le_real; candle_q_atn_zero_real;
                    candle_q_atn_neg_one_real; candle_q_atn_one_real]) THEN
    MATCH_MP_TAC
      (SPECL [`--(candle_q_real x)`; `5`] atn_poly_pos_lower_bound) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC]);;

let candle_q_interval_atn_series_sound = prove
 (`!input:(((num#num)#num)#((num#num)#num)). !x.
     candle_q_interval_atn_series_domain input /\
     candle_q_interval_contains input x
     ==> candle_q_interval_contains
           (candle_q_interval_atn_series input) (atn x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_atn_series_domain_def;
              candle_q_interval_contains_def;
              candle_q_interval_atn_series_def; FST; SND] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_le_real; candle_q_atn_neg_one_real;
                  candle_q_atn_one_real]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `atn (candle_q_real
        (FST (input:(((num#num)#num)#((num#num)#num)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
        (SPEC
          `FST (input:(((num#num)#num)#((num#num)#num)))`
          candle_q_atn_lower_sound) THEN
      REWRITE_TAC[candle_q_le_real; candle_q_atn_neg_one_real;
                  candle_q_atn_one_real] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[ATN_MONO_LE_EQ]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `atn (candle_q_real
        (SND (input:(((num#num)#num)#((num#num)#num)))))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[ATN_MONO_LE_EQ];
      MATCH_MP_TAC
        (SPEC
          `SND (input:(((num#num)#num)#((num#num)#num)))`
          candle_q_atn_upper_sound) THEN
      REWRITE_TAC[candle_q_le_real; candle_q_atn_neg_one_real;
                  candle_q_atn_one_real] THEN
      ASM_REAL_ARITH_TAC]]);;

(* Reflected evaluator.  The fixed coefficients are literal encoded rationals; *)
(* normalization remains the shared verified adaptive-normalization policy.    *)

let candle_cv_q_atn_zero_def = new_definition
 `candle_cv_q_atn_zero = candle_cv_q candle_q_atn_zero`;;
let candle_cv_q_atn_one_def = new_definition
 `candle_cv_q_atn_one = candle_cv_q candle_q_atn_one`;;
let candle_cv_q_atn_neg_one_def = new_definition
 `candle_cv_q_atn_neg_one = candle_cv_q candle_q_atn_neg_one`;;
let candle_cv_q_atn_third_def = new_definition
 `candle_cv_q_atn_third = candle_cv_q candle_q_atn_third`;;
let candle_cv_q_atn_fifth_def = new_definition
 `candle_cv_q_atn_fifth = candle_cv_q candle_q_atn_fifth`;;
let candle_cv_q_atn_seventh_def = new_definition
 `candle_cv_q_atn_seventh = candle_cv_q candle_q_atn_seventh`;;
let candle_cv_q_atn_ninth_def = new_definition
 `candle_cv_q_atn_ninth = candle_cv_q candle_q_atn_ninth`;;
let candle_cv_q_atn_eleventh_def = new_definition
 `candle_cv_q_atn_eleventh = candle_cv_q candle_q_atn_eleventh`;;
let candle_cv_q_atn_thirteenth_def = new_definition
 `candle_cv_q_atn_thirteenth = candle_cv_q candle_q_atn_thirteenth`;;

let candle_cv_q_atn_zero_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_atn_zero_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    candle_cv_q_atn_zero_def;;
let candle_cv_q_atn_one_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_atn_one_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    candle_cv_q_atn_one_def;;
let candle_cv_q_atn_neg_one_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_atn_neg_one_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    candle_cv_q_atn_neg_one_def;;
let candle_cv_q_atn_third_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_atn_third_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    candle_cv_q_atn_third_def;;
let candle_cv_q_atn_fifth_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_atn_fifth_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    candle_cv_q_atn_fifth_def;;
let candle_cv_q_atn_seventh_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_atn_seventh_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    candle_cv_q_atn_seventh_def;;
let candle_cv_q_atn_ninth_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_atn_ninth_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    candle_cv_q_atn_ninth_def;;
let candle_cv_q_atn_eleventh_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_atn_eleventh_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    candle_cv_q_atn_eleventh_def;;
let candle_cv_q_atn_thirteenth_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_atn_thirteenth_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    candle_cv_q_atn_thirteenth_def;;

let candle_cv_q_atn_pos_lower_def = new_definition
 `candle_cv_q_atn_pos_lower x =
    let x2 = candle_cv_q_mul_normalized x x in
    candle_cv_q_mul_normalized x
      (candle_cv_q_add_normalized candle_cv_q_atn_one
        (candle_cv_q_mul_normalized x2
          (candle_cv_q_add_normalized
            (candle_cv_q_neg candle_cv_q_atn_third)
            (candle_cv_q_mul_normalized x2
              (candle_cv_q_add_normalized candle_cv_q_atn_fifth
                (candle_cv_q_mul_normalized x2
                  (candle_cv_q_add_normalized
                    (candle_cv_q_neg candle_cv_q_atn_seventh)
                    (candle_cv_q_mul_normalized x2
                      (candle_cv_q_add_normalized candle_cv_q_atn_ninth
                        (candle_cv_q_mul_normalized x2
                          (candle_cv_q_neg candle_cv_q_atn_eleventh)))))))))))`;;

let candle_cv_q_atn_pos_upper_def = new_definition
 `candle_cv_q_atn_pos_upper x =
    let x2 = candle_cv_q_mul_normalized x x in
    candle_cv_q_mul_normalized x
      (candle_cv_q_add_normalized candle_cv_q_atn_one
        (candle_cv_q_mul_normalized x2
          (candle_cv_q_add_normalized
            (candle_cv_q_neg candle_cv_q_atn_third)
            (candle_cv_q_mul_normalized x2
              (candle_cv_q_add_normalized candle_cv_q_atn_fifth
                (candle_cv_q_mul_normalized x2
                  (candle_cv_q_add_normalized
                    (candle_cv_q_neg candle_cv_q_atn_seventh)
                    (candle_cv_q_mul_normalized x2
                      (candle_cv_q_add_normalized candle_cv_q_atn_ninth
                        (candle_cv_q_mul_normalized x2
                          (candle_cv_q_add_normalized
                            (candle_cv_q_neg candle_cv_q_atn_eleventh)
                            (candle_cv_q_mul_normalized x2
                            candle_cv_q_atn_thirteenth))))))))))))`;;

let candle_cv_q_atn_pos_lower_compute =
  REWRITE_RULE[LET_DEF; LET_END_DEF] candle_cv_q_atn_pos_lower_def;;

let candle_cv_q_atn_pos_upper_compute =
  REWRITE_RULE[LET_DEF; LET_END_DEF] candle_cv_q_atn_pos_upper_def;;

let candle_cv_q_atn_lower_def = new_definition
 `candle_cv_q_atn_lower x =
    Cexp_if (candle_cv_q_le candle_cv_q_atn_zero x)
      (candle_cv_q_atn_pos_lower x)
      (candle_cv_q_neg (candle_cv_q_atn_pos_upper (candle_cv_q_neg x)))`;;

let candle_cv_q_atn_upper_def = new_definition
 `candle_cv_q_atn_upper x =
    Cexp_if (candle_cv_q_le candle_cv_q_atn_zero x)
      (candle_cv_q_atn_pos_upper x)
      (candle_cv_q_neg (candle_cv_q_atn_pos_lower (candle_cv_q_neg x)))`;;

let candle_cv_q_interval_atn_series_def = new_definition
 `candle_cv_q_interval_atn_series input =
    Cexp_pair
      (candle_cv_q_atn_lower (Cexp_fst input))
      (candle_cv_q_atn_upper (Cexp_snd input))`;;

let candle_cv_q_interval_atn_series_domain_def = new_definition
 `candle_cv_q_interval_atn_series_domain input =
    Cexp_if (candle_cv_q_le (Cexp_fst input) (Cexp_snd input))
      (Cexp_if
        (candle_cv_q_le (Cexp_fst input) candle_cv_q_atn_neg_one)
        (Cexp_num 0)
        (Cexp_if
          (candle_cv_q_le candle_cv_q_atn_one (Cexp_snd input))
          (Cexp_num 0) (Cexp_num 1)))
      (Cexp_num 0)`;;

let candle_cv_q_atn_series_compute_eqs =
  candle_cv_q_order_compute_eqs @
  candle_cv_q_normalized_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_atn_zero_compute; candle_cv_q_atn_one_compute;
    candle_cv_q_atn_neg_one_compute; candle_cv_q_atn_third_compute;
    candle_cv_q_atn_fifth_compute; candle_cv_q_atn_seventh_compute;
    candle_cv_q_atn_ninth_compute; candle_cv_q_atn_eleventh_compute;
    candle_cv_q_atn_thirteenth_compute;
    candle_cv_q_atn_pos_lower_compute; candle_cv_q_atn_pos_upper_compute;
    candle_cv_q_atn_lower_def; candle_cv_q_atn_upper_def;
    candle_cv_q_interval_atn_series_def;
    candle_cv_q_interval_atn_series_domain_def];;

let candle_cv_q_atn_pos_lower_correct = prove
 (`!x.
     candle_cv_q_atn_pos_lower (candle_cv_q x) =
     candle_cv_q (candle_q_atn_pos_lower x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_atn_pos_lower_def;
              candle_q_atn_pos_lower_def; LET_DEF; LET_END_DEF;
              candle_cv_q_atn_one_def; candle_cv_q_atn_third_def;
              candle_cv_q_atn_fifth_def; candle_cv_q_atn_seventh_def;
              candle_cv_q_atn_ninth_def; candle_cv_q_atn_eleventh_def;
              candle_cv_q_mul_normalized_correct;
              candle_cv_q_add_normalized_correct;
              candle_cv_q_neg_correct]);;

let candle_cv_q_atn_pos_upper_correct = prove
 (`!x.
     candle_cv_q_atn_pos_upper (candle_cv_q x) =
     candle_cv_q (candle_q_atn_pos_upper x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_atn_pos_upper_def;
              candle_q_atn_pos_upper_def; LET_DEF; LET_END_DEF;
              candle_cv_q_atn_one_def; candle_cv_q_atn_third_def;
              candle_cv_q_atn_fifth_def; candle_cv_q_atn_seventh_def;
              candle_cv_q_atn_ninth_def; candle_cv_q_atn_eleventh_def;
              candle_cv_q_atn_thirteenth_def;
              candle_cv_q_mul_normalized_correct;
              candle_cv_q_add_normalized_correct;
              candle_cv_q_neg_correct]);;

let candle_cv_q_atn_lower_correct = prove
 (`!x.
     candle_cv_q_atn_lower (candle_cv_q x) =
     candle_cv_q (candle_q_atn_lower x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_atn_lower_def; candle_q_atn_lower_def;
              candle_cv_q_atn_zero_def; candle_cv_q_le_correct] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; candle_cv_q_atn_pos_lower_correct;
                  candle_cv_q_atn_pos_upper_correct;
                  candle_cv_q_neg_correct]);;

let candle_cv_q_atn_upper_correct = prove
 (`!x.
     candle_cv_q_atn_upper (candle_cv_q x) =
     candle_cv_q (candle_q_atn_upper x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_atn_upper_def; candle_q_atn_upper_def;
              candle_cv_q_atn_zero_def; candle_cv_q_le_correct] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; candle_cv_q_atn_pos_lower_correct;
                  candle_cv_q_atn_pos_upper_correct;
                  candle_cv_q_neg_correct]);;

let candle_cv_q_interval_atn_series_correct = prove
 (`!input.
     candle_cv_q_interval_atn_series (candle_cv_q_interval input) =
     candle_cv_q_interval (candle_q_interval_atn_series input)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_atn_series_def;
              candle_q_interval_atn_series_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_atn_lower_correct;
              candle_cv_q_atn_upper_correct]);;

let candle_cv_q_interval_atn_series_domain_correct = prove
 (`!input.
     candle_cv_q_interval_atn_series_domain
       (candle_cv_q_interval input) =
     Cexp_num
       (if candle_q_interval_atn_series_domain input then 1 else 0)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_atn_series_domain_def;
              candle_q_interval_atn_series_domain_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_atn_neg_one_def; candle_cv_q_atn_one_def;
              candle_cv_q_le_correct] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]));;
