(* ========================================================================== *)
(* Reflected exact interval bounds for arctangent, including endpoints outside *)
(* [-1,1].  Exact endpoints at -1 or 1 remain rejected fail-closed.           *)
(*                                                                            *)
(* The series checker is retained on (-1,1).  Endpoints strictly outside that *)
(* range are reduced with ATN_INV, independently of the other endpoint.  This *)
(* is important for genuine Flyspeck boxes whose enclosure straddles -1.      *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_atn_series.ml";;
needs "candle/cv_compute_exact_rational_inv.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_rational_normalize;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_rational_inv;;
open Atn;;

(* Keep this constant below the analytic-jet layer so arctangent range
   reduction does not depend cyclically on the pi/2 jet constructor. *)
let candle_q_atn_pi_half_interval_def = new_definition
 `candle_q_atn_pi_half_interval =
    ((((1686629713,0),1073741823),
      ((6746518853,0),4294967295)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_atn_pi_half_interval_sound = prove
 (`candle_q_interval_contains candle_q_atn_pi_half_interval (pi / &2)`,
  REWRITE_TAC[candle_q_atn_pi_half_interval_def;
              candle_q_interval_contains_def;
              candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  MP_TAC PI_APPROX_32 THEN
  REWRITE_TAC[REAL_ARITH
   `abs(x - a) <= e <=> a - e <= x /\ x <= a + e`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let candle_q_atn_range_domain_def = new_definition
 `candle_q_atn_range_domain x <=>
    if candle_q_le x candle_q_atn_neg_one then
      ~candle_q_le candle_q_atn_neg_one x
    else if candle_q_le candle_q_atn_one x then
      ~candle_q_le x candle_q_atn_one
    else T`;;

let candle_q_atn_range_argument_def = new_definition
 `candle_q_atn_range_argument x =
    if candle_q_le x candle_q_atn_neg_one then
      candle_q_neg (candle_q_inv x)
    else if candle_q_le candle_q_atn_one x then
      candle_q_inv x
    else x`;;

let candle_q_atn_range_lower_def = new_definition
 `candle_q_atn_range_lower x =
    if candle_q_le x candle_q_atn_neg_one then
      candle_q_add_normalized
        (candle_q_atn_lower (candle_q_atn_range_argument x))
        (candle_q_neg (SND candle_q_atn_pi_half_interval))
    else if candle_q_le candle_q_atn_one x then
      candle_q_add_normalized
        (FST candle_q_atn_pi_half_interval)
        (candle_q_neg
          (candle_q_atn_upper (candle_q_atn_range_argument x)))
    else candle_q_atn_lower x`;;

let candle_q_atn_range_upper_def = new_definition
 `candle_q_atn_range_upper x =
    if candle_q_le x candle_q_atn_neg_one then
      candle_q_add_normalized
        (candle_q_atn_upper (candle_q_atn_range_argument x))
        (candle_q_neg (FST candle_q_atn_pi_half_interval))
    else if candle_q_le candle_q_atn_one x then
      candle_q_add_normalized
        (SND candle_q_atn_pi_half_interval)
        (candle_q_neg
          (candle_q_atn_lower (candle_q_atn_range_argument x)))
    else candle_q_atn_upper x`;;

let candle_q_interval_atn_range_def = new_definition
 `candle_q_interval_atn_range
    (input:((num#num)#num)#((num#num)#num)) =
    (candle_q_atn_range_lower (FST input),
     candle_q_atn_range_upper (SND input))`;;

let candle_q_interval_atn_range_domain_def = new_definition
 `candle_q_interval_atn_range_domain
    (input:((num#num)#num)#((num#num)#num)) <=>
    candle_q_le (FST input) (SND input) /\
    candle_q_atn_range_domain (FST input) /\
    candle_q_atn_range_domain (SND input)`;;

let candle_atn_negative_reciprocal = prove
 (`!x. x < -- &1 ==> atn x = atn (--(inv x)) - pi / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `--x:real` ATN_INV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_NEG; ATN_NEG] THEN
  REAL_ARITH_TAC);;

let candle_atn_positive_reciprocal = prove
 (`!x. &1 < x ==> atn x = pi / &2 - atn (inv x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `x:real` ATN_INV) THEN
  ASM_REAL_ARITH_TAC);;

let candle_q_atn_range_argument_below = prove
 (`!x.
     candle_q_le x candle_q_atn_neg_one /\
     ~candle_q_le candle_q_atn_neg_one x
     ==> candle_q_nonzero x /\
         candle_q_real (candle_q_atn_range_argument x) =
           --(inv (candle_q_real x)) /\
         &0 <= candle_q_real (candle_q_atn_range_argument x) /\
         candle_q_real (candle_q_atn_range_argument x) < &1`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_atn_range_argument_def] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_le_real; candle_q_atn_neg_one_real]) THEN
  SUBGOAL_THEN `candle_q_nonzero x` ASSUME_TAC THENL
   [REWRITE_TAC[candle_q_nonzero_real] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN
     `candle_q_real (candle_q_inv x) = inv (candle_q_real x)`
      ASSUME_TAC THENL
     [ASM_MESON_TAC[candle_q_inv_real];
      ASM_REWRITE_TAC[candle_q_real_neg] THEN
      REWRITE_TAC[GSYM REAL_INV_NEG] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC]]]);;

let candle_q_atn_range_argument_above = prove
 (`!x.
     candle_q_le candle_q_atn_one x /\
     ~candle_q_le x candle_q_atn_one
     ==> candle_q_nonzero x /\
         candle_q_real (candle_q_atn_range_argument x) =
           inv (candle_q_real x) /\
         &0 <= candle_q_real (candle_q_atn_range_argument x) /\
         candle_q_real (candle_q_atn_range_argument x) < &1`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_atn_range_argument_def] THEN
  SUBGOAL_THEN `~candle_q_le x candle_q_atn_neg_one` ASSUME_TAC THENL
   [REWRITE_TAC[candle_q_le_real; candle_q_atn_neg_one_real] THEN
    RULE_ASSUM_TAC
      (REWRITE_RULE[candle_q_le_real; candle_q_atn_one_real]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_le_real; candle_q_atn_one_real]) THEN
  SUBGOAL_THEN `candle_q_nonzero x` ASSUME_TAC THENL
   [REWRITE_TAC[candle_q_nonzero_real] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN
      `candle_q_real (candle_q_inv x) = inv (candle_q_real x)`
      ASSUME_TAC THENL
     [ASM_MESON_TAC[candle_q_inv_real];
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC]]]);;

let candle_q_atn_range_bounds_sound = prove
 (`!x.
     candle_q_atn_range_domain x
     ==> candle_q_real (candle_q_atn_range_lower x) <=
           atn (candle_q_real x) /\
         atn (candle_q_real x) <=
           candle_q_real (candle_q_atn_range_upper x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_atn_range_domain_def;
              candle_q_atn_range_lower_def;
              candle_q_atn_range_upper_def] THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC (SPEC `x:(num#num)#num` candle_q_atn_range_argument_below) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
      `candle_q_real
         (candle_q_atn_lower (candle_q_atn_range_argument x)) <=
       atn (candle_q_real (candle_q_atn_range_argument x))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC candle_q_atn_lower_sound THEN
      REWRITE_TAC[candle_q_le_real; candle_q_atn_neg_one_real;
                  candle_q_atn_one_real] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
      `atn (candle_q_real (candle_q_atn_range_argument x)) <=
       candle_q_real
         (candle_q_atn_upper (candle_q_atn_range_argument x))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC candle_q_atn_upper_sound THEN
      REWRITE_TAC[candle_q_le_real; candle_q_atn_neg_one_real;
                  candle_q_atn_one_real] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC candle_q_atn_pi_half_interval_sound THEN
    REWRITE_TAC[candle_q_interval_contains_def] THEN STRIP_TAC THEN
    REWRITE_TAC[candle_q_real_add_normalized; candle_q_real_neg] THEN
    RULE_ASSUM_TAC
      (REWRITE_RULE[candle_q_le_real; candle_q_atn_neg_one_real]) THEN
    SUBGOAL_THEN
      `atn (candle_q_real x) =
       atn (candle_q_real (candle_q_atn_range_argument x)) - pi / &2`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `candle_q_real x < -- &1` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[candle_atn_negative_reciprocal]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    COND_CASES_TAC THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC (SPEC `x:(num#num)#num` candle_q_atn_range_argument_above) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN
        `candle_q_real
           (candle_q_atn_lower (candle_q_atn_range_argument x)) <=
         atn (candle_q_real (candle_q_atn_range_argument x))`
        ASSUME_TAC THENL
       [MATCH_MP_TAC candle_q_atn_lower_sound THEN
        REWRITE_TAC[candle_q_le_real; candle_q_atn_neg_one_real;
                    candle_q_atn_one_real] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
        `atn (candle_q_real (candle_q_atn_range_argument x)) <=
         candle_q_real
           (candle_q_atn_upper (candle_q_atn_range_argument x))`
        ASSUME_TAC THENL
       [MATCH_MP_TAC candle_q_atn_upper_sound THEN
        REWRITE_TAC[candle_q_le_real; candle_q_atn_neg_one_real;
                    candle_q_atn_one_real] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC candle_q_atn_pi_half_interval_sound THEN
      REWRITE_TAC[candle_q_interval_contains_def] THEN STRIP_TAC THEN
      REWRITE_TAC[candle_q_real_add_normalized; candle_q_real_neg] THEN
      RULE_ASSUM_TAC
        (REWRITE_RULE[candle_q_le_real; candle_q_atn_one_real]) THEN
      SUBGOAL_THEN
        `atn (candle_q_real x) =
         pi / &2 -
         atn (candle_q_real (candle_q_atn_range_argument x))`
        ASSUME_TAC THENL
       [SUBGOAL_THEN `&1 < candle_q_real x` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC;
          ASM_MESON_TAC[candle_atn_positive_reciprocal]];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[candle_q_atn_lower_sound;
                    candle_q_atn_upper_sound]]]);;

let candle_q_interval_atn_range_sound = prove
 (`!input:(((num#num)#num)#((num#num)#num)). !x.
     candle_q_interval_atn_range_domain input /\
     candle_q_interval_contains input x
     ==> candle_q_interval_contains
           (candle_q_interval_atn_range input) (atn x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_atn_range_domain_def;
              candle_q_interval_atn_range_def;
              candle_q_interval_contains_def; FST; SND] THEN
  STRIP_TAC THEN
  MP_TAC (SPEC `FST (input:(((num#num)#num)#((num#num)#num)))`
    candle_q_atn_range_bounds_sound) THEN
  MP_TAC (SPEC `SND (input:(((num#num)#num)#((num#num)#num)))`
    candle_q_atn_range_bounds_sound) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `atn (candle_q_real
      (FST (input:(((num#num)#num)#((num#num)#num)))))` THEN
    ASM_REWRITE_TAC[ATN_MONO_LE_EQ];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `atn (candle_q_real
      (SND (input:(((num#num)#num)#((num#num)#num)))))` THEN
    ASM_REWRITE_TAC[ATN_MONO_LE_EQ]]);;

(* Reflected evaluator. *)

let candle_cv_q_atn_pi_half_interval_def = new_definition
 `candle_cv_q_atn_pi_half_interval =
    candle_cv_q_interval candle_q_atn_pi_half_interval`;;

let candle_cv_q_atn_pi_half_interval_compute =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV[candle_q_atn_pi_half_interval_def;
                    candle_cv_q_interval_def; candle_cv_q_def;
                    candle_cv_lc_z_def; FST; SND]))
    candle_cv_q_atn_pi_half_interval_def;;

let candle_cv_q_atn_range_domain_def = new_definition
 `candle_cv_q_atn_range_domain x =
    Cexp_if (candle_cv_q_le x candle_cv_q_atn_neg_one)
      (Cexp_if (candle_cv_q_le candle_cv_q_atn_neg_one x)
        (Cexp_num 0) (Cexp_num 1))
      (Cexp_if (candle_cv_q_le candle_cv_q_atn_one x)
        (Cexp_if (candle_cv_q_le x candle_cv_q_atn_one)
          (Cexp_num 0) (Cexp_num 1))
        (Cexp_num 1))`;;

let candle_cv_q_atn_range_argument_def = new_definition
 `candle_cv_q_atn_range_argument x =
    Cexp_if (candle_cv_q_le x candle_cv_q_atn_neg_one)
      (candle_cv_q_neg (candle_cv_q_inv x))
      (Cexp_if (candle_cv_q_le candle_cv_q_atn_one x)
        (candle_cv_q_inv x) x)`;;

let candle_cv_q_atn_range_lower_def = new_definition
 `candle_cv_q_atn_range_lower x =
    Cexp_if (candle_cv_q_le x candle_cv_q_atn_neg_one)
      (candle_cv_q_add_normalized
        (candle_cv_q_atn_lower (candle_cv_q_atn_range_argument x))
        (candle_cv_q_neg (Cexp_snd candle_cv_q_atn_pi_half_interval)))
      (Cexp_if (candle_cv_q_le candle_cv_q_atn_one x)
        (candle_cv_q_add_normalized
          (Cexp_fst candle_cv_q_atn_pi_half_interval)
          (candle_cv_q_neg
            (candle_cv_q_atn_upper (candle_cv_q_atn_range_argument x))))
        (candle_cv_q_atn_lower x))`;;

let candle_cv_q_atn_range_upper_def = new_definition
 `candle_cv_q_atn_range_upper x =
    Cexp_if (candle_cv_q_le x candle_cv_q_atn_neg_one)
      (candle_cv_q_add_normalized
        (candle_cv_q_atn_upper (candle_cv_q_atn_range_argument x))
        (candle_cv_q_neg (Cexp_fst candle_cv_q_atn_pi_half_interval)))
      (Cexp_if (candle_cv_q_le candle_cv_q_atn_one x)
        (candle_cv_q_add_normalized
          (Cexp_snd candle_cv_q_atn_pi_half_interval)
          (candle_cv_q_neg
            (candle_cv_q_atn_lower (candle_cv_q_atn_range_argument x))))
        (candle_cv_q_atn_upper x))`;;

let candle_cv_q_interval_atn_range_def = new_definition
 `candle_cv_q_interval_atn_range input =
    Cexp_pair
      (candle_cv_q_atn_range_lower (Cexp_fst input))
      (candle_cv_q_atn_range_upper (Cexp_snd input))`;;

let candle_cv_q_interval_atn_range_domain_def = new_definition
 `candle_cv_q_interval_atn_range_domain input =
    Cexp_if (candle_cv_q_le (Cexp_fst input) (Cexp_snd input))
      (Cexp_if (candle_cv_q_atn_range_domain (Cexp_fst input))
        (candle_cv_q_atn_range_domain (Cexp_snd input))
        (Cexp_num 0))
      (Cexp_num 0)`;;

let candle_cv_q_atn_range_compute_eqs =
  union candle_cv_q_atn_series_compute_eqs
   (union candle_cv_q_inv_compute_eqs
     (map SPEC_ALL
       [candle_cv_q_atn_pi_half_interval_compute;
        candle_cv_q_atn_range_domain_def;
        candle_cv_q_atn_range_argument_def;
        candle_cv_q_atn_range_lower_def;
        candle_cv_q_atn_range_upper_def;
        candle_cv_q_interval_atn_range_def;
        candle_cv_q_interval_atn_range_domain_def]));;

let candle_cv_q_atn_range_domain_correct = prove
 (`!x.
     candle_cv_q_atn_range_domain (candle_cv_q x) =
     Cexp_num (if candle_q_atn_range_domain x then 1 else 0)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_atn_range_domain_def;
              candle_q_atn_range_domain_def;
              candle_cv_q_atn_neg_one_def; candle_cv_q_atn_one_def;
              candle_cv_q_le_correct] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]));;

let candle_cv_q_atn_range_argument_correct = prove
 (`!x.
     candle_cv_q_atn_range_argument (candle_cv_q x) =
     candle_cv_q (candle_q_atn_range_argument x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_atn_range_argument_def;
              candle_q_atn_range_argument_def;
              candle_cv_q_atn_neg_one_def; candle_cv_q_atn_one_def;
              candle_cv_q_le_correct] THEN
  REPEAT(COND_CASES_TAC THEN
    ASM_REWRITE_TAC[cexp_if_def; candle_cv_q_inv_correct;
                    candle_cv_q_neg_correct]));;

let candle_cv_q_atn_range_lower_correct = prove
 (`!x.
     candle_cv_q_atn_range_lower (candle_cv_q x) =
     candle_cv_q (candle_q_atn_range_lower x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_atn_range_lower_def;
              candle_q_atn_range_lower_def;
              candle_cv_q_atn_neg_one_def; candle_cv_q_atn_one_def;
              candle_cv_q_atn_pi_half_interval_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_le_correct] THEN
  REPEAT(COND_CASES_TAC THEN
    ASM_REWRITE_TAC[cexp_if_def; candle_cv_q_atn_range_argument_correct;
                    candle_cv_q_atn_lower_correct;
                    candle_cv_q_atn_upper_correct;
                    candle_cv_q_add_normalized_correct;
                    candle_cv_q_neg_correct]));;

let candle_cv_q_atn_range_upper_correct = prove
 (`!x.
     candle_cv_q_atn_range_upper (candle_cv_q x) =
     candle_cv_q (candle_q_atn_range_upper x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_atn_range_upper_def;
              candle_q_atn_range_upper_def;
              candle_cv_q_atn_neg_one_def; candle_cv_q_atn_one_def;
              candle_cv_q_atn_pi_half_interval_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_le_correct] THEN
  REPEAT(COND_CASES_TAC THEN
    ASM_REWRITE_TAC[cexp_if_def; candle_cv_q_atn_range_argument_correct;
                    candle_cv_q_atn_lower_correct;
                    candle_cv_q_atn_upper_correct;
                    candle_cv_q_add_normalized_correct;
                    candle_cv_q_neg_correct]));;

let candle_cv_q_interval_atn_range_correct = prove
 (`!input.
     candle_cv_q_interval_atn_range (candle_cv_q_interval input) =
     candle_cv_q_interval (candle_q_interval_atn_range input)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_atn_range_def;
              candle_q_interval_atn_range_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_atn_range_lower_correct;
              candle_cv_q_atn_range_upper_correct]);;

let candle_cv_q_atn_range_bool_and = prove
 (`!p q.
     Cexp_if (Cexp_num (if p then SUC 0 else 0))
       (Cexp_num (if q then SUC 0 else 0)) (Cexp_num 0) =
     Cexp_num (if p /\ q then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN
  BOOL_CASES_TAC `q:bool` THEN REWRITE_TAC[cexp_if_def]);;

let candle_cv_q_interval_atn_range_domain_correct = prove
 (`!input.
     candle_cv_q_interval_atn_range_domain
       (candle_cv_q_interval input) =
     Cexp_num
       (if candle_q_interval_atn_range_domain input then 1 else 0)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_atn_range_domain_def;
              candle_q_interval_atn_range_domain_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_le_correct;
              candle_cv_q_atn_range_domain_correct] THEN
  REWRITE_TAC[ONE; candle_cv_q_atn_range_bool_and; CONJ_ASSOC]);;
