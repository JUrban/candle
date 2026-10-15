(* ========================================================================== *)
(* Soundness of the bounded fixed-scale Taylor handoff.                      *)
(*                                                                            *)
(* This file gives ordinary-HOL meanings to the compact 10^-12 integer       *)
(* boundary used after exact analytic-jet execution.  The scalar lemmas are  *)
(* the base for the reusable gradient/Hessian and final-verdict theorem.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_taylor_handoff_compute.ml";;

module Candle_cv_analytic_expr_fixed_scale_taylor_handoff_sound = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_analytic_expr_fixed_scale_taylor_handoff_compute;;

let candle_matan_fs_scale_def = new_definition
 `candle_matan_fs_scale = 1000000000000`;;

let candle_matan_fs_real_def = new_definition
 `candle_matan_fs_real (z:num#num) =
    candle_lc_zreal z / &candle_matan_fs_scale`;;

let candle_matan_fs_ceil_div_def = new_definition
 `candle_matan_fs_ceil_div numerator denominator =
    numerator DIV denominator +
    (if numerator MOD denominator = 0 then 0 else 1)`;;

let candle_matan_fs_q_upper_def = new_definition
 `candle_matan_fs_q_upper (q:(num#num)#num) =
    if FST (FST q) < SND (FST q) then
      (0,
       ((SND (FST q) - FST (FST q)) * candle_matan_fs_scale) DIV
       candle_q_den q)
    else
      (candle_matan_fs_ceil_div
        ((FST (FST q) - SND (FST q)) * candle_matan_fs_scale)
        (candle_q_den q),
       0)`;;

let candle_matan_fs_q_abs_upper_def = new_definition
 `candle_matan_fs_q_abs_upper (q:(num#num)#num) =
    candle_matan_fs_ceil_div
      ((if FST (FST q) < SND (FST q)
        then SND (FST q) - FST (FST q)
        else FST (FST q) - SND (FST q)) * candle_matan_fs_scale)
      (candle_q_den q)`;;

let candle_matan_fs_weighted_rows_upper_def = define
 `(candle_matan_fs_weighted_rows_upper radii [] row_lists = 0) /\
  (candle_matan_fs_weighted_rows_upper radii (CONS weight weights) [] = 0) /\
  (candle_matan_fs_weighted_rows_upper radii (CONS weight weights)
      (CONS interval_row row_tail) =
     candle_matan_fs_q_abs_upper
       (candle_q_mul weight
         (candle_q_dot_abs_upper radii interval_row)) +
     candle_matan_fs_weighted_rows_upper radii weights row_tail)`;;

let candle_matan_fs_taylor_accept_def = new_definition
 `candle_matan_fs_taylor_accept value gradient radii weights row_lists <=>
    FST (candle_matan_fs_q_upper value) +
      candle_matan_fs_q_abs_upper gradient +
      candle_matan_fs_ceil_div
        (candle_matan_fs_weighted_rows_upper radii weights row_lists) 2 <
    SND (candle_matan_fs_q_upper value)`;;

let candle_cv_matan_fs_scale_correct = prove
 (`candle_cv_matan_fs_scale = Cexp_num candle_matan_fs_scale`,
  REWRITE_TAC[candle_cv_matan_fs_scale_def;
              candle_matan_fs_scale_def]);;
let _ = marker "sound-scale-correct";;

let candle_cv_matan_fs_ceil_div_correct = prove
 (`!numerator denominator.
     candle_cv_matan_fs_ceil_div
       (Cexp_num numerator) (Cexp_num denominator) =
     Cexp_num (candle_matan_fs_ceil_div numerator denominator)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_matan_fs_ceil_div_def;
              candle_matan_fs_ceil_div_def;
              cexp_div_def; cexp_mod_def; cexp_eq_def;
              injectivity "cval"] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_add_def; ADD_CLAUSES; ADD1]);;
let _ = marker "sound-ceil-div-correct";;

let candle_cv_matan_fs_q_upper_correct = prove
 (`!q.
     candle_cv_matan_fs_q_upper (candle_cv_q q) =
     candle_cv_lc_z (candle_matan_fs_q_upper q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_matan_fs_q_upper_def;
              candle_matan_fs_q_upper_def;
              candle_cv_q_def; candle_cv_lc_z_def;
              candle_cv_matan_fs_q_den_def;
              candle_q_den_def;
              candle_cv_matan_fs_scale_correct;
              candle_cv_matan_fs_ceil_div_correct;
              cexp_fst_def; cexp_snd_def; cexp_less_def;
              cexp_sub_def; cexp_mul_def; cexp_div_def;
              cexp_add_def; FST; SND] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_mul_def;
                  candle_cv_matan_fs_ceil_div_correct; ADD1]);;
let _ = marker "sound-q-upper-correct";;

let candle_cv_matan_fs_q_abs_upper_correct = prove
 (`!q.
     candle_cv_matan_fs_q_abs_upper (candle_cv_q q) =
     Cexp_num (candle_matan_fs_q_abs_upper q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_matan_fs_q_abs_upper_def;
              candle_matan_fs_q_abs_upper_def;
              candle_cv_q_def; candle_cv_lc_z_def;
              candle_cv_matan_fs_q_den_def;
              candle_q_den_def;
              candle_cv_matan_fs_scale_correct;
              candle_cv_matan_fs_ceil_div_correct;
              cexp_fst_def; cexp_snd_def; cexp_less_def;
              cexp_sub_def; cexp_mul_def; cexp_add_def; FST; SND] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_mul_def;
                  candle_cv_matan_fs_ceil_div_correct; ADD1]);;
let _ = marker "sound-q-abs-upper-correct";;

let candle_cv_matan_fs_weighted_rows_upper_correct = prove
 (`!radii weights row_lists.
     candle_cv_matan_fs_weighted_rows_upper
       (candle_cv_q_list radii) (candle_cv_q_list weights)
       (candle_cv_q_interval_matrix row_lists) =
     Cexp_num
       (candle_matan_fs_weighted_rows_upper radii weights row_lists)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_list_def;
                candle_cv_matan_fs_weighted_rows_upper_def;
                candle_matan_fs_weighted_rows_upper_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_q_list_def;
                    candle_cv_q_interval_matrix_def;
                    candle_cv_matan_fs_weighted_rows_upper_def;
                    candle_matan_fs_weighted_rows_upper_def;
                    candle_cv_q_dot_abs_upper_correct;
                    candle_cv_q_mul_correct;
                    candle_cv_matan_fs_q_abs_upper_correct;
                    cexp_add_def]]);;
let _ = marker "sound-weighted-rows-correct";;

let candle_matan_fs_scale_pos = prove
 (`0 < candle_matan_fs_scale`,
  REWRITE_TAC[candle_matan_fs_scale_def] THEN ARITH_TAC);;
let _ = marker "sound-scale-pos";;

let candle_matan_fs_ceil_div_step = prove
 (`!denominator numerator. ~(denominator = 0)
     ==> numerator <=
         candle_matan_fs_ceil_div numerator denominator * denominator`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`numerator:num`; `denominator:num`] DIVISION) THEN
  ASM_REWRITE_TAC[candle_matan_fs_ceil_div_def] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV
      [ASSUME
        `numerator = numerator DIV denominator * denominator +
         numerator MOD denominator`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL];
    GEN_REWRITE_TAC LAND_CONV
      [ASSUME
        `numerator = numerator DIV denominator * denominator +
         numerator MOD denominator`] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES; LE_ADD_LCANCEL] THEN
    ASM_MESON_TAC[LT_IMP_LE]]);;
let _ = marker "sound-ceil-div-step";;

let candle_matan_fs_scaled_floor_le = prove
 (`!numerator denominator. ~(denominator = 0)
     ==> &((numerator * candle_matan_fs_scale) DIV denominator) /
         &candle_matan_fs_scale <=
         &numerator / &denominator`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < candle_matan_fs_scale` ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC candle_matan_fs_scale_pos; ALL_TAC] THEN
  SUBGOAL_THEN `0 < denominator` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[candle_real_div_le_div; REAL_OF_NUM_LT] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MP_TAC
    (SPECL
      [`numerator * candle_matan_fs_scale`; `denominator:num`]
      DIV_MUL_LE) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL]);;
let _ = marker "sound-scaled-floor-le";;

let candle_matan_fs_scaled_le_ceil = prove
 (`!numerator denominator. ~(denominator = 0)
     ==> &numerator / &denominator <=
         &(candle_matan_fs_ceil_div
             (numerator * candle_matan_fs_scale) denominator) /
         &candle_matan_fs_scale`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < candle_matan_fs_scale` ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC candle_matan_fs_scale_pos; ALL_TAC] THEN
  SUBGOAL_THEN `0 < denominator` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[candle_real_div_le_div; REAL_OF_NUM_LT] THEN
  MP_TAC
    (SPECL
      [`denominator:num`; `numerator * candle_matan_fs_scale`]
      candle_matan_fs_ceil_div_step) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL]);;
let _ = marker "sound-scaled-le-ceil";;

let candle_matan_fs_q_upper_sound_components = prove
 (`!ppos nneg ddpre.
     candle_q_real ((ppos,nneg),ddpre) <=
     candle_matan_fs_real
       (candle_matan_fs_q_upper ((ppos,nneg),ddpre))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_matan_fs_q_upper_def;
              candle_matan_fs_real_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[candle_q_real_def; candle_lc_zreal_def;
              candle_q_den_def; FST; SND] THENL
   [MP_TAC
      (SPECL
        [`(nneg:num) - ppos`; `SUC (ddpre:num)`]
        candle_matan_fs_scaled_floor_le) THEN
    REWRITE_TAC[NOT_SUC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[real_div] th)) THEN
    SUBGOAL_THEN `(ppos:num) <= nneg` ASSUME_TAC THENL
     [MATCH_MP_TAC (ARITH_RULE `(ppos:num) < nneg ==> ppos <= nneg`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&ppos - &nneg = --(&(nneg - ppos))`
      SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_SUB_LZERO; real_div;
                      GSYM REAL_NEG_LMUL; REAL_LE_NEG2]];
    MP_TAC
      (SPECL
        [`(ppos:num) - nneg`; `SUC (ddpre:num)`]
        candle_matan_fs_scaled_le_ceil) THEN
    REWRITE_TAC[NOT_SUC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(nneg:num) <= ppos` ASSUME_TAC THENL
     [MATCH_MP_TAC (ARITH_RULE `~((ppos:num) < nneg) ==> nneg <= ppos`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `&ppos - &nneg = &(ppos - nneg)`
      SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB];
      ASM_REWRITE_TAC[REAL_SUB_RZERO]]]);;
let _ = marker "sound-q-upper-components";;

let candle_matan_fs_q_upper_sound = prove
 (`!q:(num#num)#num.
     candle_q_real q <=
     candle_matan_fs_real (candle_matan_fs_q_upper q)`,
  REWRITE_TAC[FORALL_PAIR_THM;
              candle_matan_fs_q_upper_sound_components]);;
let _ = marker "sound-q-upper";;

let candle_matan_fs_q_abs_upper_sound_components = prove
 (`!ppos nneg ddpre.
     abs (candle_q_real ((ppos,nneg),ddpre)) <=
     &(candle_matan_fs_q_abs_upper ((ppos,nneg),ddpre)) /
     &candle_matan_fs_scale`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_matan_fs_q_abs_upper_def;
              candle_q_real_def; candle_lc_zreal_def;
              candle_q_den_def; FST; SND] THEN
  COND_CASES_TAC THENL
   [MP_TAC
      (SPECL
        [`(nneg:num) - ppos`; `SUC (ddpre:num)`]
        candle_matan_fs_scaled_le_ceil) THEN
    REWRITE_TAC[NOT_SUC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(ppos:num) <= nneg` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
      `abs ((&ppos - &nneg) / &(SUC ddpre)) =
       &(nneg - ppos) / &(SUC ddpre)`
      SUBST1_TAC THENL
     [SUBGOAL_THEN
        `&ppos - &nneg = --(&(nneg - ppos))`
        SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NEG; REAL_ABS_NUM]];
      ASM_REWRITE_TAC[]];
    MP_TAC
      (SPECL
        [`(ppos:num) - nneg`; `SUC (ddpre:num)`]
        candle_matan_fs_scaled_le_ceil) THEN
    REWRITE_TAC[NOT_SUC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(nneg:num) <= ppos` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
      `abs ((&ppos - &nneg) / &(SUC ddpre)) =
       &(ppos - nneg) / &(SUC ddpre)`
      SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB; REAL_ABS_DIV; REAL_ABS_NUM];
      ASM_REWRITE_TAC[]]]);;
let _ = marker "sound-q-abs-upper-components";;

let candle_matan_fs_q_abs_upper_sound = prove
 (`!q:(num#num)#num.
     abs (candle_q_real q) <=
     &(candle_matan_fs_q_abs_upper q) / &candle_matan_fs_scale`,
  REWRITE_TAC[FORALL_PAIR_THM;
              candle_matan_fs_q_abs_upper_sound_components]);;
let _ = marker "sound-q-abs-upper";;

let candle_real_le_abs = prove
 (`!x:real. x <= abs x`,
  GEN_TAC THEN
  MP_TAC (SPECL [`x:real`; `abs x`] REAL_ABS_BOUNDS) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN MESON_TAC[]);;

let candle_matan_fs_weighted_rows_upper_sound = prove
 (`!radii weights row_lists.
     candle_q_real
       (candle_q_weighted_rows_abs_upper radii weights row_lists) <=
     &(candle_matan_fs_weighted_rows_upper radii weights row_lists) /
     &candle_matan_fs_scale`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_weighted_rows_abs_upper_def;
                candle_matan_fs_weighted_rows_upper_def;
                candle_q_dim_real_zero; real_div; REAL_MUL_LZERO;
                REAL_LE_REFL];
    POP_ASSUM (LABEL_TAC "weights_ih") THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_q_weighted_rows_abs_upper_def;
                    candle_matan_fs_weighted_rows_upper_def;
                    candle_q_dim_real_zero; real_div; REAL_MUL_LZERO;
                    REAL_LE_REFL] THEN
    SUBGOAL_THEN
     `candle_q_real
        (candle_q_mul h (candle_q_dot_abs_upper radii h')) <=
      &(candle_matan_fs_q_abs_upper
          (candle_q_mul h (candle_q_dot_abs_upper radii h'))) /
      &candle_matan_fs_scale`
     ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `abs
         (candle_q_real
           (candle_q_mul h (candle_q_dot_abs_upper radii h')))` THEN
      REWRITE_TAC[candle_real_le_abs] THEN
      MATCH_ACCEPT_TAC candle_matan_fs_q_abs_upper_sound;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_q_real
        (candle_q_weighted_rows_abs_upper radii t t') <=
      &(candle_matan_fs_weighted_rows_upper radii t t') /
      &candle_matan_fs_scale`
     ASSUME_TAC THENL
     [USE_THEN "weights_ih" MATCH_ACCEPT_TAC;
      REWRITE_TAC[candle_q_real_add; GSYM REAL_OF_NUM_ADD; real_div;
                  REAL_ADD_RDISTRIB] THEN
      ASM_REAL_ARITH_TAC]]);;
let _ = marker "sound-weighted-rows";;

let candle_matan_fs_half_ceil_sound = prove
 (`!numerator.
     &numerator / &candle_matan_fs_scale / &2 <=
     &(candle_matan_fs_ceil_div numerator 2) /
     &candle_matan_fs_scale`,
  GEN_TAC THEN
  SUBGOAL_THEN `&0 < &(candle_matan_fs_scale)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; candle_matan_fs_scale_pos];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&numerator / &candle_matan_fs_scale / &2 =
    (&numerator / &2) / &candle_matan_fs_scale`
   SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  SUBGOAL_THEN `(&0:real) < &2` ASSUME_TAC THENL
   [REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MP_TAC
    (SPECL [`2`; `numerator:num`] candle_matan_fs_ceil_div_step) THEN
  REWRITE_TAC[ARITH_RULE `~(2 = 0)`;
              GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL] THEN
  REAL_ARITH_TAC);;
let _ = marker "sound-half-ceil";;

let candle_matan_fs_integer_cast_negative = prove
 (`!positive negative gradient hessian.
     positive + gradient + hessian < negative
     ==>
     &positive + &gradient + &hessian < &negative`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD]);;
let _ = marker "sound-integer-cast-negative";;

let candle_matan_fs_integer_negative = prove
 (`!positive negative gradient hessian.
     positive + gradient + hessian < negative
     ==>
     (&positive - &negative) / &candle_matan_fs_scale +
       &gradient / &candle_matan_fs_scale +
       &hessian / &candle_matan_fs_scale < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(candle_matan_fs_scale)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; candle_matan_fs_scale_pos];
    ALL_TAC] THEN
  MP_TAC
    (SPECL
      [`positive:num`; `negative:num`; `gradient:num`; `hessian:num`]
      candle_matan_fs_integer_cast_negative) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(&positive - &negative) / &candle_matan_fs_scale +
      &gradient / &candle_matan_fs_scale +
      &hessian / &candle_matan_fs_scale =
    (&positive + &gradient + &hessian - &negative) /
      &candle_matan_fs_scale`
   SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO] THEN
  ASM_REAL_ARITH_TAC);;
let _ = marker "sound-integer-negative";;

let candle_matan_fs_taylor_accept_sound = prove
 (`!value gradient radii weights row_lists.
     candle_matan_fs_taylor_accept
       value gradient radii weights row_lists
     ==>
     candle_q_real value + candle_q_real gradient +
       candle_q_real
         (candle_q_weighted_rows_abs_upper radii weights row_lists) / &2 <
     &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_matan_fs_taylor_accept_def] THEN DISCH_TAC THEN
  ABBREV_TAC `value_bound = candle_matan_fs_q_upper value` THEN
  ABBREV_TAC `gradient_bound = candle_matan_fs_q_abs_upper gradient` THEN
  ABBREV_TAC
   `row_bound =
      candle_matan_fs_weighted_rows_upper radii weights row_lists` THEN
  ABBREV_TAC
   `hessian_bound = candle_matan_fs_ceil_div row_bound 2` THEN
  SUBGOAL_THEN
   `candle_q_real value <=
    (&(FST value_bound) - &(SND value_bound)) /
      &candle_matan_fs_scale`
   ASSUME_TAC THENL
   [MP_TAC (SPEC `value:(num#num)#num` candle_matan_fs_q_upper_sound) THEN
    EXPAND_TAC "value_bound" THEN
    REWRITE_TAC[candle_matan_fs_real_def; candle_lc_zreal_def];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_real gradient <=
    &gradient_bound / &candle_matan_fs_scale`
   ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs (candle_q_real gradient)` THEN
    REWRITE_TAC[candle_real_le_abs] THEN
    EXPAND_TAC "gradient_bound" THEN
    MATCH_ACCEPT_TAC candle_matan_fs_q_abs_upper_sound;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_real
      (candle_q_weighted_rows_abs_upper radii weights row_lists) / &2 <=
    &hessian_bound / &candle_matan_fs_scale`
   ASSUME_TAC THENL
   [SUBGOAL_THEN
     `candle_q_real
        (candle_q_weighted_rows_abs_upper radii weights row_lists) <=
      &row_bound / &candle_matan_fs_scale`
     ASSUME_TAC THENL
     [EXPAND_TAC "row_bound" THEN
      MATCH_ACCEPT_TAC candle_matan_fs_weighted_rows_upper_sound;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&row_bound / &candle_matan_fs_scale / &2 <=
      &hessian_bound / &candle_matan_fs_scale`
     ASSUME_TAC THENL
     [EXPAND_TAC "hessian_bound" THEN
      MATCH_ACCEPT_TAC candle_matan_fs_half_ceil_sound;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC
    (SPECL
      [`FST (value_bound:num#num)`;
       `SND (value_bound:num#num)`;
       `gradient_bound:num`;
       `hessian_bound:num`]
      candle_matan_fs_integer_negative) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REAL_ARITH_TAC);;
let _ = marker "sound-taylor-accept";;

end;;
