(* ========================================================================== *)
(* Semantic boundary for the reflected centered Taylor-model interpreter.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The executable layer rounds every stored      *)
(* rational interval outward at a fixed decimal scale.  This file first      *)
(* establishes that boundary in ordinary HOL data; the analytic program      *)
(* soundness proof is built above these directed-rounding lemmas.             *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_compute.ml";;

module Candle_cv_analytic_expr_taylor_model_sound = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;

let candle_q_taylor_model_scale_def = new_definition
 `candle_q_taylor_model_scale = 1000000000000`;;

let candle_q_ceil_div_def = new_definition
 `candle_q_ceil_div numerator denominator =
    numerator DIV denominator +
    (if numerator MOD denominator = 0 then 0 else 1)`;;

let candle_q_ceil_div_step = prove
 (`!denominator numerator. ~(denominator = 0)
     ==> numerator <= candle_q_ceil_div numerator denominator * denominator`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`numerator:num`; `denominator:num`] DIVISION) THEN
  ASM_REWRITE_TAC[candle_q_ceil_div_def] THEN STRIP_TAC THEN
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

let candle_q_fixed_make_def = new_definition
 `candle_q_fixed_make positive negative =
    ((positive,negative),candle_q_taylor_model_scale - 1)`;;

let candle_q_fixed_round_lower_def = new_definition
 `candle_q_fixed_round_lower (q:(num#num)#num) =
    if FST (FST q) < SND (FST q) then
      candle_q_fixed_make 0
        (candle_q_ceil_div
          ((SND (FST q) - FST (FST q)) * candle_q_taylor_model_scale)
          (candle_q_den q))
    else
      candle_q_fixed_make
        (((FST (FST q) - SND (FST q)) * candle_q_taylor_model_scale)
          DIV candle_q_den q)
        0`;;

let candle_q_fixed_round_upper_def = new_definition
 `candle_q_fixed_round_upper (q:(num#num)#num) =
    if FST (FST q) < SND (FST q) then
      candle_q_fixed_make 0
        (((SND (FST q) - FST (FST q)) * candle_q_taylor_model_scale)
          DIV candle_q_den q)
    else
      candle_q_fixed_make
        (candle_q_ceil_div
          ((FST (FST q) - SND (FST q)) * candle_q_taylor_model_scale)
          (candle_q_den q))
        0`;;

let candle_cv_q_taylor_model_scale_correct = prove
 (`candle_cv_q_taylor_model_scale =
   Cexp_num candle_q_taylor_model_scale`,
  REWRITE_TAC[candle_cv_q_taylor_model_scale_def;
              candle_q_taylor_model_scale_def]);;

let candle_cv_q_ceil_div_correct = prove
 (`!numerator denominator.
     candle_cv_q_ceil_div
       (Cexp_num numerator) (Cexp_num denominator) =
     Cexp_num (candle_q_ceil_div numerator denominator)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_ceil_div_def; candle_q_ceil_div_def;
              cexp_div_def; cexp_mod_def; cexp_eq_def;
              injectivity "cval"] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_add_def; ADD_CLAUSES; ADD1]);;

let candle_cv_q_fixed_make_correct = prove
 (`!positive negative.
     candle_cv_q_fixed_make (Cexp_num positive) (Cexp_num negative) =
     candle_cv_q (candle_q_fixed_make positive negative)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_fixed_make_def; candle_q_fixed_make_def;
              candle_cv_q_def; candle_cv_lc_z_def;
              candle_cv_q_taylor_model_scale_correct;
              candle_q_taylor_model_scale_def; cexp_sub_def; FST; SND]);;

let candle_cv_q_fixed_round_lower_correct = prove
 (`!q.
     candle_cv_q_fixed_round_lower (candle_cv_q q) =
     candle_cv_q (candle_q_fixed_round_lower q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_fixed_round_lower_def;
              candle_q_fixed_round_lower_def;
              candle_cv_q_def; candle_cv_lc_z_def;
              cexp_fst_def; cexp_snd_def; cexp_less_def;
              cexp_sub_def; cexp_mul_def; cexp_div_def;
              candle_cv_q_taylor_model_scale_correct;
              candle_cv_q_den_correct; candle_cv_q_ceil_div_correct;
              candle_cv_q_fixed_make_correct; FST; SND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]);;

let candle_cv_q_fixed_round_upper_correct = prove
 (`!q.
     candle_cv_q_fixed_round_upper (candle_cv_q q) =
     candle_cv_q (candle_q_fixed_round_upper q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_fixed_round_upper_def;
              candle_q_fixed_round_upper_def;
              candle_cv_q_def; candle_cv_lc_z_def;
              cexp_fst_def; cexp_snd_def; cexp_less_def;
              cexp_sub_def; cexp_mul_def; cexp_div_def;
              candle_cv_q_taylor_model_scale_correct;
              candle_cv_q_den_correct; candle_cv_q_ceil_div_correct;
              candle_cv_q_fixed_make_correct; FST; SND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]);;

(* -------------------------------------------------------------------------- *)
(* Ordinary-HOL semantics of the fixed-scale outward rounding boundary.      *)
(* -------------------------------------------------------------------------- *)

let candle_q_fixed_make_real = prove
 (`!positive negative.
     candle_q_real (candle_q_fixed_make positive negative) =
     (&positive - &negative) / &candle_q_taylor_model_scale`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_real_def; candle_q_fixed_make_def;
              candle_q_den_def; candle_lc_zreal_def;
              candle_q_taylor_model_scale_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_scaled_floor_le = prove
 (`!numerator denominator. ~(denominator = 0)
     ==> &((numerator * candle_q_taylor_model_scale) DIV denominator) /
         &candle_q_taylor_model_scale <=
         &numerator / &denominator`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < candle_q_taylor_model_scale` ASSUME_TAC THENL
   [REWRITE_TAC[candle_q_taylor_model_scale_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < denominator` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[candle_real_div_le_div; REAL_OF_NUM_LT] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MP_TAC
    (SPECL
      [`numerator * candle_q_taylor_model_scale`; `denominator:num`]
      DIV_MUL_LE) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL]);;

let candle_q_scaled_le_ceil = prove
 (`!numerator denominator. ~(denominator = 0)
     ==> &numerator / &denominator <=
         &(candle_q_ceil_div
             (numerator * candle_q_taylor_model_scale) denominator) /
         &candle_q_taylor_model_scale`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < candle_q_taylor_model_scale` ASSUME_TAC THENL
   [REWRITE_TAC[candle_q_taylor_model_scale_def] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < denominator` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[candle_real_div_le_div; REAL_OF_NUM_LT] THEN
  MP_TAC
    (SPECL
      [`denominator:num`;
       `numerator * candle_q_taylor_model_scale`]
      candle_q_ceil_div_step) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL]);;

let candle_q_fixed_round_lower_sound_components = prove
 (`!ppos nneg ddpre.
     candle_q_real
       (candle_q_fixed_round_lower
         ((ppos,nneg),ddpre)) <=
     candle_q_real ((ppos,nneg),ddpre)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_fixed_round_lower_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[candle_q_fixed_make_real; candle_q_real_def;
              candle_lc_zreal_def; candle_q_den_def; FST; SND] THENL
   [MP_TAC
      (SPECL
        [`(nneg:num) - ppos`; `SUC (ddpre:num)`]
        candle_q_scaled_le_ceil) THEN
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
        candle_q_scaled_floor_le) THEN
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

let candle_q_fixed_round_upper_sound_components = prove
 (`!ppos nneg ddpre.
     candle_q_real ((ppos,nneg),ddpre) <=
     candle_q_real
       (candle_q_fixed_round_upper
         ((ppos,nneg),ddpre))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_fixed_round_upper_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[candle_q_fixed_make_real; candle_q_real_def;
              candle_lc_zreal_def; candle_q_den_def; FST; SND] THENL
   [MP_TAC
      (SPECL
        [`(nneg:num) - ppos`; `SUC (ddpre:num)`]
        candle_q_scaled_floor_le) THEN
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
        candle_q_scaled_le_ceil) THEN
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

let candle_q_fixed_round_lower_sound = prove
 (`!q:(num#num)#num.
     candle_q_real (candle_q_fixed_round_lower q) <= candle_q_real q`,
  REWRITE_TAC[FORALL_PAIR_THM; candle_q_fixed_round_lower_sound_components]);;

let candle_q_fixed_round_upper_sound = prove
 (`!q:(num#num)#num.
     candle_q_real q <= candle_q_real (candle_q_fixed_round_upper q)`,
  REWRITE_TAC[FORALL_PAIR_THM; candle_q_fixed_round_upper_sound_components]);;

(* -------------------------------------------------------------------------- *)
(* Lift the scalar boundary to the interval/list/matrix representations used *)
(* by the centered model.                                                     *)
(* -------------------------------------------------------------------------- *)

let candle_q_fixed_interval_round_def = new_definition
 `candle_q_fixed_interval_round
    (i:((num#num)#num)#((num#num)#num)) =
    (candle_q_fixed_round_lower (FST i),
     candle_q_fixed_round_upper (SND i))`;;

let candle_q_fixed_interval_list_round_def = new_recursive_definition list_RECURSION
 `(candle_q_fixed_interval_list_round [] = []) /\
  (candle_q_fixed_interval_list_round (CONS h t) =
     CONS (candle_q_fixed_interval_round h)
       (candle_q_fixed_interval_list_round t))`;;

let candle_q_fixed_interval_matrix_round_def = new_recursive_definition list_RECURSION
 `(candle_q_fixed_interval_matrix_round [] = []) /\
  (candle_q_fixed_interval_matrix_round (CONS h t) =
     CONS (candle_q_fixed_interval_list_round h)
       (candle_q_fixed_interval_matrix_round t))`;;

let candle_cv_q_fixed_interval_round_correct = prove
 (`!i.
     candle_cv_q_fixed_interval_round (candle_cv_q_interval i) =
     candle_cv_q_interval (candle_q_fixed_interval_round i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_fixed_interval_round_def;
              candle_q_fixed_interval_round_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_fixed_round_lower_correct;
              candle_cv_q_fixed_round_upper_correct; FST; SND]);;

let candle_cv_q_fixed_interval_list_round_correct = prove
 (`!items.
     candle_cv_q_fixed_interval_list_round
       (candle_cv_q_interval_list items) =
     candle_cv_q_interval_list
       (candle_q_fixed_interval_list_round items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_fixed_interval_list_round_def;
                  candle_cv_q_interval_list_def;
                  candle_q_fixed_interval_list_round_def;
                  candle_cv_q_fixed_interval_round_correct]);;

let candle_cv_q_fixed_interval_matrix_round_correct = prove
 (`!rows.
     candle_cv_q_fixed_interval_matrix_round
       (candle_cv_q_interval_matrix rows) =
     candle_cv_q_interval_matrix
       (candle_q_fixed_interval_matrix_round rows)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_fixed_interval_matrix_round_def;
                  candle_cv_q_interval_matrix_def;
                  candle_q_fixed_interval_matrix_round_def;
                  candle_cv_q_fixed_interval_list_round_correct]);;

let candle_q_fixed_interval_round_contains = prove
 (`!i x. candle_q_interval_contains i x
         ==> candle_q_interval_contains
               (candle_q_fixed_interval_round i) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_q_fixed_interval_round_def; FST; SND] THEN
  MESON_TAC[candle_q_fixed_round_lower_sound;
            candle_q_fixed_round_upper_sound; REAL_LE_TRANS]);;

let candle_q_fixed_interval_list_round_contains = prove
 (`!items values.
     candle_q_stack_contains items values
     ==> candle_q_stack_contains
           (candle_q_fixed_interval_list_round items) values`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_q_fixed_interval_list_round_def;
                candle_q_stack_contains_def];
    GEN_TAC THEN
    MP_TAC(ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_q_fixed_interval_list_round_def;
                    candle_q_stack_contains_def] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_fixed_interval_round_contains THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC
        (SPEC `t':real list`
          (ASSUME
            `!values.
               candle_q_stack_contains t values
               ==> candle_q_stack_contains
                     (candle_q_fixed_interval_list_round t) values`)) THEN
      ASM_REWRITE_TAC[]]]);;

let candle_q_fixed_interval_matrix_round_contains = prove
 (`!rows values.
     ALL2 candle_q_stack_contains rows values
     ==> ALL2 candle_q_stack_contains
           (candle_q_fixed_interval_matrix_round rows) values`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC
      (ISPEC
        `values:(real list)list`
        list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_q_fixed_interval_matrix_round_def; ALL2];
    GEN_TAC THEN
    MP_TAC
      (ISPEC
        `values:(real list)list`
        list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_q_fixed_interval_matrix_round_def; ALL2] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_fixed_interval_list_round_contains THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC
        (SPEC `t':(real list)list`
          (ASSUME
            `!values.
               ALL2 candle_q_stack_contains t values
               ==> ALL2 candle_q_stack_contains
                     (candle_q_fixed_interval_matrix_round t) values`)) THEN
      ASM_REWRITE_TAC[]]]);;

end;;
