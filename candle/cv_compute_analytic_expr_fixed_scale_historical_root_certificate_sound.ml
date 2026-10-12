(* ========================================================================== *)
(* Historical supplied roots: exact square-bound certificate soundness.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_root_certificate_sound = struct

open Candle_cv_analytic_expr_fixed_scale_sound;;

(* All endpoints used by the historical fixed-scale evaluator are canonical
   nonnegative integers over [candle_fs_scale].  These two exact integer
   inequalities authenticate an externally prepared positive square-root
   enclosure; no floating-point preparation is trusted. *)

let candle_fs_hist_root_certificate_sound = prove
 (`!input_lower input_upper root_lower root_upper x.
     candle_fs_interval_contains
       ((input_lower,0),(input_upper,0)) x /\
     0 < input_lower /\ input_lower <= input_upper /\
     0 < root_lower /\ root_lower <= root_upper /\
     root_lower * root_lower <= input_lower * candle_fs_scale /\
     input_upper * candle_fs_scale <= root_upper * root_upper
     ==> candle_fs_interval_contains
       ((root_lower,0),(root_upper,0)) (sqrt x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
   (REWRITE_RULE[candle_fs_interval_contains_def;
                 candle_fs_real_def; candle_lc_zreal_def;
                 FST; SND; REAL_SUB_RZERO]) THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_real_def; candle_lc_zreal_def;
              FST; SND; REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `&0 < &(candle_fs_scale)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT; candle_fs_scale_pos];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&(candle_fs_scale) = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&root_lower * &root_lower <=
    &input_lower * &candle_fs_scale`
  ASSUME_TAC THENL
   [MP_TAC
     (ASSUME
       `root_lower * root_lower <= input_lower * candle_fs_scale`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&input_upper * &candle_fs_scale <=
    &root_upper * &root_upper`
  ASSUME_TAC THENL
   [MP_TAC
     (ASSUME
       `input_upper * candle_fs_scale <= root_upper * root_upper`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&root_lower / &candle_fs_scale) pow 2 <=
    &input_lower / &candle_fs_scale`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&input_lower / &candle_fs_scale =
      (&input_lower * &candle_fs_scale) /
      (&candle_fs_scale pow 2)`
    SUBST1_TAC THENL
     [MP_TAC (ASSUME `~(&(candle_fs_scale) = &0)`) THEN
      CONV_TAC REAL_FIELD;
      REWRITE_TAC[REAL_POW_DIV] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT] THEN
      ASM_REWRITE_TAC[REAL_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&input_upper / &candle_fs_scale <=
    (&root_upper / &candle_fs_scale) pow 2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&input_upper / &candle_fs_scale =
      (&input_upper * &candle_fs_scale) /
      (&candle_fs_scale pow 2)`
    SUBST1_TAC THENL
     [MP_TAC (ASSUME `~(&(candle_fs_scale) = &0)`) THEN
      CONV_TAC REAL_FIELD;
      REWRITE_TAC[REAL_POW_DIV] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT] THEN
      ASM_REWRITE_TAC[REAL_POW_2]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&input_lower / &candle_fs_scale` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&input_upper / &candle_fs_scale` THEN
      ASM_REWRITE_TAC[]]]);;

end;;
