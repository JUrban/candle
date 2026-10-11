(* ========================================================================== *)
(* Analytic jet factorization for the historical dihedral square roots.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_analytic_bridge_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sqrt_factorization_sound = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_analytic_bridge_sound;;

(* Bounds carried by a sqrt node constrain the checked interval execution but
   do not alter the denoted value or either formal derivative layer.  A
   canonical node keeps the algebraic factorization theorem independent of
   particular certificate bounds. *)

let candle_hist_analytic_sqrt_def = new_definition
 `candle_hist_analytic_sqrt expression =
    Candle_analytic_sqrt 0 0 0 0 0 0 expression`;;

let candle_hist_analytic_sqrt_bounds_irrelevant = prove
 (`!env lp ln ld up un ud (expression:candle_analytic_expr).
     candle_hist_analytic_real_jet env
       (Candle_analytic_sqrt lp ln ld up un ud expression) =
     candle_hist_analytic_real_jet env
       (candle_hist_analytic_sqrt expression)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_analytic_real_jet_def;
              candle_hist_analytic_sqrt_def;
              candle_hist_real_jet_make_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def]);;

let candle_hist_analytic_sqrt_mul_value = prove
 (`!env (left_expression:candle_analytic_expr) right_expression.
     candle_analytic_value env
       (Candle_analytic_mul
         (candle_hist_analytic_sqrt left_expression)
         (candle_hist_analytic_sqrt right_expression)) =
     candle_analytic_value env
       (candle_hist_analytic_sqrt
         (Candle_analytic_mul left_expression right_expression))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_analytic_sqrt_def;
              candle_analytic_value_def; SQRT_MUL]);;

let candle_hist_analytic_sqrt_mul_d = prove
 (`!env (left_expression:candle_analytic_expr) right_expression coordinate.
     &0 < candle_analytic_value env left_expression /\
     &0 < candle_analytic_value env right_expression
     ==> candle_analytic_d coordinate env
           (Candle_analytic_mul
             (candle_hist_analytic_sqrt left_expression)
             (candle_hist_analytic_sqrt right_expression)) =
         candle_analytic_d coordinate env
           (candle_hist_analytic_sqrt
             (Candle_analytic_mul left_expression right_expression))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~(candle_analytic_value env left_expression = &0)`
  (LABEL_TAC "left_nonzero") THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(candle_analytic_value env right_expression = &0)`
  (LABEL_TAC "right_nonzero") THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(sqrt (candle_analytic_value env left_expression) = &0)`
  (LABEL_TAC "left_root_nonzero") THENL
   [ASM_SIMP_TAC[SQRT_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(sqrt (candle_analytic_value env right_expression) = &0)`
  (LABEL_TAC "right_root_nonzero") THENL
   [ASM_SIMP_TAC[SQRT_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt (candle_analytic_value env left_expression) *
      sqrt (candle_analytic_value env left_expression) =
    candle_analytic_value env left_expression`
  (LABEL_TAC "left_root_square") THENL
   [REWRITE_TAC[GSYM REAL_POW_2] THEN
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt (candle_analytic_value env right_expression) *
      sqrt (candle_analytic_value env right_expression) =
    candle_analytic_value env right_expression`
  (LABEL_TAC "right_root_square") THENL
   [REWRITE_TAC[GSYM REAL_POW_2] THEN
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[candle_hist_analytic_sqrt_def;
              candle_analytic_value_def;
              candle_analytic_d_def; SQRT_MUL] THEN
  REMOVE_THEN "left_nonzero" MP_TAC THEN
  REMOVE_THEN "right_nonzero" MP_TAC THEN
  REMOVE_THEN "left_root_nonzero" MP_TAC THEN
  REMOVE_THEN "right_root_nonzero" MP_TAC THEN
  REMOVE_THEN "left_root_square" MP_TAC THEN
  REMOVE_THEN "right_root_square" MP_TAC THEN
  CONV_TAC REAL_FIELD);;

let candle_hist_analytic_sqrt_mul_dd = prove
 (`!env (left_expression:candle_analytic_expr) right_expression row column.
     &0 < candle_analytic_value env left_expression /\
     &0 < candle_analytic_value env right_expression
     ==> candle_analytic_dd row column env
           (Candle_analytic_mul
             (candle_hist_analytic_sqrt left_expression)
             (candle_hist_analytic_sqrt right_expression)) =
         candle_analytic_dd row column env
           (candle_hist_analytic_sqrt
             (Candle_analytic_mul left_expression right_expression))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `~(candle_analytic_value env left_expression = &0)`
  (LABEL_TAC "left_nonzero") THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(candle_analytic_value env right_expression = &0)`
  (LABEL_TAC "right_nonzero") THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(sqrt (candle_analytic_value env left_expression) = &0)`
  (LABEL_TAC "left_root_nonzero") THENL
   [ASM_SIMP_TAC[SQRT_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(sqrt (candle_analytic_value env right_expression) = &0)`
  (LABEL_TAC "right_root_nonzero") THENL
   [ASM_SIMP_TAC[SQRT_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt (candle_analytic_value env left_expression) *
      sqrt (candle_analytic_value env left_expression) =
    candle_analytic_value env left_expression`
  (LABEL_TAC "left_root_square") THENL
   [REWRITE_TAC[GSYM REAL_POW_2] THEN
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt (candle_analytic_value env right_expression) *
      sqrt (candle_analytic_value env right_expression) =
    candle_analytic_value env right_expression`
  (LABEL_TAC "right_root_square") THENL
   [REWRITE_TAC[GSYM REAL_POW_2] THEN
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[candle_hist_analytic_sqrt_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def; SQRT_MUL] THEN
  REMOVE_THEN "left_nonzero" MP_TAC THEN
  REMOVE_THEN "right_nonzero" MP_TAC THEN
  REMOVE_THEN "left_root_nonzero" MP_TAC THEN
  REMOVE_THEN "right_root_nonzero" MP_TAC THEN
  REMOVE_THEN "left_root_square" MP_TAC THEN
  REMOVE_THEN "right_root_square" MP_TAC THEN
  CONV_TAC REAL_FIELD);;

let candle_hist_analytic_sqrt_mul_real_jet = prove
 (`!env (left_expression:candle_analytic_expr) right_expression.
     &0 < candle_analytic_value env left_expression /\
     &0 < candle_analytic_value env right_expression
     ==> candle_hist_analytic_real_jet env
           (Candle_analytic_mul
             (candle_hist_analytic_sqrt left_expression)
             (candle_hist_analytic_sqrt right_expression)) =
         candle_hist_analytic_real_jet env
           (candle_hist_analytic_sqrt
             (Candle_analytic_mul left_expression right_expression))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def; PAIR_EQ; FUN_EQ_THM] THEN
  ASM_SIMP_TAC[candle_hist_analytic_sqrt_mul_value;
               candle_hist_analytic_sqrt_mul_d;
               candle_hist_analytic_sqrt_mul_dd]);;

let candle_hist_analytic_sqrt_mul_source_real_jet = prove
 (`!env (left_expression:candle_analytic_expr) right_expression
       lp ln ld up un ud.
     &0 < candle_analytic_value env left_expression /\
     &0 < candle_analytic_value env right_expression
     ==> candle_hist_analytic_real_jet env
           (Candle_analytic_mul
             (candle_hist_analytic_sqrt left_expression)
             (candle_hist_analytic_sqrt right_expression)) =
         candle_hist_analytic_real_jet env
           (Candle_analytic_sqrt lp ln ld up un ud
             (Candle_analytic_mul left_expression right_expression))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
    `candle_hist_analytic_real_jet env
      (candle_hist_analytic_sqrt
        (Candle_analytic_mul left_expression right_expression))` THEN
  ASM_SIMP_TAC[candle_hist_analytic_sqrt_mul_real_jet;
               GSYM candle_hist_analytic_sqrt_bounds_irrelevant]);;

end;;
