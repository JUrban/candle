(* ========================================================================== *)
(* Case-10173 historical dihedral against the authenticated source syntax.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_source_jet_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_source_dihedral_sound = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_analytic_bridge_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sqrt_factorization_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_polynomials_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_jet_sound;;

(* This is the exact analytic tree compiled by source instructions 31--38.
   The six integer parameters are the authenticated, job-specific bounds on
   the source square-root node; they affect checking but not its semantics. *)

let candle_case10173_hist_source_dihedral_expr_def = new_definition
 `candle_case10173_hist_source_dihedral_expr lp ln ld up un ud =
    Candle_analytic_add Candle_analytic_pi_half
      (Candle_analytic_atn
        (Candle_analytic_mul
          candle_case10173_hist_source_numerator_expr
          (Candle_analytic_inv
            (Candle_analytic_sqrt lp ln ld up un ud
              candle_case10173_hist_source_radical_expr))))`;;

let candle_case10173_hist_separated_dihedral_expr_def = new_definition
 `candle_case10173_hist_separated_dihedral_expr =
    candle_hist_analytic_dihedral
      candle_case10173_hist_delta_x4_expr
      (candle_hist_analytic_sqrt candle_case10173_hist_delta_expr)
      (candle_hist_analytic_sqrt candle_case10173_hist_four_x0_expr)`;;

(* Formal second-order jets form a commutative algebra under analytic
   multiplication.  Stating this once avoids invoking the heavier ring
   proof translator on the case-specific source polynomial. *)

let candle_hist_analytic_real_jet_mul_comm = prove
 (`!env (left_expression:candle_analytic_expr) right_expression.
     candle_hist_analytic_real_jet env
       (Candle_analytic_mul left_expression right_expression) =
     candle_hist_analytic_real_jet env
       (Candle_analytic_mul right_expression left_expression)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def; PAIR_EQ; FUN_EQ_THM;
              candle_analytic_value_def; candle_analytic_d_def;
              candle_analytic_dd_def] THEN
  REPEAT CONJ_TAC THEN REWRITE_TAC[REAL_MUL_AC; REAL_ADD_AC]);;

let candle_case10173_hist_source_radical_real_jet_reversed = prove
 (`!env.
     candle_hist_analytic_real_jet env
       candle_case10173_hist_source_radical_expr =
     candle_hist_analytic_real_jet env
       (Candle_analytic_mul
         candle_case10173_hist_delta_expr
         candle_case10173_hist_four_x0_expr)`,
  GEN_TAC THEN
  TRANS_TAC EQ_TRANS
   `candle_hist_analytic_real_jet env
      (Candle_analytic_mul
        candle_case10173_hist_four_x0_expr
        candle_case10173_hist_delta_expr)` THEN
  REWRITE_TAC[candle_case10173_hist_source_radical_real_jet;
              candle_hist_analytic_real_jet_mul_comm]);;

(* Equal input jets remain equal after a source square-root node. *)

let candle_hist_analytic_sqrt_real_jet_congr = prove
 (`!env (left_expression:candle_analytic_expr) right_expression
       lp ln ld up un ud.
     candle_hist_analytic_real_jet env left_expression =
       candle_hist_analytic_real_jet env right_expression
     ==> candle_hist_analytic_real_jet env
           (Candle_analytic_sqrt lp ln ld up un ud left_expression) =
         candle_hist_analytic_real_jet env
           (Candle_analytic_sqrt lp ln ld up un ud right_expression)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def; PAIR_EQ; FUN_EQ_THM] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[candle_analytic_value_def;
                  candle_analytic_d_def; candle_analytic_dd_def]);;

(* The historical checker evaluates the two positive square roots separately;
   the authenticated source takes one square root after multiplying. *)

let candle_case10173_hist_source_denominator_real_jet = prove
 (`!env lp ln ld up un ud.
     &0 < candle_analytic_value env candle_case10173_hist_delta_expr /\
     &0 < candle_analytic_value env candle_case10173_hist_four_x0_expr
     ==> candle_hist_analytic_real_jet env
           (Candle_analytic_mul
             (candle_hist_analytic_sqrt
               candle_case10173_hist_delta_expr)
             (candle_hist_analytic_sqrt
               candle_case10173_hist_four_x0_expr)) =
         candle_hist_analytic_real_jet env
           (Candle_analytic_sqrt lp ln ld up un ud
             candle_case10173_hist_source_radical_expr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `candle_hist_analytic_real_jet env
      (Candle_analytic_sqrt lp ln ld up un ud
        (Candle_analytic_mul
          candle_case10173_hist_delta_expr
          candle_case10173_hist_four_x0_expr))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_hist_analytic_sqrt_mul_source_real_jet THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC candle_hist_analytic_sqrt_real_jet_congr THEN
    MATCH_ACCEPT_TAC
      (SPEC `env:real list`
        candle_case10173_hist_source_radical_real_jet_reversed)]);;

let candle_case10173_hist_source_denominator_real_jet_reversed = prove
 (`!env lp ln ld up un ud.
     &0 < candle_analytic_value env candle_case10173_hist_delta_expr /\
     &0 < candle_analytic_value env candle_case10173_hist_four_x0_expr
     ==> candle_hist_analytic_real_jet env
           (Candle_analytic_sqrt lp ln ld up un ud
             candle_case10173_hist_source_radical_expr) =
         candle_hist_real_jet_mul
           (candle_hist_analytic_real_jet env
             (candle_hist_analytic_sqrt
               candle_case10173_hist_delta_expr))
           (candle_hist_analytic_real_jet env
             (candle_hist_analytic_sqrt
               candle_case10173_hist_four_x0_expr))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_hist_analytic_real_jet_mul] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC candle_case10173_hist_source_denominator_real_jet THEN
  ASM_REWRITE_TAC[]);;

(* Consequently the complete specialized expression is the same formal jet
   as the exact source tree, including every first and second derivative. *)

let candle_case10173_hist_source_dihedral_real_jet = prove
 (`!env lp ln ld up un ud.
     &0 < candle_analytic_value env candle_case10173_hist_delta_expr /\
     &0 < candle_analytic_value env candle_case10173_hist_four_x0_expr
     ==> candle_hist_analytic_real_jet env
           (candle_case10173_hist_source_dihedral_expr
             lp ln ld up un ud) =
         candle_hist_analytic_real_jet env
           candle_case10173_hist_separated_dihedral_expr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_hist_analytic_real_jet env
      (Candle_analytic_sqrt lp ln ld up un ud
        candle_case10173_hist_source_radical_expr) =
    candle_hist_real_jet_mul
      (candle_hist_analytic_real_jet env
        (candle_hist_analytic_sqrt
          candle_case10173_hist_delta_expr))
      (candle_hist_analytic_real_jet env
        (candle_hist_analytic_sqrt
          candle_case10173_hist_four_x0_expr))`
  (LABEL_TAC "source_denominator") THENL
   [MATCH_MP_TAC
      candle_case10173_hist_source_denominator_real_jet_reversed THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_case10173_hist_source_dihedral_expr_def;
              candle_case10173_hist_separated_dihedral_expr_def;
              candle_hist_analytic_dihedral_def;
              GSYM candle_hist_analytic_real_jet_add;
              GSYM candle_hist_analytic_real_jet_mul;
              GSYM candle_hist_analytic_real_jet_inv;
              GSYM candle_hist_analytic_real_jet_atn;
              GSYM candle_hist_analytic_real_jet_neg] THEN
  ASM_REWRITE_TAC[candle_case10173_hist_source_numerator_real_jet;
                  GSYM candle_hist_analytic_real_jet_neg]);;

end;;
