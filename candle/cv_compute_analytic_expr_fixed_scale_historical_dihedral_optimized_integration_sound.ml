(* ========================================================================== *)
(* Historical low-work dihedral instruction: complete analytic integration.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_integration_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_instantiation;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound;;

(* First-order companion to the generic low-work Hessian theorem. *)

let candle_hist_real_atan_negative_quotient_gradient_low_work = prove
 (`!(a_jet:real#((num->real)#(num->num->real)))
     (b_jet:real#((num->real)#(num->num->real))) coordinate.
     ~(candle_hist_real_jet_value b_jet = &0) /\
     ~(candle_hist_real_jet_value a_jet *
        candle_hist_real_jet_value a_jet +
        candle_hist_real_jet_value b_jet *
        candle_hist_real_jet_value b_jet = &0)
     ==> candle_hist_real_jet_gradient
       (candle_hist_real_jet_atn
         (candle_hist_real_jet_mul
           (candle_hist_real_jet_neg a_jet)
           (candle_hist_real_jet_inv b_jet))) coordinate =
       inv
         (candle_hist_real_jet_value a_jet *
            candle_hist_real_jet_value a_jet +
          candle_hist_real_jet_value b_jet *
            candle_hist_real_jet_value b_jet) *
       (--(candle_hist_real_jet_gradient a_jet coordinate *
            candle_hist_real_jet_value b_jet) +
        candle_hist_real_jet_value a_jet *
          candle_hist_real_jet_gradient b_jet coordinate)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2
     (LABEL_TAC "b_nonzero")
     (LABEL_TAC "u_nonzero")) THEN
  REWRITE_TAC[candle_hist_real_jet_atn_def;
              candle_hist_real_jet_mul_def;
              candle_hist_real_jet_neg_def;
              candle_hist_real_jet_inv_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              FST; SND] THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_hist_real_jet_value_def]) THEN
  ABBREV_TAC
   `qvalue:real = --(FST a_jet) * inv (FST b_jet)` THEN
  SUBGOAL_THEN
   `~(&1 + qvalue * qvalue = &0)`
  (LABEL_TAC "atan_denominator_nonzero") THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MP_TAC (SPEC `qvalue:real` REAL_LE_SQUARE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "qvalue" THEN
  REMOVE_THEN "b_nonzero" MP_TAC THEN
  REMOVE_THEN "atan_denominator_nonzero" MP_TAC THEN
  REMOVE_THEN "u_nonzero" MP_TAC THEN
  CONV_TAC REAL_FIELD);;

let candle_fs_hist_c_real_is_analytic_numerator = prove
 (`!values coordinate.
     candle_fs_hist_c_real values coordinate =
     --(candle_hist_real_jet_gradient
          (candle_fs_hist_delta_x4_real_jet values) coordinate *
        candle_hist_real_jet_value
          (candle_fs_hist_b_real_jet values)) +
     candle_hist_real_jet_value
       (candle_fs_hist_delta_x4_real_jet values) *
     candle_hist_real_jet_gradient
       (candle_fs_hist_b_real_jet values) coordinate`,
  REWRITE_TAC[candle_fs_hist_c_real_def;
              candle_fs_hist_delta_x4_real_jet_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_make_def; FST; SND]);;

end;;
