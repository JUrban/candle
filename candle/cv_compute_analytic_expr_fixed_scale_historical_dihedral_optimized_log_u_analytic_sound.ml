(* ========================================================================== *)
(* Historical low-work dihedral: identify log-U with the analytic gradient.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_product_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_analytic_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_integration_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_product_sound;;

let candle_fs_hist_log_u_gradient_real_is_product_gradient = prove
 (`!values coordinate.
     ~(candle_fs_hist_u126_real values = &0) /\
     ~(candle_fs_hist_u135_real values = &0)
     ==> candle_fs_hist_log_u_gradient_real values coordinate =
         (candle_fs_hist_u126_gradient_real values coordinate *
            candle_fs_hist_u135_real values +
          candle_fs_hist_u126_real values *
            candle_fs_hist_u135_gradient_real values coordinate) *
         inv
           (candle_fs_hist_u126_real values *
            candle_fs_hist_u135_real values)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2
     (LABEL_TAC "u126_nonzero")
     (LABEL_TAC "u135_nonzero")) THEN
  REWRITE_TAC[candle_fs_hist_log_u_gradient_real_def] THEN
  REMOVE_THEN "u126_nonzero" MP_TAC THEN
  REMOVE_THEN "u135_nonzero" MP_TAC THEN
  CONV_TAC REAL_FIELD);;

let candle_fs_hist_log_u_gradient_real_is_analytic = prove
 (`!values coordinate.
     coordinate < 6 /\
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     ~(candle_fs_hist_u126_real values = &0) /\
     ~(candle_fs_hist_u135_real values = &0)
     ==> candle_fs_hist_log_u_gradient_real values coordinate =
         ((candle_hist_real_jet_value
              (candle_fs_hist_delta_x4_real_jet values) +
            candle_hist_real_jet_value
              (candle_fs_hist_delta_x4_real_jet values)) *
           candle_hist_real_jet_gradient
             (candle_fs_hist_delta_x4_real_jet values) coordinate +
          (candle_hist_real_jet_value
              (candle_fs_hist_b_real_jet values) +
            candle_hist_real_jet_value
              (candle_fs_hist_b_real_jet values)) *
           candle_hist_real_jet_gradient
             (candle_fs_hist_b_real_jet values) coordinate) *
         inv
           (candle_hist_real_jet_value
              (candle_fs_hist_delta_x4_real_jet values) *
            candle_hist_real_jet_value
              (candle_fs_hist_delta_x4_real_jet values) +
            candle_hist_real_jet_value
              (candle_fs_hist_b_real_jet values) *
            candle_hist_real_jet_value
              (candle_fs_hist_b_real_jet values))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(candle_hist_real_jet_value
        (candle_fs_hist_b_real_jet values) +
      candle_hist_real_jet_value
        (candle_fs_hist_b_real_jet values)) *
     candle_hist_real_jet_gradient
       (candle_fs_hist_b_real_jet values) coordinate =
     candle_fs_hist_four_x0_real values *
       EL coordinate (candle_fs_hist_delta_gradient_real values) +
     candle_fs_hist_delta_real values *
       candle_fs_hist_four_x0_gradient_real coordinate`
  (LABEL_TAC "b_gradient_product") THENL
   [MATCH_MP_TAC candle_fs_hist_b_real_jet_gradient_squared_product THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_u126_real values *
      candle_fs_hist_u135_real values =
    candle_hist_real_jet_value
       (candle_fs_hist_delta_x4_real_jet values) *
    candle_hist_real_jet_value
       (candle_fs_hist_delta_x4_real_jet values) +
    candle_hist_real_jet_value
       (candle_fs_hist_b_real_jet values) *
    candle_hist_real_jet_value
       (candle_fs_hist_b_real_jet values)`
  (LABEL_TAC "analytic_denominator") THENL
   [MATCH_MP_TAC candle_fs_hist_u_product_is_analytic_denominator THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[candle_fs_hist_log_u_gradient_real_is_product_gradient;
               candle_fs_hist_u_product_gradient_polynomial] THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_real_jet_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_make_def; FST; SND] THEN
  USE_THEN "analytic_denominator" (SUBST1_TAC o SYM) THEN
  USE_THEN "b_gradient_product" (SUBST1_TAC o SYM) THEN
  REFL_TAC);;

end;;
