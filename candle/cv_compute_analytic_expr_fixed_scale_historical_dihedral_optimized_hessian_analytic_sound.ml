(* ========================================================================== *)
(* Historical low-work dihedral: final Hessian analytic identification.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_analytic_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_hessian_analytic_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_instantiation;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_integration_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_analytic_sound;;

let candle_fs_hist_result_gradient_real_is_analytic = prove
 (`!values coordinate.
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values
     ==> inv
           (candle_fs_hist_u126_real values *
            candle_fs_hist_u135_real values) *
         candle_fs_hist_c_real values coordinate =
         inv
           (candle_hist_real_jet_value
              (candle_fs_hist_delta_x4_real_jet values) *
            candle_hist_real_jet_value
              (candle_fs_hist_delta_x4_real_jet values) +
            candle_hist_real_jet_value
              (candle_fs_hist_b_real_jet values) *
            candle_hist_real_jet_value
              (candle_fs_hist_b_real_jet values)) *
         (--(candle_hist_real_jet_gradient
                (candle_fs_hist_delta_x4_real_jet values) coordinate *
              candle_hist_real_jet_value
                (candle_fs_hist_b_real_jet values)) +
          candle_hist_real_jet_value
            (candle_fs_hist_delta_x4_real_jet values) *
          candle_hist_real_jet_gradient
            (candle_fs_hist_b_real_jet values) coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
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
  SUBST1_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_u_product_is_analytic_denominator THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[candle_fs_hist_c_real_is_analytic_numerator]]);;

let candle_fs_hist_reference_dihedral_hessian_is_atan = prove
 (`!values rowindex colindex.
     candle_hist_real_jet_hessian
       (candle_fs_hist_reference_dihedral_real_jet values)
       rowindex colindex =
     candle_hist_real_jet_hessian
       (candle_hist_real_jet_atn
         (candle_hist_real_jet_mul
           (candle_hist_real_jet_neg
             (candle_fs_hist_delta_x4_real_jet values))
           (candle_hist_real_jet_inv
             (candle_fs_hist_b_real_jet values))))
       rowindex colindex`,
  REWRITE_TAC[candle_fs_hist_reference_dihedral_real_jet_def;
              candle_real_hist_dihedral_jet_def;
              GSYM candle_fs_hist_b_real_jet_def;
              candle_hist_real_jet_add_def;
              candle_hist_real_jet_pi_half_def;
              candle_hist_real_jet_hessian_def;
              candle_hist_real_jet_make_def;
              FST; SND; REAL_ADD_LID]);;

let candle_fs_hist_final_hessian_entry_real_is_reference = prove
 (`!values rowindex colindex.
     rowindex < 6 /\ colindex < 6 /\
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     ~(candle_fs_hist_u126_real values = &0) /\
     ~(candle_fs_hist_u135_real values = &0)
     ==> candle_fs_hist_final_hessian_entry_real rowindex colindex
           (candle_hist_real_jet_value
             (candle_fs_hist_b_real_jet values))
           (candle_hist_real_jet_value
             (candle_fs_hist_delta_x4_real_jet values))
           (candle_hist_real_jet_gradient
             (candle_fs_hist_delta_x4_real_jet values))
           (candle_hist_real_jet_hessian
             (candle_fs_hist_delta_x4_real_jet values))
           (candle_hist_real_jet_gradient
             (candle_fs_hist_b_real_jet values))
           (candle_hist_real_jet_hessian
             (candle_fs_hist_b_real_jet values))
           (inv
             (candle_fs_hist_u126_real values *
              candle_fs_hist_u135_real values))
           (\i.
              inv
                (candle_fs_hist_u126_real values *
                 candle_fs_hist_u135_real values) *
              candle_fs_hist_c_real values i)
           (candle_fs_hist_log_u_gradient_real values) =
         candle_hist_real_jet_hessian
           (candle_fs_hist_reference_dihedral_real_jet values)
           rowindex colindex`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 < candle_hist_real_jet_value
      (candle_fs_hist_b_real_jet values)`
  (LABEL_TAC "b_positive") THENL
   [MATCH_MP_TAC candle_fs_hist_b_real_jet_value_positive THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(candle_hist_real_jet_value
       (candle_fs_hist_b_real_jet values) = &0)`
  (LABEL_TAC "b_nonzero") THENL
   [USE_THEN "b_positive" MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(candle_hist_real_jet_value
        (candle_fs_hist_delta_x4_real_jet values) *
      candle_hist_real_jet_value
        (candle_fs_hist_delta_x4_real_jet values) +
      candle_hist_real_jet_value
        (candle_fs_hist_b_real_jet values) *
      candle_hist_real_jet_value
        (candle_fs_hist_b_real_jet values) = &0)`
  (LABEL_TAC "denominator_nonzero") THENL
   [MP_TAC
     (SPEC
       `candle_hist_real_jet_value
         (candle_fs_hist_delta_x4_real_jet (values:num->real))`
       REAL_LE_SQUARE) THEN
    MP_TAC
     (MATCH_MP REAL_LT_MUL
       (CONJ
         (ASSUME
           `&0 < candle_hist_real_jet_value
             (candle_fs_hist_b_real_jet (values:num->real))`)
         (ASSUME
           `&0 < candle_hist_real_jet_value
             (candle_fs_hist_b_real_jet (values:num->real))`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC
   (SPECL
     [`candle_fs_hist_delta_x4_real_jet (values:num->real)`;
      `candle_fs_hist_b_real_jet (values:num->real)`;
      `rowindex:num`; `colindex:num`]
     candle_fs_hist_final_hessian_entry_real_is_atan_hessian) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[candle_fs_hist_reference_dihedral_hessian_is_atan] THEN
  REWRITE_TAC[candle_fs_hist_final_hessian_entry_real_def;
              LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[ITLIST;
               candle_fs_hist_result_gradient_real_is_analytic;
               candle_fs_hist_log_u_gradient_real_is_analytic;
               candle_fs_hist_u_product_is_analytic_denominator;
               REAL_LT_IMP_LE]);;

end;;
