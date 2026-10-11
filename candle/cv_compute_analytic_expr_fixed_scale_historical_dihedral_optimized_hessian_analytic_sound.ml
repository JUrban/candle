(* ========================================================================== *)
(* Historical low-work dihedral: final Hessian analytic identification.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_log_u_analytic_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_hessian_analytic_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_root_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_x4_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
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

(* The executable matrix stores only one triangle.  Establish symmetry at the
   analytic-jet boundary once, rather than relying on an informal calculus
   argument when the stored entry is selected below the diagonal. *)

let candle_hist_real_atan_negative_quotient_hessian_symmetric = prove
 (`!(a_jet:real#((num->real)#(num->num->real)))
     (b_jet:real#((num->real)#(num->num->real))) rowindex colindex.
     candle_hist_real_jet_hessian a_jet rowindex colindex =
       candle_hist_real_jet_hessian a_jet colindex rowindex /\
     candle_hist_real_jet_hessian b_jet rowindex colindex =
       candle_hist_real_jet_hessian b_jet colindex rowindex
     ==> candle_hist_real_jet_hessian
           (candle_hist_real_jet_atn
             (candle_hist_real_jet_mul
               (candle_hist_real_jet_neg a_jet)
               (candle_hist_real_jet_inv b_jet)))
           rowindex colindex =
         candle_hist_real_jet_hessian
           (candle_hist_real_jet_atn
             (candle_hist_real_jet_mul
               (candle_hist_real_jet_neg a_jet)
               (candle_hist_real_jet_inv b_jet)))
           colindex rowindex`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_hist_real_jet_hessian_def]) THEN
  REWRITE_TAC[candle_hist_real_jet_atn_def;
              candle_hist_real_jet_mul_def;
              candle_hist_real_jet_neg_def;
              candle_hist_real_jet_inv_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def;
              FST; SND] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC (BINOP_CONV REAL_POLY_CONV) THEN REFL_TAC);;

let candle_fs_hist_b_real_jet_hessian_symmetric = prove
 (`!values rowindex colindex.
     candle_hist_real_jet_hessian
       (candle_fs_hist_b_real_jet values) rowindex colindex =
     candle_hist_real_jet_hessian
       (candle_fs_hist_b_real_jet values) colindex rowindex`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_b_real_jet_def;
              candle_hist_real_jet_mul_def;
              candle_fs_hist_root_delta_real_jet_def;
              candle_fs_hist_root_four_x0_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_hessian_def;
              FST; SND;
              candle_fs_hist_delta_hessian_component_real_symmetric;
              candle_fs_hist_four_x0_hessian_real_symmetric] THEN
  CONV_TAC (BINOP_CONV REAL_POLY_CONV) THEN REFL_TAC);;

let candle_fs_hist_reference_dihedral_hessian_symmetric = prove
 (`!values rowindex colindex.
     candle_hist_real_jet_hessian
       (candle_fs_hist_reference_dihedral_real_jet values)
       rowindex colindex =
     candle_hist_real_jet_hessian
       (candle_fs_hist_reference_dihedral_real_jet values)
       colindex rowindex`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_reference_dihedral_hessian_is_atan] THEN
  MATCH_MP_TAC candle_hist_real_atan_negative_quotient_hessian_symmetric THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_real_jet_def;
              candle_hist_real_jet_make_def;
              candle_hist_real_jet_hessian_def;
              FST; SND;
              candle_fs_hist_delta_x4_hessian_component_real_symmetric;
              candle_fs_hist_b_real_jet_hessian_symmetric]);;

let candle_fs_hist_final_hessian_symmetric_real_is_reference = prove
 (`!values rowindex colindex.
     rowindex < 6 /\ colindex < 6 /\
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     ~(candle_fs_hist_u126_real values = &0) /\
     ~(candle_fs_hist_u135_real values = &0)
     ==> candle_fs_hist_final_hessian_symmetric_real rowindex colindex
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
  REWRITE_TAC[candle_fs_hist_final_hessian_symmetric_real_def] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[candle_fs_hist_final_hessian_entry_real_is_reference;
               candle_fs_hist_reference_dihedral_hessian_symmetric]);;

let candle_fs_hist_final_hessian_reference_list_of_seq = prove
 (`!values.
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     ~(candle_fs_hist_u126_real values = &0) /\
     ~(candle_fs_hist_u135_real values = &0)
     ==> list_of_seq
           (\i. list_of_seq
             (\j. candle_fs_hist_final_hessian_symmetric_real i j
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
               (\k.
                  inv
                    (candle_fs_hist_u126_real values *
                     candle_fs_hist_u135_real values) *
                  candle_fs_hist_c_real values k)
               (candle_fs_hist_log_u_gradient_real values)) 6) 6 =
         list_of_seq
           (\i. list_of_seq
             (\j. candle_hist_real_jet_hessian
               (candle_fs_hist_reference_dihedral_real_jet values) i j)
             6) 6`,
  GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `rowindex:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `colindex:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ;
               candle_fs_hist_final_hessian_symmetric_real_is_reference]);;

let candle_fs_hist_final_hessian_reference_contains = prove
 (`!values b delta_x4_value delta_x4_gradient delta_x4_hessian
      b_gradient b_hessian reciprocal_u result_gradient log_u_gradient.
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     ~(candle_fs_hist_u126_real values = &0) /\
     ~(candle_fs_hist_u135_real values = &0) /\
     candle_fs_interval_contains b
       (candle_hist_real_jet_value (candle_fs_hist_b_real_jet values)) /\
     candle_fs_interval_contains delta_x4_value
       (candle_hist_real_jet_value
         (candle_fs_hist_delta_x4_real_jet values)) /\
     LENGTH delta_x4_gradient = 6 /\
     ALL2 candle_fs_interval_contains delta_x4_gradient
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_delta_x4_real_jet values)) 6) /\
     LENGTH delta_x4_hessian = 6 /\
     ALL (\matrix_row. LENGTH matrix_row = 6) delta_x4_hessian /\
     ALL2 (ALL2 candle_fs_interval_contains) delta_x4_hessian
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_delta_x4_real_jet values) i) 6) 6) /\
     LENGTH b_gradient = 6 /\
     ALL2 candle_fs_interval_contains b_gradient
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_b_real_jet values)) 6) /\
     LENGTH b_hessian = 6 /\
     ALL (\matrix_row. LENGTH matrix_row = 6) b_hessian /\
     ALL2 (ALL2 candle_fs_interval_contains) b_hessian
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_b_real_jet values) i) 6) 6) /\
     candle_fs_interval_contains reciprocal_u
       (inv
         (candle_fs_hist_u126_real values *
          candle_fs_hist_u135_real values)) /\
     LENGTH result_gradient = 6 /\
     ALL2 candle_fs_interval_contains result_gradient
       (list_of_seq
         (\i. inv
           (candle_fs_hist_u126_real values *
            candle_fs_hist_u135_real values) *
           candle_fs_hist_c_real values i) 6) /\
     LENGTH log_u_gradient = 6 /\
     ALL2 candle_fs_interval_contains log_u_gradient
       (list_of_seq
         (candle_fs_hist_log_u_gradient_real values) 6)
     ==> ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_final_hessian b delta_x4_value
         delta_x4_gradient delta_x4_hessian b_gradient b_hessian
         reciprocal_u result_gradient log_u_gradient)
       (list_of_seq
         (\i. list_of_seq
           (\j. candle_hist_real_jet_hessian
             (candle_fs_hist_reference_dihedral_real_jet values) i j)
           6) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `list_of_seq
      (\i. list_of_seq
        (\j. candle_fs_hist_final_hessian_symmetric_real i j
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
          (\k. inv
            (candle_fs_hist_u126_real values *
             candle_fs_hist_u135_real values) *
            candle_fs_hist_c_real values k)
          (candle_fs_hist_log_u_gradient_real values)) 6) 6 =
    list_of_seq
      (\i. list_of_seq
        (\j. candle_hist_real_jet_hessian
          (candle_fs_hist_reference_dihedral_real_jet values) i j)
        6) 6`
  (LABEL_TAC "reference_matrix") THENL
   [MATCH_MP_TAC candle_fs_hist_final_hessian_reference_list_of_seq THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "reference_matrix"
    (fun matrix_eq -> ONCE_REWRITE_TAC[GSYM matrix_eq]) THEN
  MATCH_MP_TAC candle_fs_hist_final_hessian_contains THEN
  ASM_REWRITE_TAC[]);;

end;;
