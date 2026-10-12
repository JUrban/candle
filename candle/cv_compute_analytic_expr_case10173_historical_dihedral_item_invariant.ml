(* ========================================================================== *)
(* Case-10173 historical item: analytic invariant at the source boundary.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_item_sound.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_source_contains_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_invariant.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_item_invariant = struct

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_polynomials_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_jet_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_dihedral_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_contains_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_item_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_invariant;;

let candle_case10173_hist_dim_six = DIMINDEX_CONV `dimindex (:6)`;;

let candle_case10173_hist_source_dihedral_valid = prove
 (`!lp ln ld up un ud.
     candle_analytic_valid_dim 6
       (candle_case10173_hist_source_dihedral_expr lp ln ld up un ud)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_case10173_hist_source_dihedral_expr_def;
              candle_case10173_hist_source_numerator_expr_def;
              candle_case10173_hist_source_radical_expr_def;
              candle_analytic_valid_dim_def;
              candle_poly_valid_dim_def;
              candle_case10173_hist_delta_x4_poly_valid;
              candle_case10173_hist_source_radical_poly_valid]);;

let candle_case10173_hist_source_dihedral_erasure = prove
 (`!center_lp center_ln center_ld center_up center_un center_ud
      box_lp box_ln box_ld box_up box_un box_ud.
     candle_analytic_erase_sqrt_certificates
       (candle_case10173_hist_source_dihedral_expr
         center_lp center_ln center_ld center_up center_un center_ud) =
     candle_analytic_erase_sqrt_certificates
       (candle_case10173_hist_source_dihedral_expr
         box_lp box_ln box_ld box_up box_un box_ud)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_case10173_hist_source_dihedral_expr_def;
              candle_analytic_erase_sqrt_certificates_def]);;

(* This theorem is the reusable completion boundary for the custom item.
   The center evaluator need only establish its reference-jet components;
   [candle_case10173_hist_reference_source_contains] transports those to the
   authenticated source tree.  The whole-box production proof supplies the
   final Hessian premise independently. *)

let candle_case10173_hist_result_analytic_invariant = prove
 (`!boxes
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0
      center_lp center_ln center_ld center_up center_un center_ud
      box_lp box_ln box_ld box_up box_un box_ud
      (type_witness:real^6).
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_analytic_regular_at
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6)
       (candle_case10173_hist_source_dihedral_expr
         center_lp center_ln center_ld center_up center_un center_ud) /\
     (!(p:real^6). p IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_analytic_regular_at
              (list_of_seq (\k. p$(k + 1)) 6)
              (candle_case10173_hist_source_dihedral_expr
                box_lp box_ln box_ld box_up box_un box_ud)) /\
     candle_q_dim_jet_shape 6
       (candle_fs_first_to_q
         (candle_fs_hist_first_order_direct
           (candle_fs_interval_list_of_q
             (candle_q_center_environment_list boxes))
           center_root_delta center_root_four_x0)
         (candle_fs_hist_second_hessian
           (candle_fs_hist_second_order
             (candle_fs_interval_list_of_q boxes)
             box_root_delta box_root_four_x0))) /\
     &0 < candle_fs_hist_delta_real
       (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) /\
     &0 < candle_fs_hist_four_x0_real
       (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) /\
     candle_q_dim_jet_contains_components 6
       (candle_fs_first_to_q
         (candle_fs_hist_first_order_direct
           (candle_fs_interval_list_of_q
             (candle_q_center_environment_list boxes))
           center_root_delta center_root_four_x0)
         (candle_fs_hist_second_hessian
           (candle_fs_hist_second_order
             (candle_fs_interval_list_of_q boxes)
             box_root_delta box_root_four_x0)))
       (candle_hist_real_jet_value
         (candle_fs_hist_reference_dihedral_real_jet
           (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))))
       (candle_hist_real_jet_gradient
         (candle_fs_hist_reference_dihedral_real_jet
           (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1))))
       (candle_hist_real_jet_hessian
         (candle_fs_hist_reference_dihedral_real_jet
           (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)))) /\
     (!(p:real^6). p IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> ALL2 (ALL2 candle_fs_interval_contains)
              (candle_fs_hist_second_hessian
                (candle_fs_hist_second_order
                  (candle_fs_interval_list_of_q boxes)
                  box_root_delta box_root_four_x0))
              (list_of_seq
                (\di. list_of_seq
                  (\dj. partial2 (dj + 1) (di + 1)
                    (candle_analytic_denote_dim
                      (candle_case10173_hist_source_dihedral_expr
                        box_lp box_ln box_ld box_up box_un box_ud)) p) 6) 6))
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       (candle_fs_result_to_q
         (candle_case10173_hist_result
           (candle_q_center_environment_list boxes) boxes
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
           center_root_delta center_root_four_x0
           box_root_delta box_root_four_x0))
       (candle_case10173_hist_source_dihedral_expr
         center_lp center_ln center_ld center_up center_un center_ud)
       (candle_case10173_hist_source_dihedral_expr
         box_lp box_ln box_ld box_up box_un box_ud)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_case10173_hist_result_def] THEN
  MATCH_MP_TAC candle_fs_result_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_case10173_hist_dim_six] THEN
    MATCH_ACCEPT_TAC candle_case10173_hist_source_dihedral_valid;
    MATCH_ACCEPT_TAC candle_case10173_hist_source_dihedral_erasure;
    ASM_REWRITE_TAC[candle_case10173_hist_dim_six];
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    REWRITE_TAC[candle_case10173_hist_dim_six] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_case10173_hist_reference_source_contains THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

end;;
