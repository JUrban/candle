(* ========================================================================== *)
(* Historical low-work dihedral: package the complete optimized real jet.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_hessian_analytic_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_second_order_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_instantiation;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_hessian_analytic_sound;;

(* This constructor lemma is the final representation boundary.  Once the
   three executable payloads enclose one real jet, their historical record is
   a jet accepted by the universal rational checker. *)

let candle_fs_hist_second_components_from_data = prove
 (`!second value gradient hessian_value.
     LENGTH (candle_fs_hist_second_gradient second) = 6 /\
     LENGTH (candle_fs_hist_second_hessian second) = 6 /\
     ALL (\row. LENGTH row = 6)
       (candle_fs_hist_second_hessian second) /\
     candle_fs_interval_contains
       (candle_fs_hist_second_value second) value /\
     ALL2 candle_fs_interval_contains
       (candle_fs_hist_second_gradient second)
       (list_of_seq gradient 6) /\
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_second_hessian second)
       (list_of_seq (\i. list_of_seq (hessian_value i) 6) 6)
     ==> candle_q_dim_jet_contains_components 6
       (candle_fs_hist_second_to_q second)
       value gradient hessian_value`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_second_to_q_def] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  ASM_REWRITE_TAC[candle_fs_first_to_q_shape;
                  candle_fs_first_make_def;
                  candle_fs_first_value_def;
                  candle_fs_first_gradient_def; FST; SND]);;

(* The scalar denoted by the reference analytic jet is exactly the scalar
   enclosed by the historical quotient/arctangent instruction. *)

let candle_fs_hist_reference_dihedral_value = prove
 (`!values.
     candle_hist_real_jet_value
       (candle_fs_hist_reference_dihedral_real_jet values) =
     pi / &2 +
       atn
         (--(candle_fs_hist_delta_x4_real values) *
          inv
            (sqrt (candle_fs_hist_delta_real values) *
             sqrt (candle_fs_hist_four_x0_real values)))`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_reference_dihedral_real_jet_def;
              candle_real_hist_dihedral_jet_def;
              candle_fs_hist_delta_x4_real_jet_def;
              candle_fs_hist_root_delta_real_jet_def;
              candle_fs_hist_root_four_x0_real_jet_def;
              candle_hist_real_jet_add_def;
              candle_hist_real_jet_pi_half_def;
              candle_hist_real_jet_atn_def;
              candle_hist_real_jet_mul_def;
              candle_hist_real_jet_neg_def;
              candle_hist_real_jet_inv_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_make_def; FST; SND]);;

end;;
