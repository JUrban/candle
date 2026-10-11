(* ========================================================================== *)
(* Low-work historical dihedral arithmetic against the analytic reference.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_reference_instantiation.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_instantiation;;

(* The historical checker names the product of its two supplied positive
   square roots [b].  Record its exact analytic jet once; the following
   correspondence lemmas may then prove the specialized low-work formulas
   against the same object used by the universal composition theorem. *)

let candle_fs_hist_b_real_jet_def = new_definition
 `candle_fs_hist_b_real_jet values =
    candle_hist_real_jet_mul
      (candle_fs_hist_root_delta_real_jet values)
      (candle_fs_hist_root_four_x0_real_jet values)`;;

let candle_fs_hist_b_value_contains = prove
 (`!values root_delta_value root_four_x0.
     candle_fs_interval_contains root_delta_value
       (sqrt (candle_fs_hist_delta_real values)) /\
     candle_fs_interval_contains root_four_x0
       (sqrt (candle_fs_hist_four_x0_real values))
     ==> candle_fs_interval_contains
       (candle_fs_angle_interval_mul root_delta_value root_four_x0)
       (candle_hist_real_jet_value
         (candle_fs_hist_b_real_jet values))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_b_real_jet_def;
              candle_hist_real_jet_mul_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_make_def;
              candle_fs_hist_root_delta_real_jet_def;
              candle_fs_hist_root_four_x0_real_jet_def;
              FST; SND] THEN
  MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
  ASM_REWRITE_TAC[]);;

end;;
