(* ========================================================================== *)
(* Historical low-work dihedral: logical first-order executable boundary.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_source_contains_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_first_order_sound = struct

open Candle_cv_analytic_dim_jet_pi_half;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_compute;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_sound;;

(* The hot center evaluator predates the ordinary-HOL historical checker.
   Give its exact arithmetic graph a logical representation before proving
   its source-expression containment contract. *)

let candle_fs_hist_delta_x4_value_direct_def = new_definition
 `candle_fs_hist_delta_x4_value_direct environment =
    let x0 = candle_fs_interval_lookup 0 environment in
    let x1 = candle_fs_interval_lookup 1 environment in
    let x2 = candle_fs_interval_lookup 2 environment in
    let x3 = candle_fs_interval_lookup 3 environment in
    let x4 = candle_fs_interval_lookup 4 environment in
    let x5 = candle_fs_interval_lookup 5 environment in
    let linear = candle_fs_angle_interval_sum
      [candle_fs_interval_neg x0; x1; x2;
       candle_fs_interval_neg x3; x4; x5] in
    candle_fs_angle_interval_sum
      [candle_fs_interval_neg (candle_fs_angle_interval_mul x1 x2);
       candle_fs_interval_neg (candle_fs_angle_interval_mul x0 x3);
       candle_fs_angle_interval_mul x1 x4;
       candle_fs_angle_interval_mul x2 x5;
       candle_fs_interval_neg (candle_fs_angle_interval_mul x4 x5);
       candle_fs_angle_interval_mul x0 linear]`;;

let candle_cv_fs_hist_delta_x4_value_direct_correct = prove
 (`!environment.
     candle_cv_fs_hist_delta_x4_value
       (candle_cv_fs_interval_list environment) =
     candle_cv_fs_interval
       (candle_fs_hist_delta_x4_value_direct environment)`,
  REWRITE_TAC[candle_cv_fs_hist_delta_x4_value_def;
              candle_fs_hist_delta_x4_value_direct_def;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_interval_neg_correct;
              candle_cv_fs_angle_interval_mul_correct;
              candle_cv_fs_angle_interval_sum_correct;
              candle_cv_fs_angle_six_correct;
              LET_DEF; LET_END_DEF]);;

let candle_fs_hist_first_order_direct_def = new_definition
 `candle_fs_hist_first_order_direct environment root_delta root_four_x0 =
    let delta = candle_fs_angle_delta_value environment in
    let delta_gradient = candle_fs_angle_delta_gradient environment in
    let root_delta_d = candle_fs_hist_positive_inv
      (candle_fs_angle_interval_scale 2 root_delta) in
    let root_delta_gradient = candle_fsn_interval_list_scale
      root_delta_d delta_gradient in
    let delta_x4_value = candle_fs_hist_delta_x4_value_direct environment in
    let delta_x4_gradient = candle_fs_hist_delta_x4_gradient environment in
    let u126 = candle_fs_hist_u126 environment in
    let u135 = candle_fs_hist_u135 environment in
    let b = candle_fs_angle_interval_mul root_delta root_four_x0 in
    let two_over_root_four_x0 = candle_fs_angle_interval_mul
      (candle_fs_angle_interval_scale 2 candle_fs_interval_one)
      (candle_fs_hist_positive_inv root_four_x0) in
    let b_gradient_base = candle_fsn_interval_list_scale
      root_four_x0 root_delta_gradient in
    let b_gradient =
      [candle_fs_interval_add
         (candle_fs_interval_lookup 0 b_gradient_base)
         (candle_fs_angle_interval_mul
           root_delta two_over_root_four_x0);
       candle_fs_interval_lookup 1 b_gradient_base;
       candle_fs_interval_lookup 2 b_gradient_base;
       candle_fs_interval_lookup 3 b_gradient_base;
       candle_fs_interval_lookup 4 b_gradient_base;
       candle_fs_interval_lookup 5 b_gradient_base] in
    let c = candle_fs_hist_c_vector
      delta_x4_value b delta_x4_gradient b_gradient in
    let reciprocal_u = candle_fs_hist_positive_inv
      (candle_fs_angle_interval_mul (FST u126) (FST u135)) in
    let gradient_base = candle_fsn_interval_list_scale reciprocal_u c in
    let special_gradient = candle_fs_angle_interval_mul root_four_x0
      (candle_fs_hist_positive_inv
        (candle_fs_angle_interval_scale 2 root_delta)) in
    let gradient = candle_fs_hist_replace_three
      gradient_base special_gradient in
    let quotient = candle_fs_angle_interval_mul
      (candle_fs_interval_neg delta_x4_value)
      (candle_fs_hist_positive_inv b) in
    let value = candle_fs_interval_add
      (candle_fs_interval_of_q candle_q_pi_half_interval)
      (candle_fs_hist_atan_interval quotient) in
    candle_fs_first_make value gradient`;;

let candle_cv_fs_hist_first_order_direct_correct = prove
 (`!environment root_delta root_four_x0.
     candle_cv_fs_hist_first_order
       (candle_cv_fs_interval_list environment)
       (candle_cv_fs_interval root_delta)
       (candle_cv_fs_interval root_four_x0) =
     candle_cv_fs_first
       (candle_fs_hist_first_order_direct
         environment root_delta root_four_x0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_hist_first_order_def;
              candle_fs_hist_first_order_direct_def;
              candle_cv_fs_angle_delta_value_correct;
              candle_cv_fs_angle_delta_gradient_correct;
              candle_cv_fs_hist_positive_inv_correct;
              candle_cv_fs_angle_interval_scale_correct;
              candle_cv_fsn_interval_list_scale_correct;
              candle_cv_fs_hist_delta_x4_value_direct_correct;
              candle_cv_fs_hist_delta_x4_gradient_correct;
              candle_cv_fs_hist_u126_correct;
              candle_cv_fs_hist_u135_correct;
              candle_cv_fs_hist_u_fst_correct;
              candle_cv_fs_angle_interval_mul_correct;
              candle_cv_fs_interval_one_correct;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_interval_add_correct;
              candle_cv_fs_hist_c_vector_correct;
              candle_cv_fs_interval_fst_correct;
              candle_cv_fs_hist_replace_three_correct;
              candle_cv_fs_interval_neg_correct;
              candle_cv_fs_interval_of_q_correct;
              candle_cv_q_pi_half_interval_correct;
              candle_cv_fs_hist_atan_interval_correct;
              candle_cv_fs_angle_six_correct;
              candle_cv_fs_first_make_correct;
              LET_DEF; LET_END_DEF]);;

end;;
