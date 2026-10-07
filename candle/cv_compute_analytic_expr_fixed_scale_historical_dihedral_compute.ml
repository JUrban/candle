(* ========================================================================== *)
(* Historical Flyspeck dihedral first-order fixed-scale computation.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The square-root intervals *)
(* are supplied as sealed data in the first performance discriminator.  The  *)
(* delta, delta_x4, U-polynomial, inverse, atan, value, and gradient work all  *)
(* remain inside Kernel.compute.  A certificate check and a general soundness *)
(* theorem are required before this code can support a proof claim.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_angle_polynomials_compute.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_compute = struct

open Candle_cv_analytic_dim_jet_pi_half;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;

let candle_cv_fs_hist_four_def = new_definition
 `candle_cv_fs_hist_four a b c d =
    Cexp_pair a (Cexp_pair b (Cexp_pair c
      (Cexp_pair d (Cexp_num 0))))`;;

let candle_cv_fs_hist_three_def = new_definition
 `candle_cv_fs_hist_three a b c =
    Cexp_pair a (Cexp_pair b (Cexp_pair c (Cexp_num 0)))`;;

let candle_cv_fs_hist_positive_inv_def = new_definition
 `candle_cv_fs_hist_positive_inv value =
    let numerator =
      Cexp_pair candle_cv_fs_scale_squared (Cexp_num 0) in
    Cexp_pair
      (candle_cv_fs_floor_div numerator
        (Cexp_fst (Cexp_snd value)))
      (candle_cv_fs_ceil_div numerator
        (Cexp_fst (Cexp_fst value)))`;;

let candle_cv_fs_hist_rational_constant_def = new_definition
 `candle_cv_fs_hist_rational_constant positive negative denominator =
    let numerator = candle_cv_fs_raw_scale candle_cv_fs_scale
      (Cexp_pair positive negative) in
    Cexp_pair
      (candle_cv_fs_floor_div numerator denominator)
      (candle_cv_fs_ceil_div numerator denominator)`;;

let candle_cv_fs_hist_point_def = new_definition
 `candle_cv_fs_hist_point value = Cexp_pair value value`;;

let candle_cv_fs_hist_atan_pos_lower_def = new_definition
 `candle_cv_fs_hist_atan_pos_lower x =
    let point = candle_cv_fs_hist_point x in
    let x2 = candle_cv_fs_angle_interval_mul point point in
    let polynomial = candle_cv_fs_hist_rational_constant
      (Cexp_num 0) (Cexp_num 1) (Cexp_num 11) in
    let polynomial = candle_cv_fs_interval_add
      (candle_cv_fs_hist_rational_constant
        (Cexp_num 1) (Cexp_num 0) (Cexp_num 9))
      (candle_cv_fs_angle_interval_mul x2 polynomial) in
    let polynomial = candle_cv_fs_interval_add
      (candle_cv_fs_hist_rational_constant
        (Cexp_num 0) (Cexp_num 1) (Cexp_num 7))
      (candle_cv_fs_angle_interval_mul x2 polynomial) in
    let polynomial = candle_cv_fs_interval_add
      (candle_cv_fs_hist_rational_constant
        (Cexp_num 1) (Cexp_num 0) (Cexp_num 5))
      (candle_cv_fs_angle_interval_mul x2 polynomial) in
    let polynomial = candle_cv_fs_interval_add
      (candle_cv_fs_hist_rational_constant
        (Cexp_num 0) (Cexp_num 1) (Cexp_num 3))
      (candle_cv_fs_angle_interval_mul x2 polynomial) in
    candle_cv_fs_angle_interval_mul point
      (candle_cv_fs_interval_add candle_cv_fs_interval_one
        (candle_cv_fs_angle_interval_mul x2 polynomial))`;;

let candle_cv_fs_hist_atan_pos_upper_def = new_definition
 `candle_cv_fs_hist_atan_pos_upper x =
    let point = candle_cv_fs_hist_point x in
    let x2 = candle_cv_fs_angle_interval_mul point point in
    let polynomial = candle_cv_fs_hist_rational_constant
      (Cexp_num 1) (Cexp_num 0) (Cexp_num 13) in
    let polynomial = candle_cv_fs_interval_add
      (candle_cv_fs_hist_rational_constant
        (Cexp_num 0) (Cexp_num 1) (Cexp_num 11))
      (candle_cv_fs_angle_interval_mul x2 polynomial) in
    let polynomial = candle_cv_fs_interval_add
      (candle_cv_fs_hist_rational_constant
        (Cexp_num 1) (Cexp_num 0) (Cexp_num 9))
      (candle_cv_fs_angle_interval_mul x2 polynomial) in
    let polynomial = candle_cv_fs_interval_add
      (candle_cv_fs_hist_rational_constant
        (Cexp_num 0) (Cexp_num 1) (Cexp_num 7))
      (candle_cv_fs_angle_interval_mul x2 polynomial) in
    let polynomial = candle_cv_fs_interval_add
      (candle_cv_fs_hist_rational_constant
        (Cexp_num 1) (Cexp_num 0) (Cexp_num 5))
      (candle_cv_fs_angle_interval_mul x2 polynomial) in
    let polynomial = candle_cv_fs_interval_add
      (candle_cv_fs_hist_rational_constant
        (Cexp_num 0) (Cexp_num 1) (Cexp_num 3))
      (candle_cv_fs_angle_interval_mul x2 polynomial) in
    candle_cv_fs_angle_interval_mul point
      (candle_cv_fs_interval_add candle_cv_fs_interval_one
        (candle_cv_fs_angle_interval_mul x2 polynomial))`;;

let candle_cv_fs_hist_atan_lower_point_def = new_definition
 `candle_cv_fs_hist_atan_lower_point x =
    Cexp_if (candle_cv_fs_raw_le candle_cv_fs_zero x)
      (Cexp_fst (candle_cv_fs_hist_atan_pos_lower x))
      (candle_cv_fs_raw_neg
        (Cexp_snd
          (candle_cv_fs_hist_atan_pos_upper
            (candle_cv_fs_raw_neg x))))`;;

let candle_cv_fs_hist_atan_upper_point_def = new_definition
 `candle_cv_fs_hist_atan_upper_point x =
    Cexp_if (candle_cv_fs_raw_le candle_cv_fs_zero x)
      (Cexp_snd (candle_cv_fs_hist_atan_pos_upper x))
      (candle_cv_fs_raw_neg
        (Cexp_fst
          (candle_cv_fs_hist_atan_pos_lower
            (candle_cv_fs_raw_neg x))))`;;

let candle_cv_fs_hist_atan_interval_def = new_definition
 `candle_cv_fs_hist_atan_interval input =
    Cexp_pair
      (candle_cv_fs_hist_atan_lower_point (Cexp_fst input))
      (candle_cv_fs_hist_atan_upper_point (Cexp_snd input))`;;

let candle_cv_fs_hist_delta_x4_value_def = new_definition
 `candle_cv_fs_hist_delta_x4_value environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    let linear = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six (candle_cv_fs_interval_neg x0) x1 x2
        (candle_cv_fs_interval_neg x3) x4 x5) in
    candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul x1 x2))
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul x0 x3))
        (candle_cv_fs_angle_interval_mul x1 x4)
        (candle_cv_fs_angle_interval_mul x2 x5)
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul x4 x5))
        (candle_cv_fs_angle_interval_mul x0 linear))`;;

let candle_cv_fs_hist_delta_x4_gradient_def = new_definition
 `candle_cv_fs_hist_delta_x4_gradient environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    candle_cv_fs_angle_six
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_angle_six
          (candle_cv_fs_angle_interval_scale_neg_two x0) x1 x2
          (candle_cv_fs_angle_interval_scale_neg_two x3) x4 x5))
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_hist_three x0 (candle_cv_fs_interval_neg x2) x4))
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_hist_three x0 (candle_cv_fs_interval_neg x1) x5))
      (candle_cv_fs_angle_interval_scale_neg_two x0)
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_hist_three x0 x1 (candle_cv_fs_interval_neg x5)))
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_hist_three x0 x2 (candle_cv_fs_interval_neg x4)))`;;

(* Each item is [upper-negative; upper-positive; lower-negative;             *)
(* lower-positive], matching the historical U extremum selector.             *)
let candle_cv_fs_hist_u_points_def = new_definition
 `candle_cv_fs_hist_u_points x gradient =
    let lower_point = candle_cv_fs_hist_point (Cexp_fst x) in
    let upper_point = candle_cv_fs_hist_point (Cexp_snd x) in
    Cexp_if
      (candle_cv_fs_raw_le candle_cv_fs_zero (Cexp_fst gradient))
      (candle_cv_fs_hist_four
        upper_point upper_point lower_point lower_point)
      (Cexp_if
        (candle_cv_fs_raw_le (Cexp_snd gradient) candle_cv_fs_zero)
        (candle_cv_fs_hist_four
          lower_point lower_point upper_point upper_point)
        (candle_cv_fs_hist_four
          lower_point upper_point upper_point lower_point))`;;

let candle_cv_fs_hist_u_value_formula_def = new_definition
 `candle_cv_fs_hist_u_value_formula selector
      points0 points1 points2 =
    let n0 = candle_cv_fs_interval_lookup selector points0 in
    let n1 = candle_cv_fs_interval_lookup selector points1 in
    let n2 = candle_cv_fs_interval_lookup selector points2 in
    let positive_selector = Cexp_add selector (Cexp_num 1) in
    let p0 = candle_cv_fs_interval_lookup positive_selector points0 in
    let p1 = candle_cv_fs_interval_lookup positive_selector points1 in
    let p2 = candle_cv_fs_interval_lookup positive_selector points2 in
    let raw = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six
        (candle_cv_fs_interval_neg
          (candle_cv_fs_raw_interval_mul n0 n0))
        (candle_cv_fs_interval_neg
          (candle_cv_fs_raw_interval_mul n1 n1))
        (candle_cv_fs_interval_neg
          (candle_cv_fs_raw_interval_mul n2 n2))
        (candle_cv_fs_angle_interval_scale (Cexp_num 2)
          (candle_cv_fs_raw_interval_mul p0 p1))
        (candle_cv_fs_angle_interval_scale (Cexp_num 2)
          (candle_cv_fs_raw_interval_mul p1 p2))
        (candle_cv_fs_angle_interval_scale (Cexp_num 2)
          (candle_cv_fs_raw_interval_mul p2 p0))) in
    candle_cv_fs_raw_interval_round candle_cv_fs_scale raw`;;

let candle_cv_fs_hist_u_three_def = new_definition
 `candle_cv_fs_hist_u_three x0 x1 x2 =
    let g0 = candle_cv_fs_angle_interval_scale (Cexp_num 2)
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_hist_three (candle_cv_fs_interval_neg x0) x1 x2)) in
    let g1 = candle_cv_fs_angle_interval_scale (Cexp_num 2)
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_hist_three x0 (candle_cv_fs_interval_neg x1) x2)) in
    let g2 = candle_cv_fs_angle_interval_scale (Cexp_num 2)
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_hist_three x0 x1 (candle_cv_fs_interval_neg x2))) in
    let points0 = candle_cv_fs_hist_u_points x0 g0 in
    let points1 = candle_cv_fs_hist_u_points x1 g1 in
    let points2 = candle_cv_fs_hist_u_points x2 g2 in
    let lower = candle_cv_fs_hist_u_value_formula
      (Cexp_num 2) points0 points1 points2 in
    let upper = candle_cv_fs_hist_u_value_formula
      (Cexp_num 0) points0 points1 points2 in
    Cexp_pair (Cexp_pair (Cexp_fst lower) (Cexp_snd upper))
      (candle_cv_fs_hist_three g0 g1 g2)`;;

let candle_cv_fs_hist_u126_def = new_definition
 `candle_cv_fs_hist_u126 environment =
    let local = candle_cv_fs_hist_u_three
      (candle_cv_fs_interval_lookup (Cexp_num 0) environment)
      (candle_cv_fs_interval_lookup (Cexp_num 1) environment)
      (candle_cv_fs_interval_lookup (Cexp_num 5) environment) in
    Cexp_pair (Cexp_fst local)
      (candle_cv_fs_angle_six
        (candle_cv_fs_interval_lookup (Cexp_num 0) (Cexp_snd local))
        (candle_cv_fs_interval_lookup (Cexp_num 1) (Cexp_snd local))
        candle_cv_fs_interval_zero candle_cv_fs_interval_zero
        candle_cv_fs_interval_zero
        (candle_cv_fs_interval_lookup (Cexp_num 2) (Cexp_snd local)))`;;

let candle_cv_fs_hist_u135_def = new_definition
 `candle_cv_fs_hist_u135 environment =
    let local = candle_cv_fs_hist_u_three
      (candle_cv_fs_interval_lookup (Cexp_num 0) environment)
      (candle_cv_fs_interval_lookup (Cexp_num 2) environment)
      (candle_cv_fs_interval_lookup (Cexp_num 4) environment) in
    Cexp_pair (Cexp_fst local)
      (candle_cv_fs_angle_six
        (candle_cv_fs_interval_lookup (Cexp_num 0) (Cexp_snd local))
        candle_cv_fs_interval_zero
        (candle_cv_fs_interval_lookup (Cexp_num 1) (Cexp_snd local))
        candle_cv_fs_interval_zero
        (candle_cv_fs_interval_lookup (Cexp_num 2) (Cexp_snd local))
        candle_cv_fs_interval_zero)`;;

let candle_cv_fs_hist_c_vector_def = new_definition
 `candle_cv_fs_hist_c_vector delta_x4_value b delta_x4_gradient b_gradient =
    candle_cv_fs_angle_six
      (candle_cv_fs_interval_add
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_interval_lookup (Cexp_num 0) delta_x4_gradient) b))
        (candle_cv_fs_angle_interval_mul delta_x4_value
          (candle_cv_fs_interval_lookup (Cexp_num 0) b_gradient)))
      (candle_cv_fs_interval_add
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_interval_lookup (Cexp_num 1) delta_x4_gradient) b))
        (candle_cv_fs_angle_interval_mul delta_x4_value
          (candle_cv_fs_interval_lookup (Cexp_num 1) b_gradient)))
      (candle_cv_fs_interval_add
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_interval_lookup (Cexp_num 2) delta_x4_gradient) b))
        (candle_cv_fs_angle_interval_mul delta_x4_value
          (candle_cv_fs_interval_lookup (Cexp_num 2) b_gradient)))
      (candle_cv_fs_interval_add
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_interval_lookup (Cexp_num 3) delta_x4_gradient) b))
        (candle_cv_fs_angle_interval_mul delta_x4_value
          (candle_cv_fs_interval_lookup (Cexp_num 3) b_gradient)))
      (candle_cv_fs_interval_add
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_interval_lookup (Cexp_num 4) delta_x4_gradient) b))
        (candle_cv_fs_angle_interval_mul delta_x4_value
          (candle_cv_fs_interval_lookup (Cexp_num 4) b_gradient)))
      (candle_cv_fs_interval_add
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_interval_lookup (Cexp_num 5) delta_x4_gradient) b))
        (candle_cv_fs_angle_interval_mul delta_x4_value
          (candle_cv_fs_interval_lookup (Cexp_num 5) b_gradient)))`;;

let candle_cv_fs_hist_replace_three_def = new_definition
 `candle_cv_fs_hist_replace_three items value =
    candle_cv_fs_angle_six
      (candle_cv_fs_interval_lookup (Cexp_num 0) items)
      (candle_cv_fs_interval_lookup (Cexp_num 1) items)
      (candle_cv_fs_interval_lookup (Cexp_num 2) items)
      value
      (candle_cv_fs_interval_lookup (Cexp_num 4) items)
      (candle_cv_fs_interval_lookup (Cexp_num 5) items)`;;

let candle_cv_fs_hist_first_order_def = new_definition
 `candle_cv_fs_hist_first_order
      environment root_delta root_four_x0 =
    let delta = candle_cv_fs_angle_delta_value environment in
    let delta_gradient = candle_cv_fs_angle_delta_gradient environment in
    let root_delta_d = candle_cv_fs_hist_positive_inv
      (candle_cv_fs_angle_interval_scale (Cexp_num 2) root_delta) in
    let root_delta_gradient = candle_cv_fsn_interval_list_scale
      root_delta_d delta_gradient in
    let delta_x4_value = candle_cv_fs_hist_delta_x4_value environment in
    let delta_x4_gradient =
      candle_cv_fs_hist_delta_x4_gradient environment in
    let u126 = candle_cv_fs_hist_u126 environment in
    let u135 = candle_cv_fs_hist_u135 environment in
    let b = candle_cv_fs_angle_interval_mul root_delta root_four_x0 in
    let two_over_root_four_x0 = candle_cv_fs_angle_interval_mul
      (candle_cv_fs_angle_interval_scale
        (Cexp_num 2) candle_cv_fs_interval_one)
      (candle_cv_fs_hist_positive_inv root_four_x0) in
    let b_gradient_base = candle_cv_fsn_interval_list_scale
      root_four_x0 root_delta_gradient in
    let b_gradient = candle_cv_fs_angle_six
      (candle_cv_fs_interval_add
        (candle_cv_fs_interval_lookup (Cexp_num 0) b_gradient_base)
        (candle_cv_fs_angle_interval_mul
          root_delta two_over_root_four_x0))
      (candle_cv_fs_interval_lookup (Cexp_num 1) b_gradient_base)
      (candle_cv_fs_interval_lookup (Cexp_num 2) b_gradient_base)
      (candle_cv_fs_interval_lookup (Cexp_num 3) b_gradient_base)
      (candle_cv_fs_interval_lookup (Cexp_num 4) b_gradient_base)
      (candle_cv_fs_interval_lookup (Cexp_num 5) b_gradient_base) in
    let c = candle_cv_fs_hist_c_vector
      delta_x4_value b delta_x4_gradient b_gradient in
    let reciprocal_u = candle_cv_fs_hist_positive_inv
      (candle_cv_fs_angle_interval_mul (Cexp_fst u126) (Cexp_fst u135)) in
    let gradient_base = candle_cv_fsn_interval_list_scale reciprocal_u c in
    let special_gradient = candle_cv_fs_angle_interval_mul root_four_x0
      (candle_cv_fs_hist_positive_inv
        (candle_cv_fs_angle_interval_scale (Cexp_num 2) root_delta)) in
    let gradient = candle_cv_fs_hist_replace_three
      gradient_base special_gradient in
    let quotient = candle_cv_fs_angle_interval_mul
      (candle_cv_fs_interval_neg delta_x4_value)
      (candle_cv_fs_hist_positive_inv b) in
    let value = candle_cv_fs_interval_add
      (candle_cv_fs_interval_of_q candle_cv_q_pi_half_interval)
      (candle_cv_fs_hist_atan_interval quotient) in
    candle_cv_fs_first_make value gradient`;;

let candle_cv_fs_hist_first_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fs_angle_compute_eqs
      (map SPEC_ALL
        [candle_cv_fs_hist_four_def;
         candle_cv_fs_hist_three_def;
         candle_cv_fs_hist_positive_inv_def;
         candle_cv_fs_hist_rational_constant_def;
         candle_cv_fs_hist_point_def;
         candle_cv_fs_hist_atan_pos_lower_def;
         candle_cv_fs_hist_atan_pos_upper_def;
         candle_cv_fs_hist_atan_lower_point_def;
         candle_cv_fs_hist_atan_upper_point_def;
         candle_cv_fs_hist_atan_interval_def;
         candle_cv_fs_hist_delta_x4_value_def;
         candle_cv_fs_hist_delta_x4_gradient_def;
         candle_cv_fs_hist_u_points_def;
         candle_cv_fs_hist_u_value_formula_def;
         candle_cv_fs_hist_u_three_def;
         candle_cv_fs_hist_u126_def;
         candle_cv_fs_hist_u135_def;
         candle_cv_fs_hist_c_vector_def;
         candle_cv_fs_hist_replace_three_def;
         candle_cv_fs_hist_first_order_def]));;

end;;
