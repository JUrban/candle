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

(* Second-order box records are [value; gradient; hessian].  The first       *)
(* discriminator supplies only the two square-root enclosures; all          *)
(* derivative and enclosure work below remains in the computed term.        *)
let candle_cv_fs_hist_second_make_def = new_definition
 `candle_cv_fs_hist_second_make value gradient hessian =
    Cexp_pair value (Cexp_pair gradient hessian)`;;

let candle_cv_fs_hist_second_value_def = new_definition
 `candle_cv_fs_hist_second_value second = Cexp_fst second`;;

let candle_cv_fs_hist_second_gradient_def = new_definition
 `candle_cv_fs_hist_second_gradient second = Cexp_fst (Cexp_snd second)`;;

let candle_cv_fs_hist_second_hessian_def = new_definition
 `candle_cv_fs_hist_second_hessian second = Cexp_snd (Cexp_snd second)`;;

let candle_cv_fs_hist_monotone_coordinate_def = new_definition
 `candle_cv_fs_hist_monotone_coordinate coordinate upper boxes derivatives =
    let box = candle_cv_fs_interval_lookup coordinate boxes in
    let derivative_value = candle_cv_fs_interval_lookup coordinate derivatives in
    Cexp_if (candle_cv_fs_raw_le candle_cv_fs_zero (Cexp_fst derivative_value))
      (candle_cv_fs_hist_point
        (Cexp_if upper (Cexp_snd box) (Cexp_fst box)))
      (Cexp_if (candle_cv_fs_raw_le (Cexp_snd derivative_value)
                  candle_cv_fs_zero)
        (candle_cv_fs_hist_point
          (Cexp_if upper (Cexp_fst box) (Cexp_snd box)))
        box)`;;

let candle_cv_fs_hist_monotone_environment_def = new_definition
 `candle_cv_fs_hist_monotone_environment upper boxes derivatives =
    candle_cv_fs_angle_six
      (candle_cv_fs_hist_monotone_coordinate
        (Cexp_num 0) upper boxes derivatives)
      (candle_cv_fs_hist_monotone_coordinate
        (Cexp_num 1) upper boxes derivatives)
      (candle_cv_fs_hist_monotone_coordinate
        (Cexp_num 2) upper boxes derivatives)
      (candle_cv_fs_hist_monotone_coordinate
        (Cexp_num 3) upper boxes derivatives)
      (candle_cv_fs_hist_monotone_coordinate
        (Cexp_num 4) upper boxes derivatives)
      (candle_cv_fs_hist_monotone_coordinate
        (Cexp_num 5) upper boxes derivatives)`;;

let candle_cv_fs_hist_raw_product_def = new_definition
 `candle_cv_fs_hist_raw_product left right =
    candle_cv_fs_raw_interval_mul left right`;;

let candle_cv_fs_hist_round_scale_def = new_definition
 `candle_cv_fs_hist_round_scale raw =
    candle_cv_fs_raw_interval_round candle_cv_fs_scale raw`;;

let candle_cv_fs_hist_raw_cubic_def = new_definition
 `candle_cv_fs_hist_raw_cubic first second third =
    candle_cv_fs_raw_interval_mul
      (candle_cv_fs_raw_interval_mul first second) third`;;

let candle_cv_fs_hist_delta_gradient_block_0_def = new_definition
 `candle_cv_fs_hist_delta_gradient_block_0 environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    candle_cv_fs_hist_round_scale (candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_ten
        (candle_cv_fs_angle_interval_scale_neg_two
          (candle_cv_fs_hist_raw_product x0 x3))
        (candle_cv_fs_hist_raw_product x1 x3)
        (candle_cv_fs_hist_raw_product x1 x4)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x1 x5))
        (candle_cv_fs_hist_raw_product x2 x3)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x2 x4))
        (candle_cv_fs_hist_raw_product x2 x5)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x3 x3))
        (candle_cv_fs_hist_raw_product x3 x4)
        (candle_cv_fs_hist_raw_product x3 x5)))`;;

let candle_cv_fs_hist_delta_gradient_block_1_def = new_definition
 `candle_cv_fs_hist_delta_gradient_block_1 environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    candle_cv_fs_hist_round_scale (candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_ten
        (candle_cv_fs_hist_raw_product x0 x3)
        (candle_cv_fs_hist_raw_product x0 x4)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x0 x5))
        (candle_cv_fs_angle_interval_scale_neg_two
          (candle_cv_fs_hist_raw_product x1 x4))
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x2 x3))
        (candle_cv_fs_hist_raw_product x2 x4)
        (candle_cv_fs_hist_raw_product x2 x5)
        (candle_cv_fs_hist_raw_product x3 x4)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x4 x4))
        (candle_cv_fs_hist_raw_product x4 x5)))`;;

let candle_cv_fs_hist_delta_gradient_block_2_def = new_definition
 `candle_cv_fs_hist_delta_gradient_block_2 environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    candle_cv_fs_hist_round_scale (candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_ten
        (candle_cv_fs_hist_raw_product x0 x3)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x0 x4))
        (candle_cv_fs_hist_raw_product x0 x5)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x1 x3))
        (candle_cv_fs_hist_raw_product x1 x4)
        (candle_cv_fs_hist_raw_product x1 x5)
        (candle_cv_fs_angle_interval_scale_neg_two
          (candle_cv_fs_hist_raw_product x2 x5))
        (candle_cv_fs_hist_raw_product x3 x5)
        (candle_cv_fs_hist_raw_product x4 x5)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x5 x5))))`;;

let candle_cv_fs_hist_delta_gradient_block_3_def = new_definition
 `candle_cv_fs_hist_delta_gradient_block_3 environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    candle_cv_fs_hist_round_scale (candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_ten
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x0 x0))
        (candle_cv_fs_hist_raw_product x0 x1)
        (candle_cv_fs_hist_raw_product x0 x2)
        (candle_cv_fs_angle_interval_scale_neg_two
          (candle_cv_fs_hist_raw_product x0 x3))
        (candle_cv_fs_hist_raw_product x0 x4)
        (candle_cv_fs_hist_raw_product x0 x5)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x1 x2))
        (candle_cv_fs_hist_raw_product x1 x4)
        (candle_cv_fs_hist_raw_product x2 x5)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x4 x5))))`;;

let candle_cv_fs_hist_delta_gradient_block_4_def = new_definition
 `candle_cv_fs_hist_delta_gradient_block_4 environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    candle_cv_fs_hist_round_scale (candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_ten
        (candle_cv_fs_hist_raw_product x0 x1)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x0 x2))
        (candle_cv_fs_hist_raw_product x0 x3)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x1 x1))
        (candle_cv_fs_hist_raw_product x1 x2)
        (candle_cv_fs_hist_raw_product x1 x3)
        (candle_cv_fs_angle_interval_scale_neg_two
          (candle_cv_fs_hist_raw_product x1 x4))
        (candle_cv_fs_hist_raw_product x1 x5)
        (candle_cv_fs_hist_raw_product x2 x5)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x3 x5))))`;;

let candle_cv_fs_hist_delta_gradient_block_5_def = new_definition
 `candle_cv_fs_hist_delta_gradient_block_5 environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    candle_cv_fs_hist_round_scale (candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_ten
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x0 x1))
        (candle_cv_fs_hist_raw_product x0 x2)
        (candle_cv_fs_hist_raw_product x0 x3)
        (candle_cv_fs_hist_raw_product x1 x2)
        (candle_cv_fs_hist_raw_product x1 x4)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x2 x2))
        (candle_cv_fs_hist_raw_product x2 x3)
        (candle_cv_fs_hist_raw_product x2 x4)
        (candle_cv_fs_angle_interval_scale_neg_two
          (candle_cv_fs_hist_raw_product x2 x5))
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x3 x4))))`;;

let candle_cv_fs_hist_delta_gradient_component_block_def = new_definition
 `candle_cv_fs_hist_delta_gradient_component_block coordinate environment =
    Cexp_if (Cexp_eq coordinate (Cexp_num 0))
      (candle_cv_fs_hist_delta_gradient_block_0 environment)
      (Cexp_if (Cexp_eq coordinate (Cexp_num 1))
        (candle_cv_fs_hist_delta_gradient_block_1 environment)
        (Cexp_if (Cexp_eq coordinate (Cexp_num 2))
          (candle_cv_fs_hist_delta_gradient_block_2 environment)
          (Cexp_if (Cexp_eq coordinate (Cexp_num 3))
            (candle_cv_fs_hist_delta_gradient_block_3 environment)
            (Cexp_if (Cexp_eq coordinate (Cexp_num 4))
              (candle_cv_fs_hist_delta_gradient_block_4 environment)
              (candle_cv_fs_hist_delta_gradient_block_5 environment)))))`;;

let candle_cv_fs_hist_delta_gradient_sign_entry_def = new_definition
 `candle_cv_fs_hist_delta_gradient_sign_entry coordinate boxes hessian =
    let derivatives = candle_cv_fs_interval_lookup coordinate hessian in
    let lower_environment = candle_cv_fs_hist_monotone_environment
      (Cexp_num 0) boxes derivatives in
    let upper_environment = candle_cv_fs_hist_monotone_environment
      (Cexp_num 1) boxes derivatives in
    let lower = candle_cv_fs_hist_delta_gradient_component_block
      coordinate lower_environment in
    let upper = candle_cv_fs_hist_delta_gradient_component_block
      coordinate upper_environment in
    Cexp_pair (Cexp_fst lower) (Cexp_snd upper)`;;

let candle_cv_fs_hist_delta_value_block_def = new_definition
 `candle_cv_fs_hist_delta_value_block environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    let l0 = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six (candle_cv_fs_interval_neg x0) x1 x2
        (candle_cv_fs_interval_neg x3) x4 x5) in
    let l1 = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six x0 (candle_cv_fs_interval_neg x1) x2 x3
        (candle_cv_fs_interval_neg x4) x5) in
    let l2 = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six x0 x1 (candle_cv_fs_interval_neg x2) x3 x4
        (candle_cv_fs_interval_neg x5)) in
    let raw = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_seven
        (candle_cv_fs_hist_raw_cubic x0 x3 l0)
        (candle_cv_fs_hist_raw_cubic x1 x4 l1)
        (candle_cv_fs_hist_raw_cubic x2 x5 l2)
        (candle_cv_fs_interval_neg
          (candle_cv_fs_hist_raw_cubic x1 x2 x3))
        (candle_cv_fs_interval_neg
          (candle_cv_fs_hist_raw_cubic x0 x2 x4))
        (candle_cv_fs_interval_neg
          (candle_cv_fs_hist_raw_cubic x0 x1 x5))
        (candle_cv_fs_interval_neg
          (candle_cv_fs_hist_raw_cubic x3 x4 x5))) in
    candle_cv_fs_raw_interval_round candle_cv_fs_scale_squared raw`;;

let candle_cv_fs_hist_delta_second_def = new_definition
 `candle_cv_fs_hist_delta_second boxes =
    let hessian = candle_cv_fs_angle_delta_hessian boxes in
    let gradient = candle_cv_fs_angle_six
      (candle_cv_fs_hist_delta_gradient_sign_entry
        (Cexp_num 0) boxes hessian)
      (candle_cv_fs_hist_delta_gradient_sign_entry
        (Cexp_num 1) boxes hessian)
      (candle_cv_fs_hist_delta_gradient_sign_entry
        (Cexp_num 2) boxes hessian)
      (candle_cv_fs_hist_delta_gradient_sign_entry
        (Cexp_num 3) boxes hessian)
      (candle_cv_fs_hist_delta_gradient_sign_entry
        (Cexp_num 4) boxes hessian)
      (candle_cv_fs_hist_delta_gradient_sign_entry
        (Cexp_num 5) boxes hessian) in
    let lower_environment = candle_cv_fs_hist_monotone_environment
      (Cexp_num 0) boxes gradient in
    let upper_environment = candle_cv_fs_hist_monotone_environment
      (Cexp_num 1) boxes gradient in
    let lower = candle_cv_fs_hist_delta_value_block lower_environment in
    let upper = candle_cv_fs_hist_delta_value_block upper_environment in
    candle_cv_fs_hist_second_make
      (Cexp_pair (Cexp_fst lower) (Cexp_snd upper)) gradient hessian`;;

let candle_cv_fs_hist_delta_x4_hessian_def = new_definition
 `candle_cv_fs_hist_delta_x4_hessian =
    let zero_value = candle_cv_fs_interval_zero in
    let one_value = candle_cv_fs_interval_one in
    let negative_one = candle_cv_fs_interval_neg one_value in
    let negative_two = candle_cv_fs_angle_interval_scale_neg_two one_value in
    candle_cv_fs_angle_six
      (candle_cv_fs_angle_six negative_two one_value one_value
        negative_two one_value one_value)
      (candle_cv_fs_angle_six one_value zero_value negative_one
        zero_value one_value zero_value)
      (candle_cv_fs_angle_six one_value negative_one zero_value
        zero_value zero_value one_value)
      (candle_cv_fs_angle_six negative_two zero_value zero_value
        zero_value zero_value zero_value)
      (candle_cv_fs_angle_six one_value one_value zero_value
        zero_value zero_value negative_one)
      (candle_cv_fs_angle_six one_value zero_value one_value
        zero_value negative_one zero_value)`;;

let candle_cv_fs_hist_delta_x4_value_block_def = new_definition
 `candle_cv_fs_hist_delta_x4_value_block environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    let linear = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six (candle_cv_fs_interval_neg x0) x1 x2
        (candle_cv_fs_interval_neg x3) x4 x5) in
    let raw = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x1 x2))
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x0 x3))
        (candle_cv_fs_hist_raw_product x1 x4)
        (candle_cv_fs_hist_raw_product x2 x5)
        (candle_cv_fs_interval_neg (candle_cv_fs_hist_raw_product x4 x5))
        (candle_cv_fs_hist_raw_product x0 linear)) in
    candle_cv_fs_raw_interval_round candle_cv_fs_scale raw`;;

let candle_cv_fs_hist_delta_x4_second_def = new_definition
 `candle_cv_fs_hist_delta_x4_second boxes =
    let gradient = candle_cv_fs_hist_delta_x4_gradient boxes in
    let hessian = candle_cv_fs_hist_delta_x4_hessian in
    let lower_environment = candle_cv_fs_hist_monotone_environment
      (Cexp_num 0) boxes gradient in
    let upper_environment = candle_cv_fs_hist_monotone_environment
      (Cexp_num 1) boxes gradient in
    let lower = candle_cv_fs_hist_delta_x4_value_block lower_environment in
    let upper = candle_cv_fs_hist_delta_x4_value_block upper_environment in
    candle_cv_fs_hist_second_make
      (Cexp_pair (Cexp_fst lower) (Cexp_snd upper)) gradient hessian`;;

let candle_cv_fs_hist_sqrt_hessian_entry_def = new_definition
 `candle_cv_fs_hist_sqrt_hessian_entry rowindex colindex derivative_value
      logarithmic_derivative input_gradient input_hessian =
    let scaled_row = candle_cv_fs_angle_interval_mul
      logarithmic_derivative
      (candle_cv_fs_interval_lookup rowindex input_gradient) in
    let inside = candle_cv_fs_interval_add
      (candle_cv_fs_angle_interval_mul
        (candle_cv_fs_interval_lookup colindex input_gradient) scaled_row)
      (candle_cv_fs_angle_matrix_lookup
        rowindex colindex input_hessian) in
    candle_cv_fs_angle_interval_mul derivative_value inside`;;

let candle_cv_fs_hist_sqrt_hessian_symmetric_entry_def = new_definition
 `candle_cv_fs_hist_sqrt_hessian_symmetric_entry rowindex colindex derivative_value
      logarithmic_derivative input_gradient input_hessian =
    Cexp_if (Cexp_less colindex rowindex)
      (candle_cv_fs_hist_sqrt_hessian_entry colindex rowindex derivative_value
        logarithmic_derivative input_gradient input_hessian)
      (candle_cv_fs_hist_sqrt_hessian_entry rowindex colindex derivative_value
        logarithmic_derivative input_gradient input_hessian)`;;

let candle_cv_fs_hist_sqrt_hessian_row_def = new_definition
 `candle_cv_fs_hist_sqrt_hessian_row rowindex derivative_value
      logarithmic_derivative input_gradient input_hessian =
    candle_cv_fs_angle_six
      (candle_cv_fs_hist_sqrt_hessian_symmetric_entry rowindex (Cexp_num 0)
        derivative_value logarithmic_derivative input_gradient input_hessian)
      (candle_cv_fs_hist_sqrt_hessian_symmetric_entry rowindex (Cexp_num 1)
        derivative_value logarithmic_derivative input_gradient input_hessian)
      (candle_cv_fs_hist_sqrt_hessian_symmetric_entry rowindex (Cexp_num 2)
        derivative_value logarithmic_derivative input_gradient input_hessian)
      (candle_cv_fs_hist_sqrt_hessian_symmetric_entry rowindex (Cexp_num 3)
        derivative_value logarithmic_derivative input_gradient input_hessian)
      (candle_cv_fs_hist_sqrt_hessian_symmetric_entry rowindex (Cexp_num 4)
        derivative_value logarithmic_derivative input_gradient input_hessian)
      (candle_cv_fs_hist_sqrt_hessian_symmetric_entry rowindex (Cexp_num 5)
        derivative_value logarithmic_derivative input_gradient input_hessian)`;;

let candle_cv_fs_hist_sqrt_hessian_def = new_definition
 `candle_cv_fs_hist_sqrt_hessian derivative_value logarithmic_derivative
      input_gradient input_hessian =
    candle_cv_fs_angle_six
      (candle_cv_fs_hist_sqrt_hessian_row (Cexp_num 0) derivative_value
        logarithmic_derivative input_gradient input_hessian)
      (candle_cv_fs_hist_sqrt_hessian_row (Cexp_num 1) derivative_value
        logarithmic_derivative input_gradient input_hessian)
      (candle_cv_fs_hist_sqrt_hessian_row (Cexp_num 2) derivative_value
        logarithmic_derivative input_gradient input_hessian)
      (candle_cv_fs_hist_sqrt_hessian_row (Cexp_num 3) derivative_value
        logarithmic_derivative input_gradient input_hessian)
      (candle_cv_fs_hist_sqrt_hessian_row (Cexp_num 4) derivative_value
        logarithmic_derivative input_gradient input_hessian)
      (candle_cv_fs_hist_sqrt_hessian_row (Cexp_num 5) derivative_value
        logarithmic_derivative input_gradient input_hessian)`;;

let candle_cv_fs_hist_second_sqrt_supplied_def = new_definition
 `candle_cv_fs_hist_second_sqrt_supplied input root_value =
    let input_value = candle_cv_fs_hist_second_value input in
    let input_gradient = candle_cv_fs_hist_second_gradient input in
    let input_hessian = candle_cv_fs_hist_second_hessian input in
    let derivative_value = candle_cv_fs_hist_positive_inv
      (candle_cv_fs_angle_interval_scale (Cexp_num 2) root_value) in
    let logarithmic_derivative = candle_cv_fs_interval_neg
      (candle_cv_fs_hist_positive_inv
        (candle_cv_fs_angle_interval_scale (Cexp_num 2) input_value)) in
    candle_cv_fs_hist_second_make root_value
      (candle_cv_fsn_interval_list_scale derivative_value input_gradient)
      (candle_cv_fs_hist_sqrt_hessian derivative_value logarithmic_derivative
        input_gradient input_hessian)`;;

let candle_cv_fs_hist_matrix_scale_def = new_definition
 `candle_cv_fs_hist_matrix_scale scalar matrixvalue =
    candle_cv_fs_raw_interval_matrix_round candle_cv_fs_scale
      (candle_cv_fs_raw_interval_matrix_scale scalar matrixvalue)`;;

let candle_cv_fs_hist_b_hessian_entry_def = new_definition
 `candle_cv_fs_hist_b_hessian_entry rowindex colindex base_hessian
      root_delta_value root_delta_gradient two_over_root_four_x0 x0 =
    let base = candle_cv_fs_angle_matrix_lookup
      rowindex colindex base_hessian in
    Cexp_if (Cexp_eq rowindex (Cexp_num 0))
      (Cexp_if (Cexp_eq colindex (Cexp_num 0))
        (let twice_first_correction = candle_cv_fs_angle_interval_scale
          (Cexp_num 2)
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_interval_lookup (Cexp_num 0) root_delta_gradient)
            two_over_root_four_x0) in
         let diagonal_subtraction = candle_cv_fs_angle_interval_mul
          (candle_cv_fs_angle_interval_mul
            root_delta_value two_over_root_four_x0)
          (candle_cv_fs_hist_positive_inv
            (candle_cv_fs_angle_interval_scale (Cexp_num 2) x0)) in
         candle_cv_fs_interval_add base
          (candle_cv_fs_interval_add twice_first_correction
            (candle_cv_fs_interval_neg diagonal_subtraction)))
        (candle_cv_fs_interval_add base
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_interval_lookup colindex root_delta_gradient)
            two_over_root_four_x0)))
      (Cexp_if (Cexp_eq colindex (Cexp_num 0))
        (candle_cv_fs_interval_add base
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_interval_lookup rowindex root_delta_gradient)
            two_over_root_four_x0))
        base)`;;

let candle_cv_fs_hist_b_hessian_row_def = new_definition
 `candle_cv_fs_hist_b_hessian_row rowindex base_hessian root_delta_value
      root_delta_gradient two_over_root_four_x0 x0 =
    candle_cv_fs_angle_six
      (candle_cv_fs_hist_b_hessian_entry rowindex (Cexp_num 0)
        base_hessian root_delta_value root_delta_gradient
        two_over_root_four_x0 x0)
      (candle_cv_fs_hist_b_hessian_entry rowindex (Cexp_num 1)
        base_hessian root_delta_value root_delta_gradient
        two_over_root_four_x0 x0)
      (candle_cv_fs_hist_b_hessian_entry rowindex (Cexp_num 2)
        base_hessian root_delta_value root_delta_gradient
        two_over_root_four_x0 x0)
      (candle_cv_fs_hist_b_hessian_entry rowindex (Cexp_num 3)
        base_hessian root_delta_value root_delta_gradient
        two_over_root_four_x0 x0)
      (candle_cv_fs_hist_b_hessian_entry rowindex (Cexp_num 4)
        base_hessian root_delta_value root_delta_gradient
        two_over_root_four_x0 x0)
      (candle_cv_fs_hist_b_hessian_entry rowindex (Cexp_num 5)
        base_hessian root_delta_value root_delta_gradient
        two_over_root_four_x0 x0)`;;

let candle_cv_fs_hist_b_hessian_def = new_definition
 `candle_cv_fs_hist_b_hessian root_four_x0 root_delta_value
      root_delta_gradient root_delta_hessian two_over_root_four_x0 x0 =
    let base_hessian = candle_cv_fs_hist_matrix_scale
      root_four_x0 root_delta_hessian in
    candle_cv_fs_angle_six
      (candle_cv_fs_hist_b_hessian_row (Cexp_num 0) base_hessian
        root_delta_value root_delta_gradient two_over_root_four_x0 x0)
      (candle_cv_fs_hist_b_hessian_row (Cexp_num 1) base_hessian
        root_delta_value root_delta_gradient two_over_root_four_x0 x0)
      (candle_cv_fs_hist_b_hessian_row (Cexp_num 2) base_hessian
        root_delta_value root_delta_gradient two_over_root_four_x0 x0)
      (candle_cv_fs_hist_b_hessian_row (Cexp_num 3) base_hessian
        root_delta_value root_delta_gradient two_over_root_four_x0 x0)
      (candle_cv_fs_hist_b_hessian_row (Cexp_num 4) base_hessian
        root_delta_value root_delta_gradient two_over_root_four_x0 x0)
      (candle_cv_fs_hist_b_hessian_row (Cexp_num 5) base_hessian
        root_delta_value root_delta_gradient two_over_root_four_x0 x0)`;;

let candle_cv_fs_hist_log_u_gradient_entry_def = new_definition
 `candle_cv_fs_hist_log_u_gradient_entry coordinate
      u126_gradient reciprocal_u126 u135_gradient reciprocal_u135 =
    candle_cv_fs_interval_add
      (candle_cv_fs_angle_interval_mul
        (candle_cv_fs_interval_lookup coordinate u126_gradient)
        reciprocal_u126)
      (candle_cv_fs_angle_interval_mul
        (candle_cv_fs_interval_lookup coordinate u135_gradient)
        reciprocal_u135)`;;

let candle_cv_fs_hist_log_u_gradient_def = new_definition
 `candle_cv_fs_hist_log_u_gradient
      u126_gradient reciprocal_u126 u135_gradient reciprocal_u135 =
    candle_cv_fs_angle_six
      (candle_cv_fs_hist_log_u_gradient_entry (Cexp_num 0)
        u126_gradient reciprocal_u126 u135_gradient reciprocal_u135)
      (candle_cv_fs_hist_log_u_gradient_entry (Cexp_num 1)
        u126_gradient reciprocal_u126 u135_gradient reciprocal_u135)
      (candle_cv_fs_hist_log_u_gradient_entry (Cexp_num 2)
        u126_gradient reciprocal_u126 u135_gradient reciprocal_u135)
      (candle_cv_fs_hist_log_u_gradient_entry (Cexp_num 3)
        u126_gradient reciprocal_u126 u135_gradient reciprocal_u135)
      (candle_cv_fs_hist_log_u_gradient_entry (Cexp_num 4)
        u126_gradient reciprocal_u126 u135_gradient reciprocal_u135)
      (candle_cv_fs_hist_log_u_gradient_entry (Cexp_num 5)
        u126_gradient reciprocal_u126 u135_gradient reciprocal_u135)`;;

let candle_cv_fs_hist_final_hessian_entry_def = new_definition
 `candle_cv_fs_hist_final_hessian_entry rowindex colindex
      b delta_x4_value delta_x4_gradient delta_x4_hessian
      b_gradient b_hessian reciprocal_u result_gradient log_u_gradient =
    let common_first = candle_cv_fs_interval_neg
      (candle_cv_fs_angle_interval_mul b
        (candle_cv_fs_angle_matrix_lookup
          rowindex colindex delta_x4_hessian)) in
    let common_last = candle_cv_fs_angle_interval_mul delta_x4_value
      (candle_cv_fs_angle_matrix_lookup rowindex colindex b_hessian) in
    let identity = Cexp_if (Cexp_eq rowindex colindex)
      (candle_cv_fs_interval_add common_first common_last)
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_hist_four common_first
          (candle_cv_fs_interval_neg
            (candle_cv_fs_angle_interval_mul
              (candle_cv_fs_interval_lookup rowindex delta_x4_gradient)
              (candle_cv_fs_interval_lookup colindex b_gradient)))
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_interval_lookup colindex delta_x4_gradient)
            (candle_cv_fs_interval_lookup rowindex b_gradient))
          common_last)) in
    candle_cv_fs_interval_add
      (candle_cv_fs_angle_interval_mul reciprocal_u identity)
      (candle_cv_fs_interval_neg
        (candle_cv_fs_angle_interval_mul
          (candle_cv_fs_interval_lookup rowindex result_gradient)
          (candle_cv_fs_interval_lookup colindex log_u_gradient)))`;;

let candle_cv_fs_hist_final_hessian_symmetric_entry_def = new_definition
 `candle_cv_fs_hist_final_hessian_symmetric_entry rowindex colindex
      b delta_x4_value delta_x4_gradient delta_x4_hessian
      b_gradient b_hessian reciprocal_u result_gradient log_u_gradient =
    Cexp_if (Cexp_less colindex rowindex)
      (candle_cv_fs_hist_final_hessian_entry colindex rowindex
        b delta_x4_value delta_x4_gradient delta_x4_hessian
        b_gradient b_hessian reciprocal_u result_gradient log_u_gradient)
      (candle_cv_fs_hist_final_hessian_entry rowindex colindex
        b delta_x4_value delta_x4_gradient delta_x4_hessian
        b_gradient b_hessian reciprocal_u result_gradient log_u_gradient)`;;

let candle_cv_fs_hist_final_hessian_row_def = new_definition
 `candle_cv_fs_hist_final_hessian_row rowindex b delta_x4_value
      delta_x4_gradient delta_x4_hessian b_gradient b_hessian reciprocal_u
      result_gradient log_u_gradient =
    candle_cv_fs_angle_six
      (candle_cv_fs_hist_final_hessian_symmetric_entry
        rowindex (Cexp_num 0) b delta_x4_value delta_x4_gradient
        delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)
      (candle_cv_fs_hist_final_hessian_symmetric_entry
        rowindex (Cexp_num 1) b delta_x4_value delta_x4_gradient
        delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)
      (candle_cv_fs_hist_final_hessian_symmetric_entry
        rowindex (Cexp_num 2) b delta_x4_value delta_x4_gradient
        delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)
      (candle_cv_fs_hist_final_hessian_symmetric_entry
        rowindex (Cexp_num 3) b delta_x4_value delta_x4_gradient
        delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)
      (candle_cv_fs_hist_final_hessian_symmetric_entry
        rowindex (Cexp_num 4) b delta_x4_value delta_x4_gradient
        delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)
      (candle_cv_fs_hist_final_hessian_symmetric_entry
        rowindex (Cexp_num 5) b delta_x4_value delta_x4_gradient
        delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)`;;

let candle_cv_fs_hist_final_hessian_def = new_definition
 `candle_cv_fs_hist_final_hessian b delta_x4_value delta_x4_gradient
      delta_x4_hessian b_gradient b_hessian reciprocal_u
      result_gradient log_u_gradient =
    candle_cv_fs_angle_six
      (candle_cv_fs_hist_final_hessian_row (Cexp_num 0) b delta_x4_value
        delta_x4_gradient delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)
      (candle_cv_fs_hist_final_hessian_row (Cexp_num 1) b delta_x4_value
        delta_x4_gradient delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)
      (candle_cv_fs_hist_final_hessian_row (Cexp_num 2) b delta_x4_value
        delta_x4_gradient delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)
      (candle_cv_fs_hist_final_hessian_row (Cexp_num 3) b delta_x4_value
        delta_x4_gradient delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)
      (candle_cv_fs_hist_final_hessian_row (Cexp_num 4) b delta_x4_value
        delta_x4_gradient delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)
      (candle_cv_fs_hist_final_hessian_row (Cexp_num 5) b delta_x4_value
        delta_x4_gradient delta_x4_hessian b_gradient b_hessian reciprocal_u
        result_gradient log_u_gradient)`;;

let candle_cv_fs_hist_second_order_def = new_definition
 `candle_cv_fs_hist_second_order boxes root_delta_value root_four_x0 =
    let delta_second = candle_cv_fs_hist_delta_second boxes in
    let root_delta = candle_cv_fs_hist_second_sqrt_supplied
      delta_second root_delta_value in
    let root_delta_gradient = candle_cv_fs_hist_second_gradient root_delta in
    let root_delta_hessian = candle_cv_fs_hist_second_hessian root_delta in
    let delta_x4_second = candle_cv_fs_hist_delta_x4_second boxes in
    let delta_x4_value = candle_cv_fs_hist_second_value delta_x4_second in
    let delta_x4_gradient =
      candle_cv_fs_hist_second_gradient delta_x4_second in
    let delta_x4_hessian =
      candle_cv_fs_hist_second_hessian delta_x4_second in
    let u126 = candle_cv_fs_hist_u126 boxes in
    let u135 = candle_cv_fs_hist_u135 boxes in
    let b = candle_cv_fs_angle_interval_mul root_delta_value root_four_x0 in
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
          root_delta_value two_over_root_four_x0))
      (candle_cv_fs_interval_lookup (Cexp_num 1) b_gradient_base)
      (candle_cv_fs_interval_lookup (Cexp_num 2) b_gradient_base)
      (candle_cv_fs_interval_lookup (Cexp_num 3) b_gradient_base)
      (candle_cv_fs_interval_lookup (Cexp_num 4) b_gradient_base)
      (candle_cv_fs_interval_lookup (Cexp_num 5) b_gradient_base) in
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) boxes in
    let b_hessian = candle_cv_fs_hist_b_hessian root_four_x0
      root_delta_value root_delta_gradient root_delta_hessian
      two_over_root_four_x0 x0 in
    let c = candle_cv_fs_hist_c_vector
      delta_x4_value b delta_x4_gradient b_gradient in
    let reciprocal_u126 = candle_cv_fs_hist_positive_inv (Cexp_fst u126) in
    let reciprocal_u135 = candle_cv_fs_hist_positive_inv (Cexp_fst u135) in
    let reciprocal_u = candle_cv_fs_hist_positive_inv
      (candle_cv_fs_angle_interval_mul (Cexp_fst u126) (Cexp_fst u135)) in
    let gradient_base = candle_cv_fsn_interval_list_scale reciprocal_u c in
    let special_gradient = candle_cv_fs_angle_interval_mul root_four_x0
      (candle_cv_fs_hist_positive_inv
        (candle_cv_fs_angle_interval_scale
          (Cexp_num 2) root_delta_value)) in
    let gradient = candle_cv_fs_hist_replace_three
      gradient_base special_gradient in
    let log_u_gradient = candle_cv_fs_hist_log_u_gradient
      (Cexp_snd u126) reciprocal_u126 (Cexp_snd u135) reciprocal_u135 in
    let hessian = candle_cv_fs_hist_final_hessian b delta_x4_value
      delta_x4_gradient delta_x4_hessian b_gradient b_hessian reciprocal_u
      gradient log_u_gradient in
    let quotient = candle_cv_fs_angle_interval_mul
      (candle_cv_fs_interval_neg delta_x4_value)
      (candle_cv_fs_hist_positive_inv b) in
    let value = candle_cv_fs_interval_add
      (candle_cv_fs_interval_of_q candle_cv_q_pi_half_interval)
      (candle_cv_fs_hist_atan_interval quotient) in
    candle_cv_fs_hist_second_make value gradient hessian`;;

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
         candle_cv_fs_hist_first_order_def;
         candle_cv_fs_hist_second_make_def;
         candle_cv_fs_hist_second_value_def;
         candle_cv_fs_hist_second_gradient_def;
         candle_cv_fs_hist_second_hessian_def;
         candle_cv_fs_hist_monotone_coordinate_def;
         candle_cv_fs_hist_monotone_environment_def;
         candle_cv_fs_hist_raw_product_def;
         candle_cv_fs_hist_round_scale_def;
         candle_cv_fs_hist_raw_cubic_def;
         candle_cv_fs_hist_delta_gradient_block_0_def;
         candle_cv_fs_hist_delta_gradient_block_1_def;
         candle_cv_fs_hist_delta_gradient_block_2_def;
         candle_cv_fs_hist_delta_gradient_block_3_def;
         candle_cv_fs_hist_delta_gradient_block_4_def;
         candle_cv_fs_hist_delta_gradient_block_5_def;
         candle_cv_fs_hist_delta_gradient_component_block_def;
         candle_cv_fs_hist_delta_gradient_sign_entry_def;
         candle_cv_fs_hist_delta_value_block_def;
         candle_cv_fs_hist_delta_second_def;
         candle_cv_fs_hist_delta_x4_hessian_def;
         candle_cv_fs_hist_delta_x4_value_block_def;
         candle_cv_fs_hist_delta_x4_second_def;
         candle_cv_fs_hist_sqrt_hessian_entry_def;
         candle_cv_fs_hist_sqrt_hessian_symmetric_entry_def;
         candle_cv_fs_hist_sqrt_hessian_row_def;
         candle_cv_fs_hist_sqrt_hessian_def;
         candle_cv_fs_hist_second_sqrt_supplied_def;
         candle_cv_fs_hist_matrix_scale_def;
         candle_cv_fs_hist_b_hessian_entry_def;
         candle_cv_fs_hist_b_hessian_row_def;
         candle_cv_fs_hist_b_hessian_def;
         candle_cv_fs_hist_log_u_gradient_entry_def;
         candle_cv_fs_hist_log_u_gradient_def;
         candle_cv_fs_hist_final_hessian_entry_def;
         candle_cv_fs_hist_final_hessian_symmetric_entry_def;
         candle_cv_fs_hist_final_hessian_row_def;
         candle_cv_fs_hist_final_hessian_def;
         candle_cv_fs_hist_second_order_def]));;

end;;
