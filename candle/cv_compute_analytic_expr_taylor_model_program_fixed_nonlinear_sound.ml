(* ========================================================================== *)
(* Logical fixed-scale operations used by the fixed-nonlinear prototype.      *)
(*                                                                            *)
(* This is the first soundness layer for fixed nonlinear propagation.  The   *)
(* executable keeps dense derivative data fixed after rounding each product  *)
(* back to [candle_fs_scale].  The definitions below expose that arithmetic   *)
(* in HOL; the accompanying theorems connect the executable representation   *)
(* and inherit containment and shape from the established fixed-scale core.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_invariant.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_sound = struct

open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_dim_jet_pi_half;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;

let candle_fsn_interval_mul_def = new_definition
 `candle_fsn_interval_mul left right =
    candle_fs_raw_interval_round candle_fs_scale
      (candle_fs_raw_interval_mul left right)`;;

let candle_fsn_interval_list_scale_def = new_definition
 `candle_fsn_interval_list_scale scalar items =
    candle_fs_raw_interval_list_round candle_fs_scale
      (candle_fs_raw_interval_list_scale scalar items)`;;

let candle_fsn_interval_matrix_scale_def = new_definition
 `candle_fsn_interval_matrix_scale scalar row_lists =
    candle_fs_raw_interval_matrix_round candle_fs_scale
      (candle_fs_raw_interval_matrix_scale scalar row_lists)`;;

let candle_fsn_interval_outer_def = new_definition
 `candle_fsn_interval_outer left right =
    candle_fs_raw_interval_matrix_round candle_fs_scale
      (candle_fs_raw_interval_outer left right)`;;

let candle_fsn_q_inv_interval_def = new_definition
 `candle_fsn_q_inv_interval fixed_interval =
    candle_q_interval_inv (candle_fs_interval_to_q fixed_interval)`;;

let candle_fsn_first_inv_def = new_definition
 `candle_fsn_first_inv first =
    let r = candle_fs_interval_of_q
      (candle_fsn_q_inv_interval (candle_fs_first_value first)) in
    let r2 = candle_fsn_interval_mul r r in
    candle_fs_first_make r
      (candle_fsn_interval_list_scale
        (candle_fs_interval_neg r2)
        (candle_fs_first_gradient first))`;;

let candle_fsn_inv_hessian_def = new_definition
 `candle_fsn_inv_hessian value gradient hessian =
    let r = candle_fs_interval_of_q
      (candle_fsn_q_inv_interval value) in
    let r2 = candle_fsn_interval_mul r r in
    let r3 = candle_fsn_interval_mul r2 r in
    candle_fs_interval_matrix_add
      (candle_fsn_interval_matrix_scale
        (candle_fs_interval_neg r2) hessian)
      (candle_fsn_interval_matrix_scale
        (candle_fs_interval_add r3 r3)
        (candle_fsn_interval_outer gradient gradient))`;;

let candle_fsn_result_inv_def = new_definition
 `candle_fsn_result_inv radii result =
    candle_fs_result_complete_rounded radii
      (candle_fs_result_domain result /\
       candle_q_interval_not_zero
         (candle_fs_interval_to_q
           (candle_fs_first_value (candle_fs_result_center result))) /\
       candle_q_interval_not_zero
         (candle_fs_interval_to_q
           (candle_fs_result_value_bound result)))
      (candle_fsn_first_inv (candle_fs_result_center result))
      (candle_fsn_inv_hessian
        (candle_fs_result_value_bound result)
        (candle_fs_result_gradient_bounds result)
        (candle_fs_result_hessian result))`;;

let candle_fsn_sqrt_domain_def = new_definition
 `candle_fsn_sqrt_domain certificate fixed_interval <=>
    let input = candle_fs_interval_to_q fixed_interval in
    candle_q_interval_sqrt_certificate input certificate /\
    candle_q_interval_not_zero
      (candle_q_interval_add_normalized certificate certificate) /\
    candle_q_interval_not_zero
      (candle_q_interval_mul_normalized
        (candle_q_interval_add_normalized certificate certificate)
        (candle_q_interval_add_normalized input input))`;;

let candle_fsn_first_sqrt_def = new_definition
 `candle_fsn_first_sqrt certificate first =
    let value = candle_fs_interval_of_q certificate in
    let d = candle_fs_interval_of_q
      (candle_q_dim_jet_sqrt_d certificate) in
    candle_fs_first_make value
      (candle_fsn_interval_list_scale d
        (candle_fs_first_gradient first))`;;

let candle_fsn_sqrt_hessian_def = new_definition
 `candle_fsn_sqrt_hessian certificate value gradient hessian =
    let input = candle_fs_interval_to_q value in
    let d = candle_fs_interval_of_q
      (candle_q_dim_jet_sqrt_d certificate) in
    let dd = candle_fs_interval_of_q
      (candle_q_dim_jet_sqrt_dd certificate input) in
    candle_fs_interval_matrix_add
      (candle_fsn_interval_matrix_scale dd
        (candle_fsn_interval_outer gradient gradient))
      (candle_fsn_interval_matrix_scale d hessian)`;;

let candle_fsn_result_sqrt_def = new_definition
 `candle_fsn_result_sqrt radii center_certificate box_certificate result =
    candle_fs_result_complete_rounded radii
      (candle_fs_result_domain result /\
       candle_fsn_sqrt_domain center_certificate
         (candle_fs_first_value (candle_fs_result_center result)) /\
       candle_fsn_sqrt_domain box_certificate
         (candle_fs_result_value_bound result))
      (candle_fsn_first_sqrt center_certificate
        (candle_fs_result_center result))
      (candle_fsn_sqrt_hessian box_certificate
        (candle_fs_result_value_bound result)
        (candle_fs_result_gradient_bounds result)
        (candle_fs_result_hessian result))`;;

let candle_fsn_atn_domain_def = new_definition
 `candle_fsn_atn_domain fixed_interval <=>
    let input = candle_fs_interval_to_q fixed_interval in
    candle_q_interval_atn_range_domain input /\
    candle_q_interval_not_zero
      (candle_q_dim_jet_atn_denominator input)`;;

let candle_fsn_atn_d_fixed_def = new_definition
 `candle_fsn_atn_d_fixed fixed_interval =
    candle_fs_interval_of_q
      (candle_q_dim_jet_atn_d
        (candle_fs_interval_to_q fixed_interval))`;;

let candle_fsn_atn_dd_fixed_def = new_definition
 `candle_fsn_atn_dd_fixed fixed_interval =
    candle_fs_interval_of_q
      (candle_q_dim_jet_atn_dd
        (candle_fs_interval_to_q fixed_interval))`;;

let candle_fsn_first_atn_def = new_definition
 `candle_fsn_first_atn first =
    let value = candle_fs_interval_of_q
      (candle_q_interval_atn_range
        (candle_fs_interval_to_q (candle_fs_first_value first))) in
    let d = candle_fsn_atn_d_fixed (candle_fs_first_value first) in
    candle_fs_first_make value
      (candle_fsn_interval_list_scale d
        (candle_fs_first_gradient first))`;;

let candle_fsn_atn_hessian_def = new_definition
 `candle_fsn_atn_hessian value gradient hessian =
    let d = candle_fsn_atn_d_fixed value in
    let dd = candle_fsn_atn_dd_fixed value in
    candle_fs_interval_matrix_add
      (candle_fsn_interval_matrix_scale dd
        (candle_fsn_interval_outer gradient gradient))
      (candle_fsn_interval_matrix_scale d hessian)`;;

let candle_fsn_result_atn_def = new_definition
 `candle_fsn_result_atn radii result =
    candle_fs_result_complete_rounded radii
      (candle_fs_result_domain result /\
       candle_fsn_atn_domain
         (candle_fs_first_value (candle_fs_result_center result)) /\
       candle_fsn_atn_domain (candle_fs_result_value_bound result))
      (candle_fsn_first_atn (candle_fs_result_center result))
      (candle_fsn_atn_hessian
        (candle_fs_result_value_bound result)
        (candle_fs_result_gradient_bounds result)
        (candle_fs_result_hessian result))`;;

let candle_fsn_result_pi_half_def = new_definition
 `candle_fsn_result_pi_half radii dimensions =
    candle_fs_result_complete_rounded radii T
      (candle_fs_first_make
        (candle_fs_interval_of_q candle_q_pi_half_interval)
        (candle_fs_interval_zeros dimensions))
      (candle_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_cv_raw_bool_correct = prove
 (`!b. Cexp_num (if b then 1 else 0) = candle_cv_bool b`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_bool_def; ARITH_RULE `1 = SUC 0`]);;

let candle_cv_fsn_interval_mul_correct = prove
 (`!left right.
     candle_cv_fsn_interval_mul
       (candle_cv_fs_interval left) (candle_cv_fs_interval right) =
     candle_cv_fs_interval (candle_fsn_interval_mul left right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_interval_mul_def;
              candle_fsn_interval_mul_def;
              candle_cv_fs_scale_correct;
              candle_cv_fs_raw_interval_mul_correct;
              candle_cv_fs_raw_interval_round_correct]);;

let candle_cv_fsn_interval_list_scale_correct = prove
 (`!scalar items.
     candle_cv_fsn_interval_list_scale
       (candle_cv_fs_interval scalar)
       (candle_cv_fs_interval_list items) =
     candle_cv_fs_interval_list
       (candle_fsn_interval_list_scale scalar items)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_interval_list_scale_def;
              candle_fsn_interval_list_scale_def;
              candle_cv_fs_scale_correct;
              candle_cv_fs_raw_interval_list_scale_correct;
              candle_cv_fs_raw_interval_list_round_correct]);;

let candle_cv_fsn_interval_matrix_scale_correct = prove
 (`!scalar rows.
     candle_cv_fsn_interval_matrix_scale
       (candle_cv_fs_interval scalar)
       (candle_cv_fs_interval_matrix rows) =
     candle_cv_fs_interval_matrix
       (candle_fsn_interval_matrix_scale scalar rows)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_interval_matrix_scale_def;
              candle_fsn_interval_matrix_scale_def;
              candle_cv_fs_scale_correct;
              candle_cv_fs_raw_interval_matrix_scale_correct;
              candle_cv_fs_raw_interval_matrix_round_correct]);;

let candle_cv_fsn_interval_outer_correct = prove
 (`!left right.
     candle_cv_fsn_interval_outer
       (candle_cv_fs_interval_list left)
       (candle_cv_fs_interval_list right) =
     candle_cv_fs_interval_matrix
       (candle_fsn_interval_outer left right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_interval_outer_def;
              candle_fsn_interval_outer_def;
              candle_cv_fs_scale_correct;
              candle_cv_fs_raw_interval_outer_correct;
              candle_cv_fs_raw_interval_matrix_round_correct]);;

let candle_cv_fsn_q_inv_interval_correct = prove
 (`!fixed_interval.
     candle_cv_fsn_q_inv_interval
       (candle_cv_fs_interval fixed_interval) =
     candle_cv_q_interval
       (candle_fsn_q_inv_interval fixed_interval)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_q_inv_interval_def;
              candle_fsn_q_inv_interval_def;
              candle_cv_fs_interval_to_q_correct;
              candle_cv_q_interval_inv_correct]);;

let candle_cv_fsn_first_inv_correct = prove
 (`!first.
     candle_cv_fsn_first_inv (candle_cv_fs_first first) =
     candle_cv_fs_first (candle_fsn_first_inv first)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_first_inv_def;
              candle_fsn_first_inv_def;
              candle_cv_fs_first_value_correct;
              candle_cv_fsn_q_inv_interval_correct;
              candle_cv_fs_interval_of_q_correct;
              candle_cv_fsn_interval_mul_correct;
              candle_cv_fs_interval_neg_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fsn_interval_list_scale_correct;
              candle_cv_fs_first_make_correct;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fsn_inv_hessian_correct = prove
 (`!value gradient hessian.
     candle_cv_fsn_inv_hessian
       (candle_cv_fs_interval value)
       (candle_cv_fs_interval_list gradient)
       (candle_cv_fs_interval_matrix hessian) =
     candle_cv_fs_interval_matrix
       (candle_fsn_inv_hessian value gradient hessian)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_inv_hessian_def;
              candle_fsn_inv_hessian_def;
              candle_cv_fsn_q_inv_interval_correct;
              candle_cv_fs_interval_of_q_correct;
              candle_cv_fsn_interval_mul_correct;
              candle_cv_fs_interval_neg_correct;
              candle_cv_fs_interval_add_correct;
              candle_cv_fsn_interval_outer_correct;
              candle_cv_fsn_interval_matrix_scale_correct;
              candle_cv_fs_interval_matrix_add_correct;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fsn_result_inv_correct = prove
 (`!radii result.
     candle_cv_fsn_result_inv
       (candle_cv_lc_vec radii) (candle_cv_fs_result result) =
     candle_cv_fs_result (candle_fsn_result_inv radii result)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_result_inv_def;
              candle_fsn_result_inv_def;
              candle_cv_fs_result_domain_correct;
              candle_cv_fs_result_center_correct;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_result_value_bound_correct;
              candle_cv_fs_interval_to_q_correct;
              candle_cv_q_interval_not_zero_correct;
              candle_cv_raw_bool_correct;
              candle_cv_bool_and_correct;
              candle_cv_fsn_first_inv_correct;
              candle_cv_fs_result_gradient_bounds_correct;
              candle_cv_fs_result_hessian_correct;
              candle_cv_fsn_inv_hessian_correct;
              candle_cv_fs_result_complete_rounded_correct]);;

let candle_cv_fsn_sqrt_domain_correct = prove
 (`!certificate fixed_interval.
     candle_cv_fsn_sqrt_domain
       (candle_cv_q_interval certificate)
       (candle_cv_fs_interval fixed_interval) =
     candle_cv_bool (candle_fsn_sqrt_domain certificate fixed_interval)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_sqrt_domain_def;
              candle_fsn_sqrt_domain_def;
              candle_cv_fs_interval_to_q_correct;
              Candle_cv_exact_interval_sqrt_certificate.
                candle_cv_q_interval_sqrt_certificate_correct;
              Candle_cv_polynomial_expr_dim_jet_representation.
                candle_cv_q_interval_add_normalized_correct;
              Candle_cv_polynomial_expr_dim_jet_representation.
                candle_cv_q_interval_mul_normalized_correct;
              candle_cv_q_interval_not_zero_correct;
              candle_cv_raw_bool_correct;
              GSYM candle_cv_bool_and_def;
              candle_cv_bool_and_correct;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fsn_first_sqrt_correct = prove
 (`!certificate first.
     candle_cv_fsn_first_sqrt
       (candle_cv_q_interval certificate) (candle_cv_fs_first first) =
     candle_cv_fs_first (candle_fsn_first_sqrt certificate first)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_first_sqrt_def;
              candle_fsn_first_sqrt_def;
              candle_cv_fs_interval_of_q_correct;
              candle_cv_q_dim_jet_sqrt_d_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fsn_interval_list_scale_correct;
              candle_cv_fs_first_make_correct;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fsn_sqrt_hessian_correct = prove
 (`!certificate value gradient hessian.
     candle_cv_fsn_sqrt_hessian
       (candle_cv_q_interval certificate)
       (candle_cv_fs_interval value)
       (candle_cv_fs_interval_list gradient)
       (candle_cv_fs_interval_matrix hessian) =
     candle_cv_fs_interval_matrix
       (candle_fsn_sqrt_hessian certificate value gradient hessian)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_sqrt_hessian_def;
              candle_fsn_sqrt_hessian_def;
              candle_cv_fs_interval_to_q_correct;
              candle_cv_q_dim_jet_sqrt_d_correct;
              candle_cv_q_dim_jet_sqrt_dd_correct;
              candle_cv_fs_interval_of_q_correct;
              candle_cv_fsn_interval_outer_correct;
              candle_cv_fsn_interval_matrix_scale_correct;
              candle_cv_fs_interval_matrix_add_correct;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fsn_result_sqrt_correct = prove
 (`!radii center_certificate box_certificate result.
     candle_cv_fsn_result_sqrt
       (candle_cv_lc_vec radii)
       (candle_cv_q_interval center_certificate)
       (candle_cv_q_interval box_certificate)
       (candle_cv_fs_result result) =
     candle_cv_fs_result
       (candle_fsn_result_sqrt radii
         center_certificate box_certificate result)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_result_sqrt_def;
              candle_fsn_result_sqrt_def;
              candle_cv_fs_result_domain_correct;
              candle_cv_fs_result_center_correct;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_result_value_bound_correct;
              candle_cv_fsn_sqrt_domain_correct;
              candle_cv_bool_and_correct;
              candle_cv_fsn_first_sqrt_correct;
              candle_cv_fs_result_gradient_bounds_correct;
              candle_cv_fs_result_hessian_correct;
              candle_cv_fsn_sqrt_hessian_correct;
              candle_cv_fs_result_complete_rounded_correct]);;

let candle_cv_fsn_atn_domain_correct = prove
 (`!fixed_interval.
     candle_cv_fsn_atn_domain (candle_cv_fs_interval fixed_interval) =
     candle_cv_bool (candle_fsn_atn_domain fixed_interval)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_atn_domain_def;
              candle_fsn_atn_domain_def;
              candle_cv_fs_interval_to_q_correct;
              candle_cv_q_interval_atn_range_domain_correct;
              candle_cv_q_dim_jet_atn_denominator_correct;
              candle_cv_q_interval_not_zero_correct;
              candle_cv_raw_bool_correct;
              GSYM candle_cv_bool_and_def;
              candle_cv_bool_and_correct;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fsn_atn_d_fixed_correct = prove
 (`!fixed_interval.
     candle_cv_fsn_atn_d_fixed (candle_cv_fs_interval fixed_interval) =
     candle_cv_fs_interval (candle_fsn_atn_d_fixed fixed_interval)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_atn_d_fixed_def;
              candle_fsn_atn_d_fixed_def;
              candle_cv_fs_interval_to_q_correct;
              candle_cv_q_dim_jet_atn_d_correct;
              candle_cv_fs_interval_of_q_correct]);;

let candle_cv_fsn_atn_dd_fixed_correct = prove
 (`!fixed_interval.
     candle_cv_fsn_atn_dd_fixed (candle_cv_fs_interval fixed_interval) =
     candle_cv_fs_interval (candle_fsn_atn_dd_fixed fixed_interval)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_atn_dd_fixed_def;
              candle_fsn_atn_dd_fixed_def;
              candle_cv_fs_interval_to_q_correct;
              candle_cv_q_dim_jet_atn_dd_correct;
              candle_cv_fs_interval_of_q_correct]);;

let candle_cv_fsn_first_atn_correct = prove
 (`!first.
     candle_cv_fsn_first_atn (candle_cv_fs_first first) =
     candle_cv_fs_first (candle_fsn_first_atn first)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_first_atn_def;
              candle_fsn_first_atn_def;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_interval_to_q_correct;
              candle_cv_q_interval_atn_range_correct;
              candle_cv_fs_interval_of_q_correct;
              candle_cv_fsn_atn_d_fixed_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fsn_interval_list_scale_correct;
              candle_cv_fs_first_make_correct;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fsn_atn_hessian_correct = prove
 (`!value gradient hessian.
     candle_cv_fsn_atn_hessian
       (candle_cv_fs_interval value)
       (candle_cv_fs_interval_list gradient)
       (candle_cv_fs_interval_matrix hessian) =
     candle_cv_fs_interval_matrix
       (candle_fsn_atn_hessian value gradient hessian)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_atn_hessian_def;
              candle_fsn_atn_hessian_def;
              candle_cv_fsn_atn_d_fixed_correct;
              candle_cv_fsn_atn_dd_fixed_correct;
              candle_cv_fsn_interval_outer_correct;
              candle_cv_fsn_interval_matrix_scale_correct;
              candle_cv_fs_interval_matrix_add_correct;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fsn_result_atn_correct = prove
 (`!radii result.
     candle_cv_fsn_result_atn
       (candle_cv_lc_vec radii) (candle_cv_fs_result result) =
     candle_cv_fs_result (candle_fsn_result_atn radii result)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_result_atn_def;
              candle_fsn_result_atn_def;
              candle_cv_fs_result_domain_correct;
              candle_cv_fs_result_center_correct;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_result_value_bound_correct;
              candle_cv_fsn_atn_domain_correct;
              candle_cv_bool_and_correct;
              candle_cv_fsn_first_atn_correct;
              candle_cv_fs_result_gradient_bounds_correct;
              candle_cv_fs_result_hessian_correct;
              candle_cv_fsn_atn_hessian_correct;
              candle_cv_fs_result_complete_rounded_correct]);;

let candle_cv_fsn_result_pi_half_correct = prove
 (`!radii dimensions.
     candle_cv_fsn_result_pi_half
       (candle_cv_lc_vec radii)
       (candle_cv_fs_interval_list dimensions) =
     candle_cv_fs_result
       (candle_fsn_result_pi_half radii dimensions)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fsn_result_pi_half_def;
              candle_fsn_result_pi_half_def;
              candle_cv_q_pi_half_interval_correct;
              candle_cv_fs_interval_of_q_correct;
              candle_cv_fs_interval_zeros_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_interval_zero_matrix_like_correct;
              candle_cv_fs_result_complete_true_correct]);;

let candle_fsn_interval_mul_contains = prove
 (`!left right x y.
     candle_fs_interval_contains left x /\
     candle_fs_interval_contains right y
     ==> candle_fs_interval_contains
           (candle_fsn_interval_mul left right) (x * y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_interval_mul_def] THEN
  MATCH_ACCEPT_TAC candle_fs_interval_mul_sound);;

let candle_fsn_interval_list_scale_length = prove
 (`!scalar items.
     LENGTH (candle_fsn_interval_list_scale scalar items) = LENGTH items`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_interval_list_scale_def;
              candle_fs_raw_interval_list_round_length;
              candle_fs_raw_interval_list_scale_length]);;

let candle_fsn_interval_matrix_scale_shape = prove
 (`!scalar rows width.
     ALL (\row. LENGTH row = width) rows
     ==>
     LENGTH (candle_fsn_interval_matrix_scale scalar rows) = LENGTH rows /\
     ALL (\row. LENGTH row = width)
       (candle_fsn_interval_matrix_scale scalar rows)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fsn_interval_matrix_scale_def;
              candle_fs_raw_interval_matrix_round_length;
              candle_fs_raw_interval_matrix_scale_length] THEN
  MATCH_MP_TAC candle_fs_raw_interval_matrix_round_rows_width THEN
  MATCH_MP_TAC candle_fs_raw_interval_matrix_scale_rows_width THEN
  ASM_REWRITE_TAC[]);;

let candle_fsn_interval_outer_shape = prove
 (`!left right.
     LENGTH (candle_fsn_interval_outer left right) = LENGTH left /\
     ALL (\row. LENGTH row = LENGTH right)
       (candle_fsn_interval_outer left right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_interval_outer_def;
              candle_fs_raw_interval_matrix_round_length] THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC (CONJUNCT1
      (SPECL [`left:((num#num)#(num#num))list`;
              `right:((num#num)#(num#num))list`]
        candle_fs_raw_interval_outer_shape));
    MATCH_MP_TAC candle_fs_raw_interval_matrix_round_rows_width THEN
    MATCH_ACCEPT_TAC (CONJUNCT2
      (SPECL [`left:((num#num)#(num#num))list`;
              `right:((num#num)#(num#num))list`]
        candle_fs_raw_interval_outer_shape))]);;

let candle_fsn_first_inv_gradient_length = prove
 (`!first.
     LENGTH (candle_fs_first_gradient (candle_fsn_first_inv first)) =
     LENGTH (candle_fs_first_gradient first)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fsn_first_inv_def;
              candle_fs_first_make_def;
              candle_fs_first_gradient_def;
              candle_fsn_interval_list_scale_length;
              FST; SND; LET_DEF; LET_END_DEF]);;

let candle_fsn_first_sqrt_gradient_length = prove
 (`!certificate first.
     LENGTH
       (candle_fs_first_gradient
         (candle_fsn_first_sqrt certificate first)) =
     LENGTH (candle_fs_first_gradient first)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_first_sqrt_def;
              candle_fs_first_make_def;
              candle_fs_first_gradient_def;
              candle_fsn_interval_list_scale_length;
              FST; SND; LET_DEF; LET_END_DEF]);;

let candle_fsn_first_atn_gradient_length = prove
 (`!first.
     LENGTH (candle_fs_first_gradient (candle_fsn_first_atn first)) =
     LENGTH (candle_fs_first_gradient first)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fsn_first_atn_def;
              candle_fs_first_make_def;
              candle_fs_first_gradient_def;
              candle_fsn_interval_list_scale_length;
              FST; SND; LET_DEF; LET_END_DEF]);;

let candle_fsn_inv_hessian_shape = prove
 (`!value gradient hessian n.
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian
     ==>
     LENGTH (candle_fsn_inv_hessian value gradient hessian) = n /\
     ALL (\row. LENGTH row = n)
       (candle_fsn_inv_hessian value gradient hessian)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_inv_hessian_def; LET_DEF; LET_END_DEF] THEN
  ASM_MESON_TAC[candle_fsn_interval_matrix_scale_shape;
                candle_fsn_interval_outer_shape;
                candle_fs_interval_matrix_add_length;
                candle_fs_interval_matrix_add_rows_width]);;

let candle_fsn_sqrt_hessian_shape = prove
 (`!certificate value gradient hessian n.
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian
     ==>
     LENGTH
       (candle_fsn_sqrt_hessian certificate value gradient hessian) = n /\
     ALL (\row. LENGTH row = n)
       (candle_fsn_sqrt_hessian certificate value gradient hessian)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_sqrt_hessian_def; LET_DEF; LET_END_DEF] THEN
  ASM_MESON_TAC[candle_fsn_interval_matrix_scale_shape;
                candle_fsn_interval_outer_shape;
                candle_fs_interval_matrix_add_length;
                candle_fs_interval_matrix_add_rows_width]);;

let candle_fsn_atn_hessian_shape = prove
 (`!value gradient hessian n.
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian
     ==>
     LENGTH (candle_fsn_atn_hessian value gradient hessian) = n /\
     ALL (\row. LENGTH row = n)
       (candle_fsn_atn_hessian value gradient hessian)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_atn_hessian_def; LET_DEF; LET_END_DEF] THEN
  ASM_MESON_TAC[candle_fsn_interval_matrix_scale_shape;
                candle_fsn_interval_outer_shape;
                candle_fs_interval_matrix_add_length;
                candle_fs_interval_matrix_add_rows_width]);;

let candle_fsn_inv_jet_shape = prove
 (`!value gradient hessian n.
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian
     ==>
     candle_q_dim_jet_shape n
       (candle_fs_first_to_q
         (candle_fsn_first_inv (candle_fs_first_make value gradient))
         (candle_fsn_inv_hessian value gradient hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_first_to_q_shape;
              candle_fsn_first_inv_gradient_length;
              candle_fs_first_make_def;
              candle_fs_first_gradient_def; FST; SND] THEN
  ASM_MESON_TAC[candle_fsn_inv_hessian_shape]);;

let candle_fsn_sqrt_jet_shape = prove
 (`!certificate value gradient hessian n.
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian
     ==>
     candle_q_dim_jet_shape n
       (candle_fs_first_to_q
         (candle_fsn_first_sqrt certificate
           (candle_fs_first_make value gradient))
         (candle_fsn_sqrt_hessian certificate value gradient hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_first_to_q_shape;
              candle_fsn_first_sqrt_gradient_length;
              candle_fs_first_make_def;
              candle_fs_first_gradient_def; FST; SND] THEN
  ASM_MESON_TAC[candle_fsn_sqrt_hessian_shape]);;

let candle_fsn_atn_jet_shape = prove
 (`!value gradient hessian n.
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian
     ==>
     candle_q_dim_jet_shape n
       (candle_fs_first_to_q
         (candle_fsn_first_atn (candle_fs_first_make value gradient))
         (candle_fsn_atn_hessian value gradient hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_first_to_q_shape;
              candle_fsn_first_atn_gradient_length;
              candle_fs_first_make_def;
              candle_fs_first_gradient_def; FST; SND] THEN
  ASM_MESON_TAC[candle_fsn_atn_hessian_shape]);;

let candle_fsn_pi_half_jet_shape = prove
 (`!dimensions.
     candle_q_dim_jet_shape (LENGTH dimensions)
       (candle_fs_first_to_q
         (candle_fs_first_make
           (candle_fs_interval_of_q candle_q_pi_half_interval)
           (candle_fs_interval_zeros dimensions))
         (candle_fs_interval_zero_matrix dimensions dimensions))`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_first_to_q_shape;
              candle_fs_first_make_def;
              candle_fs_first_gradient_def;
              candle_fs_interval_zeros_length;
              candle_fs_interval_zero_matrix_shape;
              FST; SND]);;

let candle_fsn_interval_list_scale_contains = prove
 (`!scalar scalar_value intervals values.
     candle_fs_interval_contains scalar scalar_value /\
     ALL2 candle_fs_interval_contains intervals values
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fsn_interval_list_scale scalar intervals)
       (MAP (\x:real. scalar_value * x) values)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_interval_list_scale_def] THEN
  MATCH_MP_TAC candle_fs_raw_interval_list_round_contains THEN
  MATCH_MP_TAC candle_fs_raw_interval_list_scale_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fsn_interval_matrix_scale_contains = prove
 (`!scalar scalar_value intervals values.
     candle_fs_interval_contains scalar scalar_value /\
     ALL2 (ALL2 candle_fs_interval_contains) intervals values
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fsn_interval_matrix_scale scalar intervals)
       (MAP (MAP (\x:real. scalar_value * x)) values)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_interval_matrix_scale_def] THEN
  MATCH_MP_TAC candle_fs_raw_interval_matrix_round_contains THEN
  MATCH_MP_TAC candle_fs_raw_interval_matrix_scale_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fsn_interval_outer_contains = prove
 (`!left_intervals left_values right_intervals right_values.
     ALL2 candle_fs_interval_contains left_intervals left_values /\
     ALL2 candle_fs_interval_contains right_intervals right_values
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fsn_interval_outer left_intervals right_intervals)
       (MAP (\x:real. MAP (\y:real. x * y) right_values) left_values)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_interval_outer_def] THEN
  MATCH_MP_TAC candle_fs_raw_interval_matrix_round_contains THEN
  MATCH_MP_TAC candle_fs_raw_interval_outer_contains THEN
  ASM_REWRITE_TAC[]);;

(* The nonlinear operations first obtain rational enclosures and then round
   them outward to the fixed scale.  This scalar lemma is the bridge used by
   all three component proofs below; in particular, it records explicitly
   that the reciprocal's nonzero side condition is checked before rounding. *)

let candle_fsn_q_inv_interval_contains = prove
 (`!fixed_interval x.
     candle_q_interval_not_zero
       (candle_fs_interval_to_q fixed_interval) /\
     candle_fs_interval_contains fixed_interval x
     ==> candle_fs_interval_contains
           (candle_fs_interval_of_q
             (candle_fsn_q_inv_interval fixed_interval))
           (inv x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_interval_of_q_sound THEN
  REWRITE_TAC[candle_fsn_q_inv_interval_def] THEN
  MATCH_MP_TAC candle_q_interval_inv_sound THEN
  ASM_REWRITE_TAC[candle_fs_interval_to_q_contains]);;

let candle_fsn_inv_square_contains = prove
 (`!fixed_interval x.
     candle_q_interval_not_zero
       (candle_fs_interval_to_q fixed_interval) /\
     candle_fs_interval_contains fixed_interval x
     ==> candle_fs_interval_contains
           (candle_fsn_interval_mul
             (candle_fs_interval_of_q
               (candle_fsn_q_inv_interval fixed_interval))
             (candle_fs_interval_of_q
               (candle_fsn_q_inv_interval fixed_interval)))
           (inv x * inv x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fsn_interval_mul_contains THEN
  CONJ_TAC THEN MATCH_MP_TAC candle_fsn_q_inv_interval_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fsn_inv_square_neg_contains = prove
 (`!fixed_interval x.
     candle_q_interval_not_zero
       (candle_fs_interval_to_q fixed_interval) /\
     candle_fs_interval_contains fixed_interval x
     ==> candle_fs_interval_contains
           (candle_fs_interval_neg
             (candle_fsn_interval_mul
               (candle_fs_interval_of_q
                 (candle_fsn_q_inv_interval fixed_interval))
               (candle_fs_interval_of_q
                 (candle_fsn_q_inv_interval fixed_interval))))
           (--(inv x * inv x))`,
  MESON_TAC[candle_fsn_inv_square_contains;
            candle_fs_interval_neg_sound]);;

let candle_fsn_inv_cube_contains = prove
 (`!fixed_interval x.
     candle_q_interval_not_zero
       (candle_fs_interval_to_q fixed_interval) /\
     candle_fs_interval_contains fixed_interval x
     ==> candle_fs_interval_contains
           (candle_fsn_interval_mul
             (candle_fsn_interval_mul
               (candle_fs_interval_of_q
                 (candle_fsn_q_inv_interval fixed_interval))
               (candle_fs_interval_of_q
                 (candle_fsn_q_inv_interval fixed_interval)))
             (candle_fs_interval_of_q
               (candle_fsn_q_inv_interval fixed_interval)))
           ((inv x * inv x) * inv x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fsn_interval_mul_contains THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_fsn_inv_square_contains;
    MATCH_MP_TAC candle_fsn_q_inv_interval_contains] THEN
  ASM_REWRITE_TAC[]);;

let candle_fsn_inv_cube_twice_contains = prove
 (`!fixed_interval x.
     candle_q_interval_not_zero
       (candle_fs_interval_to_q fixed_interval) /\
     candle_fs_interval_contains fixed_interval x
     ==> candle_fs_interval_contains
           (candle_fs_interval_add
             (candle_fsn_interval_mul
               (candle_fsn_interval_mul
                 (candle_fs_interval_of_q
                   (candle_fsn_q_inv_interval fixed_interval))
                 (candle_fs_interval_of_q
                   (candle_fsn_q_inv_interval fixed_interval)))
               (candle_fs_interval_of_q
                 (candle_fsn_q_inv_interval fixed_interval)))
             (candle_fsn_interval_mul
               (candle_fsn_interval_mul
                 (candle_fs_interval_of_q
                   (candle_fsn_q_inv_interval fixed_interval))
                 (candle_fs_interval_of_q
                   (candle_fsn_q_inv_interval fixed_interval)))
               (candle_fs_interval_of_q
                 (candle_fsn_q_inv_interval fixed_interval))))
           (((inv x * inv x) * inv x) +
            ((inv x * inv x) * inv x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_interval_add_sound THEN
  CONJ_TAC THEN MATCH_MP_TAC candle_fsn_inv_cube_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fsn_first_inv_contains = prove
 (`!n first value gradient.
     candle_q_interval_not_zero
       (candle_fs_interval_to_q (candle_fs_first_value first)) /\
     candle_fs_interval_contains (candle_fs_first_value first) value /\
     ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient first) (list_of_seq gradient n)
     ==> candle_fs_interval_contains
           (candle_fs_first_value (candle_fsn_first_inv first))
           (inv value) /\
         ALL2 candle_fs_interval_contains
           (candle_fs_first_gradient (candle_fsn_first_inv first))
           (list_of_seq
             (\i. (--(inv value * inv value)) * gradient i) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_first_inv_def;
              candle_fs_first_make_def;
              candle_fs_first_value_def;
              candle_fs_first_gradient_def;
              FST; SND; LET_DEF; LET_END_DEF] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_fsn_q_inv_interval_contains THEN
    ASM_REWRITE_TAC[GSYM candle_fs_first_value_def];
    REWRITE_TAC[GSYM candle_map_scale_list_of_seq] THEN
    MATCH_MP_TAC candle_fsn_interval_list_scale_contains THEN
    ASM_REWRITE_TAC[GSYM candle_fs_first_value_def;
                    GSYM candle_fs_first_gradient_def] THEN
    MATCH_MP_TAC candle_fsn_inv_square_neg_contains THEN
    ASM_REWRITE_TAC[]]);;

end;;
