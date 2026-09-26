(* ========================================================================== *)
(* Soundness substrate for reflected signed fixed-scale arithmetic.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The executable backend is useful only after   *)
(* these representation and real-semantics results are lifted through        *)
(* intervals, jets, and the polynomial interpreter.  This file begins that   *)
(* reusable proof; no theorem here is tied to a particular Flyspeck formula.  *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_mul_core.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;

module Candle_cv_analytic_expr_fixed_scale_sound = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_representation;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_sound;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_fixed_scale_compute;;

(* -------------------------------------------------------------------------- *)
(* Ordinary HOL representation.                                               *)
(* -------------------------------------------------------------------------- *)

let candle_fs_scale_def = new_definition
 `candle_fs_scale = 1000000000000`;;

let candle_fs_scale_squared_def = new_definition
 `candle_fs_scale_squared = candle_fs_scale * candle_fs_scale`;;

let candle_fs_two_scale_squared_def = new_definition
 `candle_fs_two_scale_squared = 2 * candle_fs_scale_squared`;;

let candle_fs_real_def = new_definition
 `candle_fs_real (z:num#num) = candle_lc_zreal z / &candle_fs_scale`;;

let candle_fs_raw_real_def = new_definition
 `candle_fs_raw_real denominator (z:num#num) =
    candle_lc_zreal z / &denominator`;;

let candle_fs_raw_neg_def = new_definition
 `candle_fs_raw_neg (z:num#num) = (SND z,FST z)`;;

let candle_fs_canonical_def = new_definition
 `candle_fs_canonical (z:num#num) =
    if FST z < SND z then (0,SND z - FST z)
    else (FST z - SND z,0)`;;

let candle_fs_add_def = new_definition
 `candle_fs_add (x:num#num) y =
    candle_fs_canonical (candle_lc_zadd x y)`;;

let candle_fs_floor_div_def = new_definition
 `candle_fs_floor_div (z:num#num) denominator =
    if FST z < SND z then
      (0,candle_q_ceil_div (SND z - FST z) denominator)
    else ((FST z - SND z) DIV denominator,0)`;;

let candle_fs_ceil_div_def = new_definition
 `candle_fs_ceil_div (z:num#num) denominator =
    if FST z < SND z then
      (0,(SND z - FST z) DIV denominator)
    else (candle_q_ceil_div (FST z - SND z) denominator,0)`;;

let candle_fs_to_q_def = new_definition
 `candle_fs_to_q (z:num#num) = (z,candle_fs_scale - 1)`;;

let candle_fs_raw_le_def = new_definition
 `candle_fs_raw_le (x:num#num) y <=>
    FST x + SND y <= FST y + SND x`;;

let candle_fs_raw_min_def = new_definition
 `candle_fs_raw_min (x:num#num) y =
    if candle_fs_raw_le x y then x else y`;;

let candle_fs_raw_max_def = new_definition
 `candle_fs_raw_max (x:num#num) y =
    if candle_fs_raw_le x y then y else x`;;

let candle_fs_raw_abs_def = new_definition
 `candle_fs_raw_abs (z:num#num) =
    candle_fs_raw_max z (candle_fs_raw_neg z)`;;

let candle_fs_of_q_lower_def = new_definition
 `candle_fs_of_q_lower (q:(num#num)#num) =
    FST (candle_q_fixed_round_lower q)`;;

let candle_fs_of_q_upper_def = new_definition
 `candle_fs_of_q_upper (q:(num#num)#num) =
    FST (candle_q_fixed_round_upper q)`;;

let candle_cv_fs_interval_def = new_definition
 `candle_cv_fs_interval (i:(num#num)#(num#num)) =
    Cexp_pair (candle_cv_lc_z (FST i)) (candle_cv_lc_z (SND i))`;;

let candle_fs_interval_zero_def = new_definition
 `candle_fs_interval_zero = ((0,0),(0,0))`;;

let candle_fs_interval_one_def = new_definition
 `candle_fs_interval_one =
    ((candle_fs_scale,0),(candle_fs_scale,0))`;;

let candle_fs_interval_of_q_def = new_definition
 `candle_fs_interval_of_q
    (i:((num#num)#num)#((num#num)#num)) =
    (candle_fs_of_q_lower (FST i),
     candle_fs_of_q_upper (SND i))`;;

let candle_fs_interval_constant_def = new_definition
 `candle_fs_interval_constant (q:(num#num)#num) =
    (candle_fs_of_q_lower q,candle_fs_of_q_upper q)`;;

let candle_fs_interval_neg_def = new_definition
 `candle_fs_interval_neg (i:(num#num)#(num#num)) =
    (candle_fs_raw_neg (SND i),candle_fs_raw_neg (FST i))`;;

let candle_fs_interval_add_def = new_definition
 `candle_fs_interval_add (x:(num#num)#(num#num)) y =
    (candle_fs_add (FST x) (FST y),
     candle_fs_add (SND x) (SND y))`;;

let candle_fs_raw_interval_neg_def = new_definition
 `candle_fs_raw_interval_neg (i:(num#num)#(num#num)) =
    (candle_fs_raw_neg (SND i),candle_fs_raw_neg (FST i))`;;

let candle_fs_raw_interval_add_def = new_definition
 `candle_fs_raw_interval_add (x:(num#num)#(num#num)) y =
    (candle_lc_zadd (FST x) (FST y),
     candle_lc_zadd (SND x) (SND y))`;;

let candle_fs_raw_interval_mul_def = new_definition
 `candle_fs_raw_interval_mul (x:(num#num)#(num#num)) y =
    (candle_fs_raw_min
      (candle_fs_raw_min
        (candle_q_zmul (FST x) (FST y))
        (candle_q_zmul (FST x) (SND y)))
      (candle_fs_raw_min
        (candle_q_zmul (SND x) (FST y))
        (candle_q_zmul (SND x) (SND y))),
     candle_fs_raw_max
      (candle_fs_raw_max
        (candle_q_zmul (FST x) (FST y))
        (candle_q_zmul (FST x) (SND y)))
      (candle_fs_raw_max
        (candle_q_zmul (SND x) (FST y))
        (candle_q_zmul (SND x) (SND y))))`;;

let candle_fs_raw_interval_round_def = new_definition
 `candle_fs_raw_interval_round denominator
    (i:(num#num)#(num#num)) =
    (candle_fs_floor_div (FST i) denominator,
     candle_fs_ceil_div (SND i) denominator)`;;

let candle_fs_interval_abs_upper_def = new_definition
 `candle_fs_interval_abs_upper (i:(num#num)#(num#num)) =
    candle_fs_raw_max
      (candle_fs_raw_abs (FST i))
      (candle_fs_raw_abs (SND i))`;;

let candle_fs_interval_contains_def = new_definition
 `candle_fs_interval_contains (i:(num#num)#(num#num)) (x:real) <=>
    candle_fs_real (FST i) <= x /\ x <= candle_fs_real (SND i)`;;

let candle_fs_raw_interval_contains_def = new_definition
 `candle_fs_raw_interval_contains denominator
    (i:(num#num)#(num#num)) (x:real) <=>
    candle_fs_raw_real denominator (FST i) <= x /\
    x <= candle_fs_raw_real denominator (SND i)`;;

let candle_cv_fs_interval_list_def = define
 `(candle_cv_fs_interval_list [] = Cexp_num 0) /\
  (candle_cv_fs_interval_list (CONS h t) =
     Cexp_pair (candle_cv_fs_interval h)
       (candle_cv_fs_interval_list t))`;;

let candle_cv_fs_interval_matrix_def = define
 `(candle_cv_fs_interval_matrix [] = Cexp_num 0) /\
  (candle_cv_fs_interval_matrix (CONS h t) =
     Cexp_pair (candle_cv_fs_interval_list h)
       (candle_cv_fs_interval_matrix t))`;;

let candle_fs_interval_lookup_def = define
 `(candle_fs_interval_lookup variable
     ([]:((num#num)#(num#num))list) = candle_fs_interval_zero) /\
  (candle_fs_interval_lookup 0 (CONS h t) = h) /\
  (candle_fs_interval_lookup (SUC n) (CONS h t) =
     candle_fs_interval_lookup n t)`;;

let candle_fs_interval_zeros_def = define
 `(candle_fs_interval_zeros
     ([]:((num#num)#(num#num))list) = []) /\
  (candle_fs_interval_zeros (CONS h t) =
     CONS candle_fs_interval_zero (candle_fs_interval_zeros t))`;;

let candle_fs_interval_unit_def = define
 `(candle_fs_interval_unit variable
     ([]:((num#num)#(num#num))list) = []) /\
  (candle_fs_interval_unit 0 (CONS h t) =
     CONS candle_fs_interval_one (candle_fs_interval_zeros t)) /\
  (candle_fs_interval_unit (SUC n) (CONS h t) =
     CONS candle_fs_interval_zero (candle_fs_interval_unit n t))`;;

let candle_fs_interval_zero_matrix_def = define
 `(candle_fs_interval_zero_matrix width [] = []) /\
  (candle_fs_interval_zero_matrix width (CONS h t) =
     CONS (candle_fs_interval_zeros width)
       (candle_fs_interval_zero_matrix width t))`;;

let candle_fs_interval_list_of_q_def = define
 `(candle_fs_interval_list_of_q
     ([]:(((num#num)#num)#((num#num)#num))list) = []) /\
  (candle_fs_interval_list_of_q (CONS h t) =
     CONS (candle_fs_interval_of_q h)
       (candle_fs_interval_list_of_q t))`;;

let candle_fs_list_of_q_def = define
 `(candle_fs_list_of_q ([]:((num#num)#num)list) = []) /\
  (candle_fs_list_of_q (CONS h t) =
     CONS (FST h) (candle_fs_list_of_q t))`;;

let candle_fs_interval_list_neg_def = define
 `(candle_fs_interval_list_neg
     ([]:((num#num)#(num#num))list) = []) /\
  (candle_fs_interval_list_neg (CONS h t) =
     CONS (candle_fs_interval_neg h)
       (candle_fs_interval_list_neg t))`;;

let candle_fs_interval_list_add_def = define
 `(candle_fs_interval_list_add
     ([]:((num#num)#(num#num))list) ys = []) /\
  (candle_fs_interval_list_add (CONS x xs) [] = []) /\
  (candle_fs_interval_list_add (CONS x xs) (CONS y ys) =
     CONS (candle_fs_interval_add x y)
       (candle_fs_interval_list_add xs ys))`;;

let candle_fs_interval_matrix_neg_def = define
 `(candle_fs_interval_matrix_neg [] = []) /\
  (candle_fs_interval_matrix_neg (CONS h t) =
     CONS (candle_fs_interval_list_neg h)
       (candle_fs_interval_matrix_neg t))`;;

let candle_fs_interval_matrix_add_def = define
 `(candle_fs_interval_matrix_add [] ys = []) /\
  (candle_fs_interval_matrix_add (CONS x xs) [] = []) /\
  (candle_fs_interval_matrix_add (CONS x xs) (CONS y ys) =
     CONS (candle_fs_interval_list_add x y)
       (candle_fs_interval_matrix_add xs ys))`;;

let candle_fs_raw_interval_list_add_def = define
 `(candle_fs_raw_interval_list_add [] ys = []) /\
  (candle_fs_raw_interval_list_add (CONS x xs) [] = []) /\
  (candle_fs_raw_interval_list_add (CONS x xs) (CONS y ys) =
     CONS (candle_fs_raw_interval_add x y)
       (candle_fs_raw_interval_list_add xs ys))`;;

let candle_fs_raw_interval_list_scale_def = define
 `(candle_fs_raw_interval_list_scale scalar [] = []) /\
  (candle_fs_raw_interval_list_scale scalar (CONS h t) =
     CONS (candle_fs_raw_interval_mul scalar h)
       (candle_fs_raw_interval_list_scale scalar t))`;;

let candle_fs_raw_interval_matrix_add_def = define
 `(candle_fs_raw_interval_matrix_add [] ys = []) /\
  (candle_fs_raw_interval_matrix_add (CONS x xs) [] = []) /\
  (candle_fs_raw_interval_matrix_add (CONS x xs) (CONS y ys) =
     CONS (candle_fs_raw_interval_list_add x y)
       (candle_fs_raw_interval_matrix_add xs ys))`;;

let candle_fs_raw_interval_matrix_scale_def = define
 `(candle_fs_raw_interval_matrix_scale scalar [] = []) /\
  (candle_fs_raw_interval_matrix_scale scalar (CONS h t) =
     CONS (candle_fs_raw_interval_list_scale scalar h)
       (candle_fs_raw_interval_matrix_scale scalar t))`;;

let candle_fs_raw_interval_outer_def = define
 `(candle_fs_raw_interval_outer [] ys = []) /\
  (candle_fs_raw_interval_outer (CONS x xs) ys =
     CONS (candle_fs_raw_interval_list_scale x ys)
       (candle_fs_raw_interval_outer xs ys))`;;

let candle_fs_raw_interval_list_round_def = define
 `(candle_fs_raw_interval_list_round denominator [] = []) /\
  (candle_fs_raw_interval_list_round denominator (CONS h t) =
     CONS (candle_fs_raw_interval_round denominator h)
       (candle_fs_raw_interval_list_round denominator t))`;;

let candle_fs_raw_interval_matrix_round_def = define
 `(candle_fs_raw_interval_matrix_round denominator [] = []) /\
  (candle_fs_raw_interval_matrix_round denominator (CONS h t) =
     CONS (candle_fs_raw_interval_list_round denominator h)
       (candle_fs_raw_interval_matrix_round denominator t))`;;

let candle_fs_dot_abs_upper_def = define
 `(candle_fs_dot_abs_upper ([]:(num#num)list) ys = (0,0)) /\
  (candle_fs_dot_abs_upper (CONS x xs) [] = (0,0)) /\
  (candle_fs_dot_abs_upper (CONS x xs) (CONS y ys) =
     candle_lc_zadd
       (candle_q_zmul x (candle_fs_interval_abs_upper y))
       (candle_fs_dot_abs_upper xs ys))`;;

let candle_fs_weighted_rows_abs_upper_def = define
 `(candle_fs_weighted_rows_abs_upper radii [] row_lists = (0,0)) /\
  (candle_fs_weighted_rows_abs_upper radii (CONS w ws) [] = (0,0)) /\
  (candle_fs_weighted_rows_abs_upper
     radii (CONS w ws) (CONS interval_row row_tail) =
     candle_lc_zadd
       (candle_q_zmul w (candle_fs_dot_abs_upper radii interval_row))
       (candle_fs_weighted_rows_abs_upper radii ws row_tail))`;;

let candle_fs_first_make_def = new_definition
 `candle_fs_first_make value gradient = (value,gradient)`;;

let candle_fs_first_value_def = new_definition
 `candle_fs_first_value first = FST first`;;

let candle_fs_first_gradient_def = new_definition
 `candle_fs_first_gradient first = SND first`;;

let candle_cv_fs_first_def = new_definition
 `candle_cv_fs_first first =
    Cexp_pair (candle_cv_fs_interval (candle_fs_first_value first))
      (candle_cv_fs_interval_list (candle_fs_first_gradient first))`;;

let candle_fs_result_make_def = new_definition
 `candle_fs_result_make domain center value_bound gradient_bounds hessian =
    (domain,(center,(value_bound,(gradient_bounds,hessian))))`;;

let candle_fs_result_domain_def = new_definition
 `candle_fs_result_domain result = FST result`;;

let candle_fs_result_center_def = new_definition
 `candle_fs_result_center result = FST (SND result)`;;

let candle_fs_result_value_bound_def = new_definition
 `candle_fs_result_value_bound result = FST (SND (SND result))`;;

let candle_fs_result_gradient_bounds_def = new_definition
 `candle_fs_result_gradient_bounds result =
    FST (SND (SND (SND result)))`;;

let candle_fs_result_hessian_def = new_definition
 `candle_fs_result_hessian result = SND (SND (SND (SND result)))`;;

let candle_cv_fs_result_def = new_definition
 `candle_cv_fs_result result =
    candle_cv_fs_result_make
      (candle_cv_bool (candle_fs_result_domain result))
      (candle_cv_fs_first (candle_fs_result_center result))
      (candle_cv_fs_interval (candle_fs_result_value_bound result))
      (candle_cv_fs_interval_list
        (candle_fs_result_gradient_bounds result))
      (candle_cv_fs_interval_matrix (candle_fs_result_hessian result))`;;

let candle_cv_fs_result_list_def = define
 `(candle_cv_fs_result_list [] = Cexp_num 0) /\
  (candle_cv_fs_result_list (CONS h t) =
     Cexp_pair (candle_cv_fs_result h) (candle_cv_fs_result_list t))`;;

let candle_fs_gradient_bounds_def = define
 `(candle_fs_gradient_bounds radii [] row_lists = []) /\
  (candle_fs_gradient_bounds radii (CONS g gs) [] = []) /\
  (candle_fs_gradient_bounds radii (CONS g gs)
      (CONS interval_row row_lists) =
     CONS
       (candle_fs_raw_interval_round candle_fs_scale
         (candle_fs_raw_interval_add
           (candle_lc_zscale candle_fs_scale (FST g),
            candle_lc_zscale candle_fs_scale (SND g))
           (candle_fs_raw_neg
              (candle_fs_dot_abs_upper radii interval_row),
            candle_fs_dot_abs_upper radii interval_row)))
       (candle_fs_gradient_bounds radii gs row_lists))`;;

let candle_fs_result_complete_rounded_def = new_definition
 `candle_fs_result_complete_rounded radii domain center hessian =
    candle_fs_result_make domain center
      (candle_fs_raw_interval_round candle_fs_two_scale_squared
        (candle_fs_raw_interval_add
          (candle_lc_zscale candle_fs_two_scale_squared
             (FST (candle_fs_first_value center)),
           candle_lc_zscale candle_fs_two_scale_squared
             (SND (candle_fs_first_value center)))
          (candle_fs_raw_neg
             (candle_lc_zadd
               (candle_lc_zscale (2 * candle_fs_scale)
                 (candle_fs_dot_abs_upper radii
                   (candle_fs_first_gradient center)))
               (candle_fs_weighted_rows_abs_upper radii radii hessian)),
           candle_lc_zadd
             (candle_lc_zscale (2 * candle_fs_scale)
               (candle_fs_dot_abs_upper radii
                 (candle_fs_first_gradient center)))
             (candle_fs_weighted_rows_abs_upper radii radii hessian))))
      (candle_fs_gradient_bounds
        radii (candle_fs_first_gradient center) hessian)
      hessian`;;

let candle_fs_result_complete_raw_def = new_definition
 `candle_fs_result_complete_raw radii domain raw_center raw_hessian =
    candle_fs_result_complete_rounded radii domain
      (candle_fs_first_make
        (candle_fs_raw_interval_round candle_fs_scale
          (candle_fs_first_value raw_center))
        (candle_fs_raw_interval_list_round candle_fs_scale
          (candle_fs_first_gradient raw_center)))
      (candle_fs_raw_interval_matrix_round
        candle_fs_scale raw_hessian)`;;

let candle_fs_result_zero_def = new_definition
 `candle_fs_result_zero dimensions =
    candle_fs_result_complete_rounded [] F
      (candle_fs_first_make candle_fs_interval_zero
        (candle_fs_interval_zeros dimensions))
      (candle_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_fs_result_head_def = define
 `(candle_fs_result_head dimensions [] =
     candle_fs_result_zero dimensions) /\
  (candle_fs_result_head dimensions (CONS h t) = h)`;;

let candle_fs_result_tail_def = define
 `(candle_fs_result_tail [] = []) /\
  (candle_fs_result_tail (CONS h t) = t)`;;

let candle_fs_result_constant_def = new_definition
 `candle_fs_result_constant dimensions radii q =
    candle_fs_result_complete_rounded radii T
      (candle_fs_first_make
        (candle_fs_interval_constant q)
        (candle_fs_interval_zeros dimensions))
      (candle_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_fs_result_variable_def = new_definition
 `candle_fs_result_variable dimensions radii variable =
    candle_fs_result_complete_rounded radii T
      (candle_fs_first_make
        (candle_fs_interval_lookup variable dimensions)
        (candle_fs_interval_unit variable dimensions))
      (candle_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_fs_result_neg_def = new_definition
 `candle_fs_result_neg radii result =
    candle_fs_result_complete_rounded radii
      (candle_fs_result_domain result)
      (candle_fs_first_make
        (candle_fs_interval_neg
          (candle_fs_first_value (candle_fs_result_center result)))
        (candle_fs_interval_list_neg
          (candle_fs_first_gradient (candle_fs_result_center result))))
      (candle_fs_interval_matrix_neg
        (candle_fs_result_hessian result))`;;

let candle_fs_result_add_def = new_definition
 `candle_fs_result_add radii left right =
    candle_fs_result_complete_rounded radii
      (candle_fs_result_domain left /\ candle_fs_result_domain right)
      (candle_fs_first_make
        (candle_fs_interval_add
          (candle_fs_first_value (candle_fs_result_center left))
          (candle_fs_first_value (candle_fs_result_center right)))
        (candle_fs_interval_list_add
          (candle_fs_first_gradient (candle_fs_result_center left))
          (candle_fs_first_gradient (candle_fs_result_center right))))
      (candle_fs_interval_matrix_add
        (candle_fs_result_hessian left)
        (candle_fs_result_hessian right))`;;

let candle_fs_result_mul_def = new_definition
 `candle_fs_result_mul radii left right =
    candle_fs_result_complete_raw radii
      (candle_fs_result_domain left /\ candle_fs_result_domain right)
      (candle_fs_first_make
        (candle_fs_raw_interval_mul
          (candle_fs_first_value (candle_fs_result_center left))
          (candle_fs_first_value (candle_fs_result_center right)))
        (candle_fs_raw_interval_list_add
          (candle_fs_raw_interval_list_scale
            (candle_fs_first_value (candle_fs_result_center right))
            (candle_fs_first_gradient (candle_fs_result_center left)))
          (candle_fs_raw_interval_list_scale
            (candle_fs_first_value (candle_fs_result_center left))
            (candle_fs_first_gradient (candle_fs_result_center right)))))
      (candle_fs_raw_interval_matrix_add
        (candle_fs_raw_interval_matrix_add
          (candle_fs_raw_interval_matrix_scale
            (candle_fs_result_value_bound right)
            (candle_fs_result_hessian left))
          (candle_fs_raw_interval_outer
            (candle_fs_result_gradient_bounds left)
            (candle_fs_result_gradient_bounds right)))
        (candle_fs_raw_interval_matrix_add
          (candle_fs_raw_interval_outer
            (candle_fs_result_gradient_bounds right)
            (candle_fs_result_gradient_bounds left))
          (candle_fs_raw_interval_matrix_scale
            (candle_fs_result_value_bound left)
            (candle_fs_result_hessian right))))`;;

let candle_fs_result_square_def = new_definition
 `candle_fs_result_square radii result =
    candle_fs_result_mul radii result result`;;

let candle_fs_poly_step_def = define
 `(candle_fs_poly_step dimensions radii
      (Candle_q_push p n d) stack =
     CONS
       (candle_fs_result_constant dimensions radii ((p,n),d)) stack) /\
  (candle_fs_poly_step dimensions radii
      (Candle_q_load variable) stack =
     CONS
       (candle_fs_result_variable dimensions radii variable) stack) /\
  (candle_fs_poly_step dimensions radii Candle_q_neg stack =
     CONS
       (candle_fs_result_neg radii
         (candle_fs_result_head dimensions stack))
       (candle_fs_result_tail stack)) /\
  (candle_fs_poly_step dimensions radii Candle_q_add stack =
     CONS
       (candle_fs_result_add radii
         (candle_fs_result_head dimensions
           (candle_fs_result_tail stack))
         (candle_fs_result_head dimensions stack))
       (candle_fs_result_tail (candle_fs_result_tail stack))) /\
  (candle_fs_poly_step dimensions radii Candle_q_mul stack =
     CONS
       (candle_fs_result_mul radii
         (candle_fs_result_head dimensions
           (candle_fs_result_tail stack))
         (candle_fs_result_head dimensions stack))
       (candle_fs_result_tail (candle_fs_result_tail stack))) /\
  (candle_fs_poly_step dimensions radii Candle_q_square stack =
     CONS
       (candle_fs_result_square radii
         (candle_fs_result_head dimensions stack))
       (candle_fs_result_tail stack))`;;

let candle_fs_poly_run_def = define
 `(candle_fs_poly_run dimensions radii [] stack = stack) /\
  (candle_fs_poly_run dimensions radii (CONS h t) stack =
     candle_fs_poly_run dimensions radii t
       (candle_fs_poly_step dimensions radii h stack))`;;

let candle_fs_poly_program_fixed_def = new_definition
 `candle_fs_poly_program_fixed dimensions radii program =
    candle_fs_result_head dimensions
      (candle_fs_poly_run dimensions radii program [])`;;

let candle_fs_poly_program_def = new_definition
 `candle_fs_poly_program center_boxes radii program =
    candle_fs_poly_program_fixed
      (candle_fs_interval_list_of_q center_boxes)
      (candle_fs_list_of_q radii) program`;;

(* The conversion is outside the hot arithmetic path.  It gives the fixed
   result the established ordinary rational Taylor-model interface used by
   the universal analytic invariant.  The whole-box Hessian is also a valid
   center Hessian enclosure, and the executable first-jet encoding erases
   this otherwise unobservable component. *)

let candle_fs_interval_to_q_def = new_definition
 `candle_fs_interval_to_q (i:(num#num)#(num#num)) =
    (candle_fs_to_q (FST i),candle_fs_to_q (SND i))`;;

let candle_fs_interval_list_to_q_def = define
 `(candle_fs_interval_list_to_q
     ([]:((num#num)#(num#num))list) = []) /\
  (candle_fs_interval_list_to_q (CONS h t) =
     CONS (candle_fs_interval_to_q h)
       (candle_fs_interval_list_to_q t))`;;

let candle_fs_interval_matrix_to_q_def = define
 `(candle_fs_interval_matrix_to_q
     ([]:(((num#num)#(num#num))list)list) = []) /\
  (candle_fs_interval_matrix_to_q (CONS h t) =
     CONS (candle_fs_interval_list_to_q h)
       (candle_fs_interval_matrix_to_q t))`;;

let candle_fs_first_to_q_def = new_definition
 `candle_fs_first_to_q first hessian =
    candle_q_dim_jet_make
      (candle_fs_interval_to_q (candle_fs_first_value first))
      (candle_fs_interval_list_to_q (candle_fs_first_gradient first))
      (candle_fs_interval_matrix_to_q hessian)`;;

let candle_fs_result_to_q_def = new_definition
 `candle_fs_result_to_q result =
    candle_q_dim_taylor_model_result_make
      (candle_fs_result_domain result)
      (candle_fs_first_to_q
        (candle_fs_result_center result)
        (candle_fs_result_hessian result))
      (candle_fs_interval_to_q (candle_fs_result_value_bound result))
      (candle_fs_interval_list_to_q
        (candle_fs_result_gradient_bounds result))
      (candle_fs_interval_matrix_to_q
        (candle_fs_result_hessian result))`;;

let candle_fs_poly_program_to_q_def = new_definition
 `candle_fs_poly_program_to_q center_boxes radii program =
    candle_fs_result_to_q
      (candle_fs_poly_program center_boxes radii program)`;;

(* -------------------------------------------------------------------------- *)
(* Computed-value representation theorems.                                    *)
(* -------------------------------------------------------------------------- *)

let candle_cv_fs_scale_correct = prove
 (`candle_cv_fs_scale = Cexp_num candle_fs_scale`,
  REWRITE_TAC[candle_cv_fs_scale_def; candle_fs_scale_def]);;

let candle_cv_fs_scale_squared_correct = prove
 (`candle_cv_fs_scale_squared = Cexp_num candle_fs_scale_squared`,
  REWRITE_TAC[candle_cv_fs_scale_squared_def;
              candle_fs_scale_squared_def;
              candle_cv_fs_scale_correct; cexp_mul_def]);;

let candle_cv_fs_two_scale_squared_correct = prove
 (`candle_cv_fs_two_scale_squared =
   Cexp_num candle_fs_two_scale_squared`,
  REWRITE_TAC[candle_cv_fs_two_scale_squared_def;
              candle_fs_two_scale_squared_def;
              candle_cv_fs_scale_squared_correct; cexp_mul_def]);;

let candle_cv_fs_zero_correct = prove
 (`candle_cv_fs_zero = candle_cv_lc_z (0,0)`,
  REWRITE_TAC[candle_cv_fs_zero_def; candle_cv_lc_z_def; FST; SND]);;

let candle_cv_fs_one_correct = prove
 (`candle_cv_fs_one = candle_cv_lc_z (candle_fs_scale,0)`,
  REWRITE_TAC[candle_cv_fs_one_def; candle_cv_fs_scale_correct;
              candle_cv_lc_z_def; FST; SND]);;

let candle_cv_fs_raw_add_correct = prove
 (`!x y.
     candle_cv_fs_raw_add (candle_cv_lc_z x) (candle_cv_lc_z y) =
     candle_cv_lc_z (candle_lc_zadd x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_add_def; candle_cv_lc_z_def;
              candle_lc_zadd_def; cexp_fst_def; cexp_snd_def;
              cexp_add_def; FST; SND]);;

let candle_cv_fs_raw_neg_correct = prove
 (`!z.
     candle_cv_fs_raw_neg (candle_cv_lc_z z) =
     candle_cv_lc_z (candle_fs_raw_neg z)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_neg_def; candle_cv_lc_z_def;
              candle_fs_raw_neg_def; cexp_fst_def; cexp_snd_def;
              FST; SND]);;

let candle_cv_fs_raw_mul_correct = prove
 (`!x y.
     candle_cv_fs_raw_mul (candle_cv_lc_z x) (candle_cv_lc_z y) =
     candle_cv_lc_z (candle_q_zmul x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_mul_def; candle_cv_lc_z_def;
              candle_q_zmul_def; cexp_fst_def; cexp_snd_def;
              cexp_add_def; cexp_mul_def; FST; SND]);;

let candle_cv_fs_raw_scale_correct = prove
 (`!factor z.
     candle_cv_fs_raw_scale (Cexp_num factor) (candle_cv_lc_z z) =
     candle_cv_lc_z (candle_lc_zscale factor z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_scale_def; candle_cv_lc_z_def;
              candle_lc_zscale_def; cexp_fst_def; cexp_snd_def;
              cexp_mul_def; FST; SND]);;

let candle_cv_fs_canonical_correct = prove
 (`!z.
     candle_cv_fs_canonical (candle_cv_lc_z z) =
     candle_cv_lc_z (candle_fs_canonical z)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_canonical_def; candle_fs_canonical_def;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              cexp_less_def; FST; SND] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_sub_def]);;

let candle_cv_fs_add_correct = prove
 (`!x y.
     candle_cv_fs_add (candle_cv_lc_z x) (candle_cv_lc_z y) =
     candle_cv_lc_z (candle_fs_add x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_add_def; candle_fs_add_def;
              candle_cv_fs_raw_add_correct;
              candle_cv_fs_canonical_correct]);;

let candle_cv_fs_neg_correct = prove
 (`!z.
     candle_cv_fs_neg (candle_cv_lc_z z) =
     candle_cv_lc_z (candle_fs_raw_neg z)`,
  REWRITE_TAC[candle_cv_fs_neg_def; candle_cv_fs_raw_neg_correct]);;

let candle_cv_fs_floor_div_correct = prove
 (`!z denominator.
     candle_cv_fs_floor_div
       (candle_cv_lc_z z) (Cexp_num denominator) =
     candle_cv_lc_z (candle_fs_floor_div z denominator)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_floor_div_def; candle_fs_floor_div_def;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              cexp_less_def; FST; SND] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_sub_def; cexp_div_def;
                  candle_cv_q_ceil_div_correct]);;

let candle_cv_fs_ceil_div_correct = prove
 (`!z denominator.
     candle_cv_fs_ceil_div
       (candle_cv_lc_z z) (Cexp_num denominator) =
     candle_cv_lc_z (candle_fs_ceil_div z denominator)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_ceil_div_def; candle_fs_ceil_div_def;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              cexp_less_def; FST; SND] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; cexp_sub_def; cexp_div_def;
                  candle_cv_q_ceil_div_correct]);;

let candle_cv_fs_to_q_correct = prove
 (`!z.
     candle_cv_fs_to_q (candle_cv_lc_z z) =
     candle_cv_q (candle_fs_to_q z)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_to_q_def; candle_fs_to_q_def;
              candle_cv_q_def; candle_cv_fs_scale_correct;
              candle_cv_lc_z_def; candle_fs_scale_def;
              cexp_sub_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_fs_raw_le_correct = prove
 (`!x y.
     candle_cv_fs_raw_le (candle_cv_lc_z x) (candle_cv_lc_z y) =
     Cexp_num (if candle_fs_raw_le x y then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_le_def; candle_fs_raw_le_def;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              cexp_add_def; cexp_less_def; FST; SND;
              GSYM ADD1; LT_SUC_LE]);;

let candle_cv_fs_raw_min_correct = prove
 (`!x y.
     candle_cv_fs_raw_min (candle_cv_lc_z x) (candle_cv_lc_z y) =
     candle_cv_lc_z (candle_fs_raw_min x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_min_def; candle_fs_raw_min_def;
              candle_cv_fs_raw_le_correct] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]);;

let candle_cv_fs_raw_max_correct = prove
 (`!x y.
     candle_cv_fs_raw_max (candle_cv_lc_z x) (candle_cv_lc_z y) =
     candle_cv_lc_z (candle_fs_raw_max x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_max_def; candle_fs_raw_max_def;
              candle_cv_fs_raw_le_correct] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]);;

let candle_cv_fs_raw_abs_correct = prove
 (`!z.
     candle_cv_fs_raw_abs (candle_cv_lc_z z) =
     candle_cv_lc_z (candle_fs_raw_abs z)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_abs_def; candle_fs_raw_abs_def;
              candle_cv_fs_raw_neg_correct;
              candle_cv_fs_raw_max_correct]);;

let candle_cv_fs_of_q_lower_correct = prove
 (`!q.
     candle_cv_fs_of_q_lower (candle_cv_q q) =
     candle_cv_lc_z (candle_fs_of_q_lower q)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_of_q_lower_def; candle_fs_of_q_lower_def;
              candle_cv_q_fixed_round_lower_correct;
              candle_cv_q_def; cexp_fst_def]);;

let candle_cv_fs_of_q_upper_correct = prove
 (`!q.
     candle_cv_fs_of_q_upper (candle_cv_q q) =
     candle_cv_lc_z (candle_fs_of_q_upper q)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_of_q_upper_def; candle_fs_of_q_upper_def;
              candle_cv_q_fixed_round_upper_correct;
              candle_cv_q_def; cexp_fst_def]);;

let candle_cv_fs_interval_zero_correct = prove
 (`candle_cv_fs_interval_zero =
   candle_cv_fs_interval candle_fs_interval_zero`,
  REWRITE_TAC[candle_cv_fs_interval_zero_def;
              candle_fs_interval_zero_def; candle_cv_fs_interval_def;
              candle_cv_fs_zero_correct; FST; SND]);;

let candle_cv_fs_interval_one_correct = prove
 (`candle_cv_fs_interval_one =
   candle_cv_fs_interval candle_fs_interval_one`,
  REWRITE_TAC[candle_cv_fs_interval_one_def;
              candle_fs_interval_one_def; candle_cv_fs_interval_def;
              candle_cv_fs_one_correct; FST; SND]);;

let candle_cv_fs_interval_of_q_correct = prove
 (`!i.
     candle_cv_fs_interval_of_q (candle_cv_q_interval i) =
     candle_cv_fs_interval (candle_fs_interval_of_q i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_interval_of_q_def;
              candle_fs_interval_of_q_def;
              candle_cv_q_interval_def; candle_cv_fs_interval_def;
              cexp_fst_def; cexp_snd_def;
              candle_cv_fs_of_q_lower_correct;
              candle_cv_fs_of_q_upper_correct; FST; SND]);;

let candle_cv_fs_interval_constant_correct = prove
 (`!q.
     candle_cv_fs_interval_constant (candle_cv_q q) =
     candle_cv_fs_interval (candle_fs_interval_constant q)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_interval_constant_def;
              candle_fs_interval_constant_def;
              candle_cv_fs_interval_def;
              candle_cv_fs_of_q_lower_correct;
              candle_cv_fs_of_q_upper_correct; FST; SND]);;

let candle_cv_fs_interval_neg_correct = prove
 (`!i.
     candle_cv_fs_interval_neg (candle_cv_fs_interval i) =
     candle_cv_fs_interval (candle_fs_interval_neg i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_interval_neg_def;
              candle_fs_interval_neg_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_neg_correct; FST; SND]);;

let candle_cv_fs_interval_add_correct = prove
 (`!x y.
     candle_cv_fs_interval_add
       (candle_cv_fs_interval x) (candle_cv_fs_interval y) =
     candle_cv_fs_interval (candle_fs_interval_add x y)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_interval_add_def;
              candle_fs_interval_add_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_add_correct; FST; SND]);;

let candle_cv_fs_raw_interval_neg_correct = prove
 (`!i.
     candle_cv_fs_raw_interval_neg (candle_cv_fs_interval i) =
     candle_cv_fs_interval (candle_fs_raw_interval_neg i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_neg_def;
              candle_fs_raw_interval_neg_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_raw_neg_correct; FST; SND]);;

let candle_cv_fs_raw_interval_add_correct = prove
 (`!x y.
     candle_cv_fs_raw_interval_add
       (candle_cv_fs_interval x) (candle_cv_fs_interval y) =
     candle_cv_fs_interval (candle_fs_raw_interval_add x y)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_add_def;
              candle_fs_raw_interval_add_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_raw_add_correct; FST; SND]);;

let candle_cv_fs_raw_interval_mul_correct = prove
 (`!x y.
     candle_cv_fs_raw_interval_mul
       (candle_cv_fs_interval x) (candle_cv_fs_interval y) =
     candle_cv_fs_interval (candle_fs_raw_interval_mul x y)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_mul_def;
              candle_fs_raw_interval_mul_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_raw_mul_correct;
              candle_cv_fs_raw_min_correct;
              candle_cv_fs_raw_max_correct; FST; SND]);;

let candle_cv_fs_raw_interval_round_correct = prove
 (`!denominator i.
     candle_cv_fs_raw_interval_round
       (Cexp_num denominator) (candle_cv_fs_interval i) =
     candle_cv_fs_interval (candle_fs_raw_interval_round denominator i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_raw_interval_round_def;
              candle_fs_raw_interval_round_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_floor_div_correct;
              candle_cv_fs_ceil_div_correct; FST; SND]);;

let candle_cv_fs_interval_abs_upper_correct = prove
 (`!i.
     candle_cv_fs_interval_abs_upper (candle_cv_fs_interval i) =
     candle_cv_lc_z (candle_fs_interval_abs_upper i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_interval_abs_upper_def;
              candle_fs_interval_abs_upper_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_raw_abs_correct;
              candle_cv_fs_raw_max_correct; FST; SND]);;

let candle_cv_fs_interval_fst_correct = prove
 (`!i. Cexp_fst (candle_cv_fs_interval i) =
       candle_cv_lc_z (FST i)`,
  REWRITE_TAC[candle_cv_fs_interval_def; cexp_fst_def]);;

let candle_cv_fs_interval_snd_correct = prove
 (`!i. Cexp_snd (candle_cv_fs_interval i) =
       candle_cv_lc_z (SND i)`,
  REWRITE_TAC[candle_cv_fs_interval_def; cexp_snd_def]);;

let candle_cv_fs_interval_pair_correct = prove
 (`!lower upper.
     Cexp_pair (candle_cv_lc_z lower) (candle_cv_lc_z upper) =
     candle_cv_fs_interval (lower,upper)`,
  REWRITE_TAC[candle_cv_fs_interval_def; FST; SND]);;

let candle_cv_fs_interval_lookup_correct = prove
 (`!variable items.
     candle_cv_fs_interval_lookup (Cexp_num variable)
       (candle_cv_fs_interval_list items) =
     candle_cv_fs_interval (candle_fs_interval_lookup variable items)`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_lookup_def;
                  candle_cv_fs_interval_list_def;
                  candle_fs_interval_lookup_def;
                  candle_cv_fs_interval_zero_correct]);;

let candle_cv_fs_interval_zeros_correct = prove
 (`!items.
     candle_cv_fs_interval_zeros (candle_cv_fs_interval_list items) =
     candle_cv_fs_interval_list (candle_fs_interval_zeros items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_zeros_def;
                  candle_cv_fs_interval_list_def;
                  candle_fs_interval_zeros_def;
                  candle_cv_fs_interval_zero_correct]);;

let candle_cv_fs_interval_unit_correct = prove
 (`!variable items.
     candle_cv_fs_interval_unit (Cexp_num variable)
       (candle_cv_fs_interval_list items) =
     candle_cv_fs_interval_list (candle_fs_interval_unit variable items)`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_unit_def;
                  candle_cv_fs_interval_list_def;
                  candle_fs_interval_unit_def;
                  candle_cv_fs_interval_zeros_correct;
                  candle_cv_fs_interval_zero_correct;
                  candle_cv_fs_interval_one_correct]);;

let candle_cv_fs_interval_zero_matrix_correct = prove
 (`!width rows.
     candle_cv_fs_interval_zero_matrix
       (candle_cv_fs_interval_list width)
       (candle_cv_fs_interval_matrix rows) =
     candle_cv_fs_interval_matrix
       (candle_fs_interval_zero_matrix width rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_zero_matrix_def;
                  candle_cv_fs_interval_list_def;
                  candle_cv_fs_interval_matrix_def;
                  candle_fs_interval_zero_matrix_def;
                  candle_cv_fs_interval_zeros_correct]);;

let candle_cv_fs_interval_zero_matrix_like_correct = prove
 (`!width dimensions.
     candle_cv_fs_interval_zero_matrix
       (candle_cv_fs_interval_list width)
       (candle_cv_fs_interval_list dimensions) =
     candle_cv_fs_interval_matrix
       (candle_fs_interval_zero_matrix width dimensions)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_zero_matrix_def;
                  candle_cv_fs_interval_list_def;
                  candle_cv_fs_interval_matrix_def;
                  candle_fs_interval_zero_matrix_def;
                  candle_cv_fs_interval_zeros_correct]);;

let candle_cv_fs_interval_list_of_q_correct = prove
 (`!items.
     candle_cv_fs_interval_list_of_q (candle_cv_q_interval_list items) =
     candle_cv_fs_interval_list (candle_fs_interval_list_of_q items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_list_of_q_def;
                  candle_cv_q_interval_list_def;
                  candle_cv_fs_interval_list_def;
                  candle_fs_interval_list_of_q_def;
                  candle_cv_fs_interval_of_q_correct]);;

let candle_cv_fs_list_of_q_correct = prove
 (`!items.
     candle_cv_fs_list_of_q (candle_cv_q_list items) =
     candle_cv_lc_vec (candle_fs_list_of_q items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_list_of_q_def;
                  candle_cv_q_list_def; candle_cv_lc_vec_def;
                  candle_cv_q_def; candle_fs_list_of_q_def;
                  cexp_fst_def]);;

let candle_cv_fs_interval_list_neg_correct = prove
 (`!items.
     candle_cv_fs_interval_list_neg (candle_cv_fs_interval_list items) =
     candle_cv_fs_interval_list (candle_fs_interval_list_neg items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_list_neg_def;
                  candle_cv_fs_interval_list_def;
                  candle_fs_interval_list_neg_def;
                  candle_cv_fs_interval_neg_correct]);;

let candle_cv_fs_interval_list_add_correct = prove
 (`!xs ys.
     candle_cv_fs_interval_list_add
       (candle_cv_fs_interval_list xs) (candle_cv_fs_interval_list ys) =
     candle_cv_fs_interval_list (candle_fs_interval_list_add xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_fs_interval_list_def;
                candle_cv_fs_interval_list_add_def;
                candle_fs_interval_list_add_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_fs_interval_list_def;
                    candle_cv_fs_interval_list_add_def;
                    candle_fs_interval_list_add_def;
                    candle_cv_fs_interval_add_correct]]);;

let candle_cv_fs_interval_matrix_neg_correct = prove
 (`!rows.
     candle_cv_fs_interval_matrix_neg (candle_cv_fs_interval_matrix rows) =
     candle_cv_fs_interval_matrix (candle_fs_interval_matrix_neg rows)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_matrix_neg_def;
                  candle_cv_fs_interval_matrix_def;
                  candle_fs_interval_matrix_neg_def;
                  candle_cv_fs_interval_list_neg_correct]);;

let candle_cv_fs_interval_matrix_add_correct = prove
 (`!xs ys.
     candle_cv_fs_interval_matrix_add
       (candle_cv_fs_interval_matrix xs) (candle_cv_fs_interval_matrix ys) =
     candle_cv_fs_interval_matrix (candle_fs_interval_matrix_add xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_fs_interval_matrix_def;
                candle_cv_fs_interval_matrix_add_def;
                candle_fs_interval_matrix_add_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_fs_interval_matrix_def;
                    candle_cv_fs_interval_matrix_add_def;
                    candle_fs_interval_matrix_add_def;
                    candle_cv_fs_interval_list_add_correct]]);;

let candle_cv_fs_raw_interval_list_add_correct = prove
 (`!xs ys.
     candle_cv_fs_raw_interval_list_add
       (candle_cv_fs_interval_list xs) (candle_cv_fs_interval_list ys) =
     candle_cv_fs_interval_list (candle_fs_raw_interval_list_add xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_fs_interval_list_def;
                candle_cv_fs_raw_interval_list_add_def;
                candle_fs_raw_interval_list_add_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_fs_interval_list_def;
                    candle_cv_fs_raw_interval_list_add_def;
                    candle_fs_raw_interval_list_add_def;
                    candle_cv_fs_raw_interval_add_correct]]);;

let candle_cv_fs_raw_interval_list_scale_correct = prove
 (`!scalar items.
     candle_cv_fs_raw_interval_list_scale
       (candle_cv_fs_interval scalar) (candle_cv_fs_interval_list items) =
     candle_cv_fs_interval_list
       (candle_fs_raw_interval_list_scale scalar items)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_list_def;
                  candle_cv_fs_raw_interval_list_scale_def;
                  candle_fs_raw_interval_list_scale_def;
                  candle_cv_fs_raw_interval_mul_correct]);;

let candle_cv_fs_raw_interval_matrix_add_correct = prove
 (`!xs ys.
     candle_cv_fs_raw_interval_matrix_add
       (candle_cv_fs_interval_matrix xs) (candle_cv_fs_interval_matrix ys) =
     candle_cv_fs_interval_matrix
       (candle_fs_raw_interval_matrix_add xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_fs_interval_matrix_def;
                candle_cv_fs_raw_interval_matrix_add_def;
                candle_fs_raw_interval_matrix_add_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_fs_interval_matrix_def;
                    candle_cv_fs_raw_interval_matrix_add_def;
                    candle_fs_raw_interval_matrix_add_def;
                    candle_cv_fs_raw_interval_list_add_correct]]);;

let candle_cv_fs_raw_interval_matrix_scale_correct = prove
 (`!scalar rows.
     candle_cv_fs_raw_interval_matrix_scale
       (candle_cv_fs_interval scalar) (candle_cv_fs_interval_matrix rows) =
     candle_cv_fs_interval_matrix
       (candle_fs_raw_interval_matrix_scale scalar rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_matrix_def;
                  candle_cv_fs_raw_interval_matrix_scale_def;
                  candle_fs_raw_interval_matrix_scale_def;
                  candle_cv_fs_raw_interval_list_scale_correct]);;

let candle_cv_fs_raw_interval_outer_correct = prove
 (`!xs ys.
     candle_cv_fs_raw_interval_outer
       (candle_cv_fs_interval_list xs) (candle_cv_fs_interval_list ys) =
     candle_cv_fs_interval_matrix (candle_fs_raw_interval_outer xs ys)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_list_def;
                  candle_cv_fs_interval_matrix_def;
                  candle_cv_fs_raw_interval_outer_def;
                  candle_fs_raw_interval_outer_def;
                  candle_cv_fs_raw_interval_list_scale_correct]);;

let candle_cv_fs_raw_interval_list_round_correct = prove
 (`!denominator items.
     candle_cv_fs_raw_interval_list_round (Cexp_num denominator)
       (candle_cv_fs_interval_list items) =
     candle_cv_fs_interval_list
       (candle_fs_raw_interval_list_round denominator items)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_list_def;
                  candle_cv_fs_raw_interval_list_round_def;
                  candle_fs_raw_interval_list_round_def;
                  candle_cv_fs_raw_interval_round_correct]);;

let candle_cv_fs_raw_interval_matrix_round_correct = prove
 (`!denominator rows.
     candle_cv_fs_raw_interval_matrix_round (Cexp_num denominator)
       (candle_cv_fs_interval_matrix rows) =
     candle_cv_fs_interval_matrix
       (candle_fs_raw_interval_matrix_round denominator rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_matrix_def;
                  candle_cv_fs_raw_interval_matrix_round_def;
                  candle_fs_raw_interval_matrix_round_def;
                  candle_cv_fs_raw_interval_list_round_correct]);;

let candle_cv_fs_dot_abs_upper_correct = prove
 (`!xs ys.
     candle_cv_fs_dot_abs_upper
       (candle_cv_lc_vec xs) (candle_cv_fs_interval_list ys) =
     candle_cv_lc_z (candle_fs_dot_abs_upper xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_lc_vec_def; candle_cv_fs_interval_list_def;
                candle_cv_fs_dot_abs_upper_def;
                candle_fs_dot_abs_upper_def;
                candle_cv_fs_zero_def; candle_cv_lc_z_def; FST; SND];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_lc_vec_def;
                    candle_cv_fs_interval_list_def;
                    candle_cv_fs_dot_abs_upper_def;
                    candle_fs_dot_abs_upper_def;
                    candle_cv_fs_zero_correct;
                    candle_cv_fs_raw_mul_correct;
                    candle_cv_fs_interval_abs_upper_correct;
                    candle_cv_fs_raw_add_correct]]);;

let candle_cv_fs_weighted_rows_abs_upper_correct = prove
 (`!radii weights rows.
     candle_cv_fs_weighted_rows_abs_upper
       (candle_cv_lc_vec radii) (candle_cv_lc_vec weights)
       (candle_cv_fs_interval_matrix rows) =
     candle_cv_lc_z
       (candle_fs_weighted_rows_abs_upper radii weights rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_lc_vec_def; candle_cv_fs_interval_matrix_def;
                candle_cv_fs_weighted_rows_abs_upper_def;
                candle_fs_weighted_rows_abs_upper_def;
                candle_cv_fs_zero_def; candle_cv_lc_z_def; FST; SND];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_lc_vec_def;
                    candle_cv_fs_interval_matrix_def;
                    candle_cv_fs_weighted_rows_abs_upper_def;
                    candle_fs_weighted_rows_abs_upper_def;
                    candle_cv_fs_zero_correct;
                    candle_cv_fs_dot_abs_upper_correct;
                    candle_cv_fs_raw_mul_correct;
                    candle_cv_fs_raw_add_correct]]);;

let candle_cv_fs_first_make_correct = prove
 (`!value gradient.
     candle_cv_fs_first_make
       (candle_cv_fs_interval value)
       (candle_cv_fs_interval_list gradient) =
     candle_cv_fs_first (candle_fs_first_make value gradient)`,
  REWRITE_TAC[candle_cv_fs_first_make_def; candle_cv_fs_first_def;
              candle_fs_first_make_def; candle_fs_first_value_def;
              candle_fs_first_gradient_def; FST; SND]);;

let candle_cv_fs_first_value_correct = prove
 (`!first.
     candle_cv_fs_first_value (candle_cv_fs_first first) =
     candle_cv_fs_interval (candle_fs_first_value first)`,
  REWRITE_TAC[candle_cv_fs_first_value_def; candle_cv_fs_first_def;
              cexp_fst_def]);;

let candle_cv_fs_first_gradient_correct = prove
 (`!first.
     candle_cv_fs_first_gradient (candle_cv_fs_first first) =
     candle_cv_fs_interval_list (candle_fs_first_gradient first)`,
  REWRITE_TAC[candle_cv_fs_first_gradient_def; candle_cv_fs_first_def;
              cexp_snd_def]);;

let candle_cv_fs_result_make_correct = prove
 (`!domain center value_bound gradient_bounds hessian.
     candle_cv_fs_result_make
       (candle_cv_bool domain) (candle_cv_fs_first center)
       (candle_cv_fs_interval value_bound)
       (candle_cv_fs_interval_list gradient_bounds)
       (candle_cv_fs_interval_matrix hessian) =
     candle_cv_fs_result
       (candle_fs_result_make domain center value_bound
         gradient_bounds hessian)`,
  REWRITE_TAC[candle_cv_fs_result_def; candle_cv_fs_result_make_def;
              candle_fs_result_make_def; candle_fs_result_domain_def;
              candle_fs_result_center_def;
              candle_fs_result_value_bound_def;
              candle_fs_result_gradient_bounds_def;
              candle_fs_result_hessian_def; FST; SND]);;

let candle_cv_fs_result_domain_correct = prove
 (`!result.
     candle_cv_fs_result_domain (candle_cv_fs_result result) =
     candle_cv_bool (candle_fs_result_domain result)`,
  REWRITE_TAC[candle_cv_fs_result_domain_def; candle_cv_fs_result_def;
              candle_cv_fs_result_make_def; cexp_fst_def]);;

let candle_cv_fs_result_center_correct = prove
 (`!result.
     candle_cv_fs_result_center (candle_cv_fs_result result) =
     candle_cv_fs_first (candle_fs_result_center result)`,
  REWRITE_TAC[candle_cv_fs_result_center_def; candle_cv_fs_result_def;
              candle_cv_fs_result_make_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_result_value_bound_correct = prove
 (`!result.
     candle_cv_fs_result_value_bound (candle_cv_fs_result result) =
     candle_cv_fs_interval (candle_fs_result_value_bound result)`,
  REWRITE_TAC[candle_cv_fs_result_value_bound_def; candle_cv_fs_result_def;
              candle_cv_fs_result_make_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_result_gradient_bounds_correct = prove
 (`!result.
     candle_cv_fs_result_gradient_bounds (candle_cv_fs_result result) =
     candle_cv_fs_interval_list
       (candle_fs_result_gradient_bounds result)`,
  REWRITE_TAC[candle_cv_fs_result_gradient_bounds_def;
              candle_cv_fs_result_def; candle_cv_fs_result_make_def;
              cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_result_hessian_correct = prove
 (`!result.
     candle_cv_fs_result_hessian (candle_cv_fs_result result) =
     candle_cv_fs_interval_matrix (candle_fs_result_hessian result)`,
  REWRITE_TAC[candle_cv_fs_result_hessian_def; candle_cv_fs_result_def;
              candle_cv_fs_result_make_def; cexp_snd_def]);;

let candle_cv_fs_gradient_bounds_correct = prove
 (`!radii gradients row_lists.
     candle_cv_fs_gradient_bounds
       (candle_cv_lc_vec radii)
       (candle_cv_fs_interval_list gradients)
       (candle_cv_fs_interval_matrix row_lists) =
     candle_cv_fs_interval_list
       (candle_fs_gradient_bounds radii gradients row_lists)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN
    REWRITE_TAC[candle_cv_fs_interval_list_def;
                candle_cv_fs_interval_matrix_def;
                candle_cv_fs_gradient_bounds_def;
                candle_fs_gradient_bounds_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_fs_interval_list_def;
                    candle_cv_fs_interval_matrix_def;
                    candle_cv_fs_gradient_bounds_def;
                    candle_fs_gradient_bounds_def;
                    candle_cv_fs_scale_correct;
                    candle_cv_fs_raw_scale_correct;
                    candle_cv_fs_dot_abs_upper_correct;
                    candle_cv_fs_raw_neg_correct;
                    candle_cv_fs_raw_interval_add_correct;
                    candle_cv_fs_raw_interval_round_correct;
                    candle_cv_fs_interval_fst_correct;
                    candle_cv_fs_interval_snd_correct;
                    candle_cv_fs_interval_pair_correct; FST; SND]]);;

let candle_cv_fs_result_complete_rounded_correct = prove
 (`!radii domain center hessian.
     candle_cv_fs_result_complete_rounded
       (candle_cv_lc_vec radii) (candle_cv_bool domain)
       (candle_cv_fs_first center)
       (candle_cv_fs_interval_matrix hessian) =
     candle_cv_fs_result
       (candle_fs_result_complete_rounded
         radii domain center hessian)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_result_complete_rounded_def;
              candle_fs_result_complete_rounded_def;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fs_two_scale_squared_correct;
              candle_cv_fs_scale_correct;
              candle_cv_fs_raw_scale_correct;
              candle_cv_fs_dot_abs_upper_correct;
              candle_cv_fs_weighted_rows_abs_upper_correct;
              candle_cv_fs_raw_neg_correct;
              candle_cv_fs_raw_add_correct;
              candle_cv_fs_raw_interval_add_correct;
              candle_cv_fs_raw_interval_round_correct;
              candle_cv_fs_gradient_bounds_correct;
              candle_cv_fs_result_make_correct;
              candle_cv_fs_interval_fst_correct;
              candle_cv_fs_interval_snd_correct;
              candle_cv_fs_interval_pair_correct;
              cexp_mul_def; FST; SND]);;

let candle_cv_fs_result_complete_raw_correct = prove
 (`!radii domain raw_center raw_hessian.
     candle_cv_fs_result_complete_raw
       (candle_cv_lc_vec radii) (candle_cv_bool domain)
       (candle_cv_fs_first raw_center)
       (candle_cv_fs_interval_matrix raw_hessian) =
     candle_cv_fs_result
       (candle_fs_result_complete_raw
         radii domain raw_center raw_hessian)`,
  REWRITE_TAC[candle_cv_fs_result_complete_raw_def;
              candle_fs_result_complete_raw_def;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fs_scale_correct;
              candle_cv_fs_raw_interval_round_correct;
              candle_cv_fs_raw_interval_list_round_correct;
              candle_cv_fs_raw_interval_matrix_round_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_result_complete_rounded_correct]);;

let candle_cv_fs_result_complete_empty_false_correct = prove
 (`!center hessian.
     candle_cv_fs_result_complete_rounded
       (Cexp_num 0) (Cexp_num 0)
       (candle_cv_fs_first center)
       (candle_cv_fs_interval_matrix hessian) =
     candle_cv_fs_result
       (candle_fs_result_complete_rounded [] F center hessian)`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPECL
      [`[]:(num#num)list`; `F`;
       `center:((num#num)#(num#num))#
          (((num#num)#(num#num))list)`;
       `hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_result_complete_rounded_correct) THEN
  REWRITE_TAC[candle_cv_lc_vec_def; candle_cv_bool_def]);;

let candle_cv_fs_result_complete_true_correct = prove
 (`!radii center hessian.
     candle_cv_fs_result_complete_rounded
       (candle_cv_lc_vec radii) (Cexp_num 1)
       (candle_cv_fs_first center)
       (candle_cv_fs_interval_matrix hessian) =
     candle_cv_fs_result
       (candle_fs_result_complete_rounded radii T center hessian)`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPECL
      [`radii:(num#num)list`; `T`;
       `center:((num#num)#(num#num))#
          (((num#num)#(num#num))list)`;
       `hessian:(((num#num)#(num#num))list)list`]
      candle_cv_fs_result_complete_rounded_correct) THEN
  REWRITE_TAC[candle_cv_bool_def; ARITH_RULE `1 = SUC 0`]);;

let candle_cv_fs_result_zero_correct = prove
 (`!dimensions.
     candle_cv_fs_result_zero (candle_cv_fs_interval_list dimensions) =
     candle_cv_fs_result (candle_fs_result_zero dimensions)`,
  REWRITE_TAC[candle_cv_fs_result_zero_def; candle_fs_result_zero_def;
              candle_cv_fs_interval_zero_correct;
              candle_cv_fs_interval_zeros_correct;
              candle_cv_fs_interval_zero_matrix_like_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_result_complete_empty_false_correct]);;

let candle_cv_fs_result_head_correct = prove
 (`!dimensions stack.
     candle_cv_fs_result_head (candle_cv_fs_interval_list dimensions)
       (candle_cv_fs_result_list stack) =
     candle_cv_fs_result (candle_fs_result_head dimensions stack)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_fs_result_head_def;
              candle_fs_result_head_def;
              candle_cv_fs_result_list_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def;
              candle_cv_fs_result_zero_correct]);;

let candle_cv_fs_result_tail_correct = prove
 (`!stack.
     candle_cv_fs_result_tail (candle_cv_fs_result_list stack) =
     candle_cv_fs_result_list (candle_fs_result_tail stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_fs_result_tail_def;
              candle_fs_result_tail_def;
              candle_cv_fs_result_list_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_fs_result_constant_correct = prove
 (`!dimensions radii q.
     candle_cv_fs_result_constant
       (candle_cv_fs_interval_list dimensions)
       (candle_cv_lc_vec radii) (candle_cv_q q) =
     candle_cv_fs_result
       (candle_fs_result_constant dimensions radii q)`,
  REWRITE_TAC[candle_cv_fs_result_constant_def;
              candle_fs_result_constant_def;
              candle_cv_fs_interval_constant_correct;
              candle_cv_fs_interval_zeros_correct;
              candle_cv_fs_interval_zero_matrix_like_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_result_complete_true_correct]);;

let candle_cv_fs_result_variable_correct = prove
 (`!dimensions radii variable.
     candle_cv_fs_result_variable
       (candle_cv_fs_interval_list dimensions)
       (candle_cv_lc_vec radii) (Cexp_num variable) =
     candle_cv_fs_result
       (candle_fs_result_variable dimensions radii variable)`,
  REWRITE_TAC[candle_cv_fs_result_variable_def;
              candle_fs_result_variable_def;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_interval_unit_correct;
              candle_cv_fs_interval_zero_matrix_like_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_result_complete_true_correct]);;

let candle_cv_fs_result_neg_correct = prove
 (`!radii result.
     candle_cv_fs_result_neg
       (candle_cv_lc_vec radii) (candle_cv_fs_result result) =
     candle_cv_fs_result (candle_fs_result_neg radii result)`,
  REWRITE_TAC[candle_cv_fs_result_neg_def; candle_fs_result_neg_def;
              candle_cv_fs_result_domain_correct;
              candle_cv_fs_result_center_correct;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fs_interval_neg_correct;
              candle_cv_fs_interval_list_neg_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_result_hessian_correct;
              candle_cv_fs_interval_matrix_neg_correct;
              candle_cv_fs_result_complete_rounded_correct]);;

let candle_cv_fs_result_add_correct = prove
 (`!radii left right.
     candle_cv_fs_result_add (candle_cv_lc_vec radii)
       (candle_cv_fs_result left) (candle_cv_fs_result right) =
     candle_cv_fs_result (candle_fs_result_add radii left right)`,
  REWRITE_TAC[candle_cv_fs_result_add_def; candle_fs_result_add_def;
              candle_cv_fs_result_domain_correct;
              candle_cv_bool_and_correct;
              candle_cv_fs_result_center_correct;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fs_interval_add_correct;
              candle_cv_fs_interval_list_add_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_result_hessian_correct;
              candle_cv_fs_interval_matrix_add_correct;
              candle_cv_fs_result_complete_rounded_correct]);;

let candle_cv_fs_result_mul_correct = prove
 (`!radii left right.
     candle_cv_fs_result_mul (candle_cv_lc_vec radii)
       (candle_cv_fs_result left) (candle_cv_fs_result right) =
     candle_cv_fs_result (candle_fs_result_mul radii left right)`,
  REWRITE_TAC[candle_cv_fs_result_mul_def; candle_fs_result_mul_def;
              candle_cv_fs_result_domain_correct;
              candle_cv_bool_and_correct;
              candle_cv_fs_result_center_correct;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fs_raw_interval_mul_correct;
              candle_cv_fs_raw_interval_list_scale_correct;
              candle_cv_fs_raw_interval_list_add_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_result_value_bound_correct;
              candle_cv_fs_result_gradient_bounds_correct;
              candle_cv_fs_result_hessian_correct;
              candle_cv_fs_raw_interval_matrix_scale_correct;
              candle_cv_fs_raw_interval_outer_correct;
              candle_cv_fs_raw_interval_matrix_add_correct;
              candle_cv_fs_result_complete_raw_correct]);;

let candle_cv_fs_result_square_correct = prove
 (`!radii result.
     candle_cv_fs_result_square
       (candle_cv_lc_vec radii) (candle_cv_fs_result result) =
     candle_cv_fs_result (candle_fs_result_square radii result)`,
  REWRITE_TAC[candle_cv_fs_result_square_def;
              candle_fs_result_square_def;
              candle_cv_fs_result_mul_correct]);;

let candle_cv_fs_poly_step_correct = prove
 (`!instruction dimensions radii stack.
     candle_cv_fs_poly_step
       (candle_cv_fs_interval_list dimensions)
       (candle_cv_lc_vec radii)
       (candle_cv_q_instruction instruction)
       (candle_cv_fs_result_list stack) =
     candle_cv_fs_result_list
       (candle_fs_poly_step dimensions radii instruction stack)`,
  MATCH_MP_TAC candle_q_instruction_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_poly_step_def; candle_fs_poly_step_def;
              candle_cv_q_instruction_def;
              candle_cv_fs_result_list_def;
              cexp_fst_def; cexp_snd_def; cexp_eq_def; cexp_if_def;
              cexp_ispair_def; distinctness "cval"; injectivity "cval";
              NOT_SUC; candle_one_ne_zero; candle_four_ne_two;
              candle_four_ne_three; candle_three_ne_two;
              candle_five_ne_two; candle_five_ne_three;
              candle_five_ne_four;
              candle_cv_fs_result_constant_correct;
              candle_cv_fs_result_variable_correct;
              candle_cv_fs_result_head_correct;
              candle_cv_fs_result_tail_correct;
              candle_cv_fs_result_neg_correct;
              candle_cv_fs_result_add_correct;
              candle_cv_fs_result_mul_correct;
              candle_cv_fs_result_square_correct]);;

let candle_cv_fs_poly_run_correct = prove
 (`!program dimensions radii stack.
     candle_cv_fs_poly_run
       (candle_cv_fs_interval_list dimensions)
       (candle_cv_lc_vec radii)
       (candle_cv_q_instruction_list program)
       (candle_cv_fs_result_list stack) =
     candle_cv_fs_result_list
       (candle_fs_poly_run dimensions radii program stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_instruction_list_def;
                  candle_cv_fs_poly_run_def;
                  candle_fs_poly_run_def;
                  candle_cv_fs_poly_step_correct]);;

let candle_cv_fs_poly_program_fixed_correct = prove
 (`!program dimensions radii.
     candle_cv_fs_poly_program_fixed
       (candle_cv_fs_interval_list dimensions)
       (candle_cv_lc_vec radii)
       (candle_cv_q_instruction_list program) =
     candle_cv_fs_result
       (candle_fs_poly_program_fixed dimensions radii program)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_poly_program_fixed_def;
              candle_fs_poly_program_fixed_def;
              GSYM candle_cv_fs_result_list_def;
              candle_cv_fs_poly_run_correct;
              candle_cv_fs_result_head_correct]);;

let candle_cv_fs_poly_program_correct = prove
 (`!program center_boxes radii.
     candle_cv_fs_poly_program
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction_list program) =
     candle_cv_fs_result
       (candle_fs_poly_program center_boxes radii program)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_poly_program_def;
              candle_fs_poly_program_def;
              candle_cv_fs_interval_list_of_q_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fs_poly_program_fixed_correct]);;

let candle_cv_fs_interval_to_q_correct = prove
 (`!i.
     candle_cv_fs_interval_to_q (candle_cv_fs_interval i) =
     candle_cv_q_interval (candle_fs_interval_to_q i)`,
  REWRITE_TAC[candle_cv_fs_interval_to_q_def;
              candle_fs_interval_to_q_def;
              candle_cv_fs_interval_def; candle_cv_q_interval_def;
              cexp_fst_def; cexp_snd_def;
              candle_cv_fs_to_q_correct; FST; SND]);;

let candle_cv_fs_interval_list_to_q_correct = prove
 (`!items.
     candle_cv_fs_interval_list_to_q
       (candle_cv_fs_interval_list items) =
     candle_cv_q_interval_list
       (candle_fs_interval_list_to_q items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_list_def;
                  candle_cv_fs_interval_list_to_q_def;
                  candle_cv_q_interval_list_def;
                  candle_fs_interval_list_to_q_def;
                  candle_cv_fs_interval_to_q_correct]);;

let candle_cv_fs_interval_matrix_to_q_correct = prove
 (`!row_lists.
     candle_cv_fs_interval_matrix_to_q
       (candle_cv_fs_interval_matrix row_lists) =
     candle_cv_q_interval_matrix
       (candle_fs_interval_matrix_to_q row_lists)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_matrix_def;
                  candle_cv_fs_interval_matrix_to_q_def;
                  candle_cv_q_interval_matrix_def;
                  candle_fs_interval_matrix_to_q_def;
                  candle_cv_fs_interval_list_to_q_correct]);;

let candle_cv_fs_first_to_q_correct = prove
 (`!first hessian.
     candle_cv_q_dim_first_jet_make
       (candle_cv_fs_interval_to_q
         (candle_cv_fs_first_value (candle_cv_fs_first first)))
       (candle_cv_fs_interval_list_to_q
         (candle_cv_fs_first_gradient (candle_cv_fs_first first))) =
     candle_cv_q_dim_first_jet_encode
       (candle_fs_first_to_q first hessian)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_first_value_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fs_interval_to_q_correct;
              candle_cv_fs_interval_list_to_q_correct;
              candle_fs_first_to_q_def] THEN
  MATCH_ACCEPT_TAC candle_cv_q_dim_first_jet_make_correct);;

let candle_cv_fs_result_to_q_correct = prove
 (`!result.
     candle_cv_fs_result_to_q (candle_cv_fs_result result) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_fs_result_to_q result)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_result_to_q_def;
              candle_fs_result_to_q_def;
              candle_cv_fs_result_domain_correct;
              candle_cv_fs_result_center_correct;
              candle_cv_fs_result_value_bound_correct;
              candle_cv_fs_result_gradient_bounds_correct;
              candle_cv_fs_result_hessian_correct;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fs_interval_to_q_correct;
              candle_cv_fs_interval_list_to_q_correct;
              candle_cv_fs_interval_matrix_to_q_correct;
              candle_cv_q_dim_taylor_model_result_encode_def;
              candle_cv_q_dim_taylor_model_result_make_def;
              candle_q_dim_taylor_model_result_domain_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_value_bound_def;
              candle_q_dim_taylor_model_result_gradient_bounds_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_cv_q_dim_first_jet_encode_def;
              candle_cv_q_dim_first_jet_make_def;
              candle_fs_first_to_q_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def; FST; SND]);;

let candle_cv_fs_poly_program_to_q_correct = prove
 (`!program center_boxes radii.
     candle_cv_fs_poly_program_to_q
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction_list program) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_fs_poly_program_to_q center_boxes radii program)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_poly_program_to_q_def;
              candle_fs_poly_program_to_q_def;
              candle_cv_fs_poly_program_correct;
              candle_cv_fs_result_to_q_correct]);;

(* -------------------------------------------------------------------------- *)
(* Real denotation.                                                           *)
(* -------------------------------------------------------------------------- *)

let candle_fs_scale_pos = prove
 (`0 < candle_fs_scale`,
  REWRITE_TAC[candle_fs_scale_def] THEN ARITH_TAC);;

let candle_fs_raw_neg_real = prove
 (`!z. candle_lc_zreal (candle_fs_raw_neg z) = --(candle_lc_zreal z)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_neg_def; candle_lc_zreal_def; FST; SND] THEN
  REAL_ARITH_TAC);;

let candle_fs_canonical_real = prove
 (`!z. candle_lc_zreal (candle_fs_canonical z) = candle_lc_zreal z`,
  REWRITE_TAC[FORALL_PAIR_THM; candle_fs_canonical_def;
              candle_lc_zreal_def; FST; SND] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LZERO] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_OF_NUM_SUB_CASES] THEN
    ASM_REWRITE_TAC[GSYM NOT_LT];
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_OF_NUM_SUB_CASES] THEN
    ASM_REWRITE_TAC[GSYM NOT_LT]]);;

let candle_fs_add_real = prove
 (`!x y. candle_fs_real (candle_fs_add x y) =
         candle_fs_real x + candle_fs_real y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_real_def; candle_fs_add_def;
              candle_fs_canonical_real; candle_lc_zreal_add;
              real_div; REAL_ADD_RDISTRIB]);;

let candle_fs_raw_add_real = prove
 (`!denominator x y. ~(denominator = 0)
     ==> candle_fs_raw_real denominator (candle_lc_zadd x y) =
         candle_fs_raw_real denominator x +
         candle_fs_raw_real denominator y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; candle_lc_zreal_add] THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB]);;

let candle_fs_raw_scale_real = prove
 (`!denominator factor z. ~(denominator = 0)
     ==> candle_fs_raw_real denominator (candle_lc_zscale factor z) =
         &factor * candle_fs_raw_real denominator z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; candle_lc_zreal_scale;
              real_div; REAL_MUL_ASSOC]);;

let candle_fs_raw_mul_real = prove
 (`!left_denominator right_denominator x y.
     0 < left_denominator /\ 0 < right_denominator
     ==> candle_fs_raw_real (left_denominator * right_denominator)
           (candle_q_zmul x y) =
         candle_fs_raw_real left_denominator x *
         candle_fs_raw_real right_denominator y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; candle_q_zreal_mul;
              GSYM REAL_OF_NUM_MUL] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN CONV_TAC REAL_FIELD);;

let candle_fs_raw_neg_real_scaled = prove
 (`!z. candle_fs_real (candle_fs_raw_neg z) = --(candle_fs_real z)`,
  REWRITE_TAC[candle_fs_real_def; candle_fs_raw_neg_real;
              real_div; GSYM REAL_NEG_LMUL]);;

let candle_fs_to_q_real = prove
 (`!z. candle_q_real (candle_fs_to_q z) = candle_fs_real z`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_real_def; candle_q_den_def;
              candle_fs_to_q_def; candle_fs_real_def; FST; SND] THEN
  SUBGOAL_THEN `SUC (candle_fs_scale - 1) = candle_fs_scale`
    SUBST1_TAC THENL
   [MP_TAC candle_fs_scale_pos THEN ARITH_TAC;
    REFL_TAC]);;

(* Converting a fixed-scale result to the established rational Taylor-model
   interface changes only its representation.  In particular it preserves
   interval denotations and all outer list/matrix dimensions. *)

let candle_fs_interval_to_q_contains = prove
 (`!i x.
     candle_q_interval_contains (candle_fs_interval_to_q i) x <=>
     candle_fs_interval_contains i x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_fs_interval_contains_def;
              candle_fs_interval_to_q_def;
              candle_fs_to_q_real; FST; SND]);;

let candle_fs_interval_list_to_q_length = prove
 (`!items.
     LENGTH (candle_fs_interval_list_to_q items) = LENGTH items`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_interval_list_to_q_def; LENGTH]);;

let candle_fs_interval_matrix_to_q_length = prove
 (`!rows.
     LENGTH (candle_fs_interval_matrix_to_q rows) = LENGTH rows`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fs_interval_matrix_to_q_def; LENGTH]);;

let candle_fs_interval_list_to_q_contains = prove
 (`!intervals values.
     candle_q_stack_contains
       (candle_fs_interval_list_to_q intervals) values <=>
     ALL2 candle_fs_interval_contains intervals values`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_fs_interval_list_to_q_def;
                candle_q_stack_contains_def; ALL2];
    GEN_TAC THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_fs_interval_list_to_q_def;
                    candle_q_stack_contains_def; ALL2;
                    candle_fs_interval_to_q_contains]]);;

let candle_fs_interval_matrix_to_q_contains = prove
 (`!rows values.
     ALL2 candle_q_stack_contains
       (candle_fs_interval_matrix_to_q rows) values <=>
     ALL2 (ALL2 candle_fs_interval_contains) rows values`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC (ISPEC `values:(real list)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_fs_interval_matrix_to_q_def; ALL2];
    GEN_TAC THEN
    MP_TAC (ISPEC `values:(real list)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_fs_interval_matrix_to_q_def; ALL2;
                    candle_fs_interval_list_to_q_contains]]);;

let candle_fs_raw_le_real = prove
 (`!x y. candle_fs_raw_le x y <=>
         candle_lc_zreal x <= candle_lc_zreal y`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_le_def; candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  EQ_TAC THEN REAL_ARITH_TAC);;

let candle_fs_raw_le_scaled = prove
 (`!denominator x y. 0 < denominator
     ==> (candle_fs_raw_le x y <=>
          candle_fs_raw_real denominator x <=
          candle_fs_raw_real denominator y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LT;
               candle_fs_raw_le_real]);;

let candle_fs_raw_min_real = prove
 (`!denominator x y. 0 < denominator
     ==> candle_fs_raw_real denominator (candle_fs_raw_min x y) =
         min (candle_fs_raw_real denominator x)
             (candle_fs_raw_real denominator y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_min_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC
    (SPECL [`denominator:num`; `x:num#num`; `y:num#num`]
      candle_fs_raw_le_scaled) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let candle_fs_raw_max_real = prove
 (`!denominator x y. 0 < denominator
     ==> candle_fs_raw_real denominator (candle_fs_raw_max x y) =
         max (candle_fs_raw_real denominator x)
             (candle_fs_raw_real denominator y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_max_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC
    (SPECL [`denominator:num`; `x:num#num`; `y:num#num`]
      candle_fs_raw_le_scaled) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let candle_fs_raw_max_real_scaled = prove
 (`!x y. candle_fs_real (candle_fs_raw_max x y) =
         max (candle_fs_real x) (candle_fs_real y)`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPECL [`candle_fs_scale`; `x:num#num`; `y:num#num`]
      candle_fs_raw_max_real) THEN
  REWRITE_TAC[candle_fs_scale_pos; candle_fs_raw_real_def;
              GSYM candle_fs_real_def]);;

let candle_fs_raw_abs_real_scaled = prove
 (`!z. candle_fs_real (candle_fs_raw_abs z) = abs (candle_fs_real z)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_abs_def; candle_fs_raw_max_real_scaled;
              candle_fs_raw_neg_real_scaled] THEN
  REAL_ARITH_TAC);;

let candle_fs_interval_abs_upper_sound = prove
 (`!i x. candle_fs_interval_contains i x
         ==> abs x <= candle_fs_real (candle_fs_interval_abs_upper i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_interval_abs_upper_def;
              candle_fs_raw_max_real_scaled;
              candle_fs_raw_abs_real_scaled] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`candle_fs_real (FST (i:(num#num)#(num#num)))`;
       `candle_fs_real (SND (i:(num#num)#(num#num)))`; `x:real`]
      candle_real_abs_interval_upper) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC
    (SPECL
      [`candle_fs_real (FST (i:(num#num)#(num#num)))`;
       `abs (candle_fs_real (FST (i:(num#num)#(num#num))))`]
      REAL_ABS_BOUNDS) THEN
  MP_TAC
    (SPEC `candle_fs_real (SND (i:(num#num)#(num#num)))` REAL_ABS_LE) THEN
  MP_TAC
    (SPECL
      [`abs (candle_fs_real (FST (i:(num#num)#(num#num))))`;
       `abs (candle_fs_real (SND (i:(num#num)#(num#num))))`]
      REAL_MAX_MAX) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC);;

let candle_fs_product_denominator_pos = prove
 (`0 < candle_fs_scale * candle_fs_scale`,
  REWRITE_TAC[LT_MULT; candle_fs_scale_pos]);;

let candle_fs_raw_product_real = prove
 (`!x y.
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (candle_q_zmul x y) =
     candle_fs_real x * candle_fs_real y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; candle_fs_real_def;
              candle_q_zreal_mul; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC candle_fs_scale_pos THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  CONV_TAC REAL_FIELD);;

let candle_fs_raw_zero_real = prove
 (`!denominator. candle_fs_raw_real denominator (0,0) = &0`,
  REWRITE_TAC[candle_fs_raw_real_def; candle_lc_zreal_def; FST; SND;
              REAL_SUB_REFL; real_div; REAL_MUL_LZERO]);;

let candle_fs_raw_product_add_real = prove
 (`!x y.
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (candle_lc_zadd x y) =
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale) x +
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale) y`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC candle_fs_raw_add_real THEN
  MP_TAC candle_fs_product_denominator_pos THEN ARITH_TAC);;

let candle_fs_raw_product_min_real = prove
 (`!x y.
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (candle_fs_raw_min x y) =
     min
       (candle_fs_raw_real (candle_fs_scale * candle_fs_scale) x)
       (candle_fs_raw_real (candle_fs_scale * candle_fs_scale) y)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC candle_fs_raw_min_real THEN
  MATCH_ACCEPT_TAC candle_fs_product_denominator_pos);;

let candle_fs_raw_product_max_real = prove
 (`!x y.
     candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
       (candle_fs_raw_max x y) =
     max
       (candle_fs_raw_real (candle_fs_scale * candle_fs_scale) x)
       (candle_fs_raw_real (candle_fs_scale * candle_fs_scale) y)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC candle_fs_raw_max_real THEN
  MATCH_ACCEPT_TAC candle_fs_product_denominator_pos);;

let candle_fs_raw_interval_mul_sound = prove
 (`!i j x y.
     candle_fs_interval_contains i x /\
     candle_fs_interval_contains j y
     ==> candle_fs_raw_interval_contains
           (candle_fs_scale * candle_fs_scale)
           (candle_fs_raw_interval_mul i j) (x * y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_raw_interval_contains_def;
              candle_fs_raw_interval_mul_def;
              candle_fs_raw_product_min_real;
              candle_fs_raw_product_max_real;
              candle_fs_raw_product_real; FST; SND] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC candle_real_interval_mul THEN
  ASM_REWRITE_TAC[]);;

(* The fixed-scale dot accumulator bounds the corresponding real first-order
   Taylor sum.  Its accumulator has denominator scale squared throughout. *)

let candle_fs_dot_abs_upper_sound = prove
 (`!radii values intervals.
     ALL (\r. &0 <= candle_fs_real r) radii /\
     ALL2 candle_fs_interval_contains intervals values /\
     LENGTH radii = LENGTH values
     ==>
     ITLIST2
       (\r y total. candle_fs_real r * abs y + total)
       radii values (&0)
     <= candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
          (candle_fs_dot_abs_upper radii intervals)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    MP_TAC
      (ISPEC `intervals:((num#num)#(num#num))list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL; ALL2; LENGTH; candle_fs_dot_abs_upper_def;
                ITLIST2_DEF; candle_fs_raw_zero_real; REAL_LE_REFL];
    POP_ASSUM (LABEL_TAC "radii_ih") THEN
    MAP_EVERY X_GEN_TAC
      [`values:real list`;
       `intervals:((num#num)#(num#num))list`] THEN
    MP_TAC (ISPEC `values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `y:real`
          (X_CHOOSE_THEN `ys:real list` SUBST_ALL_TAC))) THEN
    MP_TAC
      (ISPEC `intervals:((num#num)#(num#num))list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `i:(num#num)#(num#num)`
          (X_CHOOSE_THEN
            `is:((num#num)#(num#num))list` SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[ALL; ALL2; LENGTH; candle_fs_dot_abs_upper_def;
                    ITLIST2_DEF; HD; TL;
                    candle_fs_raw_product_add_real;
                    candle_fs_raw_product_real] THEN
    REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
    SUBGOAL_THEN
      `ITLIST2
         (\r y total. candle_fs_real r * abs y + total)
         t ys (&0)
       <= candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
            (candle_fs_dot_abs_upper t is)`
      ASSUME_TAC THENL
     [USE_THEN "radii_ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
      `abs y <= candle_fs_real (candle_fs_interval_abs_upper i)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC candle_fs_interval_abs_upper_sound THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `candle_fs_real h * abs y <=
       candle_fs_real h * candle_fs_real (candle_fs_interval_abs_upper i)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

let candle_fs_triple_denominator_pos = prove
 (`0 < candle_fs_scale * (candle_fs_scale * candle_fs_scale)`,
  REWRITE_TAC[LT_MULT; candle_fs_scale_pos;
              candle_fs_product_denominator_pos]);;

let candle_fs_raw_triple_add_real = prove
 (`!x y.
     candle_fs_raw_real
       (candle_fs_scale * (candle_fs_scale * candle_fs_scale))
       (candle_lc_zadd x y) =
     candle_fs_raw_real
       (candle_fs_scale * (candle_fs_scale * candle_fs_scale)) x +
     candle_fs_raw_real
       (candle_fs_scale * (candle_fs_scale * candle_fs_scale)) y`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC candle_fs_raw_add_real THEN
  MP_TAC candle_fs_triple_denominator_pos THEN ARITH_TAC);;

let candle_fs_raw_weighted_product_real = prove
 (`!weight accumulated.
     candle_fs_raw_real
       (candle_fs_scale * (candle_fs_scale * candle_fs_scale))
       (candle_q_zmul weight accumulated) =
     candle_fs_real weight *
     candle_fs_raw_real
       (candle_fs_scale * candle_fs_scale) accumulated`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPECL
      [`candle_fs_scale`; `candle_fs_scale * candle_fs_scale`;
       `weight:num#num`; `accumulated:num#num`]
      candle_fs_raw_mul_real) THEN
  REWRITE_TAC[candle_fs_scale_pos; candle_fs_product_denominator_pos;
              candle_fs_raw_real_def; GSYM candle_fs_real_def]);;

(* The outer fixed-scale accumulator bounds the complete Hessian double sum.
   Its accumulator has denominator scale cubed. *)

let candle_fs_weighted_rows_abs_upper_sound = prove
 (`!radii weights value_rows interval_rows.
     ALL (\r. &0 <= candle_fs_real r) radii /\
     ALL (\w. &0 <= candle_fs_real w) weights /\
     ALL2 (ALL2 candle_fs_interval_contains) interval_rows value_rows /\
     LENGTH weights = LENGTH value_rows /\
     ALL (\values. LENGTH radii = LENGTH values) value_rows
     ==>
     ITLIST2
       (\w values total.
          candle_fs_real w *
          ITLIST2
            (\r y subtotal. candle_fs_real r * abs y + subtotal)
            radii values (&0) + total)
       weights value_rows (&0)
     <= candle_fs_raw_real
          (candle_fs_scale * (candle_fs_scale * candle_fs_scale))
          (candle_fs_weighted_rows_abs_upper
            radii weights interval_rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `value_rows:(real list)list` list_CASES) THEN
    MP_TAC
      (ISPEC
        `interval_rows:(((num#num)#(num#num))list)list`
        list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[ALL; ALL2; LENGTH;
                candle_fs_weighted_rows_abs_upper_def; ITLIST2_DEF;
                candle_fs_raw_zero_real; REAL_LE_REFL];
    POP_ASSUM (LABEL_TAC "weights_ih") THEN
    MAP_EVERY X_GEN_TAC
      [`value_rows:(real list)list`;
       `interval_rows:(((num#num)#(num#num))list)list`] THEN
    MP_TAC (ISPEC `value_rows:(real list)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `values:real list`
          (X_CHOOSE_THEN `value_tail:(real list)list` SUBST_ALL_TAC))) THEN
    MP_TAC
      (ISPEC
        `interval_rows:(((num#num)#(num#num))list)list`
        list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `intervals:((num#num)#(num#num))list`
          (X_CHOOSE_THEN
            `interval_tail:(((num#num)#(num#num))list)list`
            SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[ALL; ALL2; LENGTH;
                    candle_fs_weighted_rows_abs_upper_def; ITLIST2_DEF;
                    HD; TL; candle_fs_raw_triple_add_real;
                    candle_fs_raw_weighted_product_real] THEN
    REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THEN
    SUBGOAL_THEN
      `ITLIST2
         (\r y subtotal. candle_fs_real r * abs y + subtotal)
         radii values (&0)
       <= candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
            (candle_fs_dot_abs_upper radii intervals)`
      (LABEL_TAC "row_bound") THENL
     [MATCH_MP_TAC candle_fs_dot_abs_upper_sound THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `ITLIST2
         (\w values total.
            candle_fs_real w *
            ITLIST2
              (\r y subtotal. candle_fs_real r * abs y + subtotal)
              radii values (&0) + total)
         t value_tail (&0)
       <= candle_fs_raw_real
            (candle_fs_scale *
              (candle_fs_scale * candle_fs_scale))
            (candle_fs_weighted_rows_abs_upper
              radii t interval_tail)`
      (LABEL_TAC "tail_bound") THENL
     [USE_THEN "weights_ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
      `candle_fs_real h *
         ITLIST2
           (\r y subtotal. candle_fs_real r * abs y + subtotal)
           radii values (&0)
       <= candle_fs_real h *
          candle_fs_raw_real (candle_fs_scale * candle_fs_scale)
            (candle_fs_dot_abs_upper radii intervals)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

let candle_fs_fixed_make_real = prove
 (`!positive negative.
     candle_fs_real (positive,negative) =
     candle_q_real (candle_q_fixed_make positive negative)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_fixed_make_real; candle_fs_real_def;
              candle_lc_zreal_def; candle_fs_scale_def;
              candle_q_taylor_model_scale_def; FST; SND]);;

let candle_fs_of_q_lower_real = prove
 (`!q. candle_fs_real (candle_fs_of_q_lower q) =
       candle_q_real (candle_q_fixed_round_lower q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_of_q_lower_def;
              candle_q_fixed_round_lower_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_make_def; FST;
                  candle_fs_fixed_make_real]);;

let candle_fs_of_q_upper_real = prove
 (`!q. candle_fs_real (candle_fs_of_q_upper q) =
       candle_q_real (candle_q_fixed_round_upper q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_of_q_upper_def;
              candle_q_fixed_round_upper_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_make_def; FST;
                  candle_fs_fixed_make_real]);;

let candle_fs_of_q_lower_sound = prove
 (`!q. candle_fs_real (candle_fs_of_q_lower q) <= candle_q_real q`,
  REWRITE_TAC[candle_fs_of_q_lower_real;
              candle_q_fixed_round_lower_sound]);;

let candle_fs_of_q_upper_sound = prove
 (`!q. candle_q_real q <= candle_fs_real (candle_fs_of_q_upper q)`,
  REWRITE_TAC[candle_fs_of_q_upper_real;
              candle_q_fixed_round_upper_sound]);;

let candle_fs_interval_of_q_sound = prove
 (`!i x. candle_q_interval_contains i x
         ==> candle_fs_interval_contains (candle_fs_interval_of_q i) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_fs_interval_contains_def;
              candle_fs_interval_of_q_def; FST; SND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC
      (SPEC
        `FST (i:((num#num)#num)#((num#num)#num))`
        candle_fs_of_q_lower_sound) THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC
      (SPEC
        `SND (i:((num#num)#num)#((num#num)#num))`
        candle_fs_of_q_upper_sound) THEN
    ASM_REAL_ARITH_TAC]);;

let candle_fs_interval_constant_sound = prove
 (`!q. candle_fs_interval_contains
         (candle_fs_interval_constant q) (candle_q_real q)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_interval_constant_def; FST; SND;
              candle_fs_of_q_lower_sound; candle_fs_of_q_upper_sound]);;

let candle_fs_interval_neg_sound = prove
 (`!i x. candle_fs_interval_contains i x
         ==> candle_fs_interval_contains (candle_fs_interval_neg i) (--x)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_interval_neg_def; candle_fs_raw_neg_real_scaled;
              FST; SND] THEN
  REAL_ARITH_TAC);;

let candle_fs_interval_add_sound = prove
 (`!i j x y.
     candle_fs_interval_contains i x /\
     candle_fs_interval_contains j y
     ==> candle_fs_interval_contains (candle_fs_interval_add i j) (x + y)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_interval_add_def; candle_fs_add_real;
              FST; SND] THEN
  REAL_ARITH_TAC);;

(* Directed division is the only lossy scalar boundary in the polynomial     *)
(* backend.  These lemmas are independent of the chosen Taylor scale.        *)

let candle_nat_floor_div_le = prove
 (`!numerator denominator. ~(denominator = 0)
     ==> &((numerator DIV denominator):num) <=
         &numerator / &denominator`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < denominator` ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT] THEN
  MATCH_MP_TAC (REAL_ARITH `y * x <= z ==> x * y <= z`) THEN
  MP_TAC (SPECL [`numerator:num`; `denominator:num`] DIV_MUL_LE) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL]);;

let candle_nat_le_ceil_div = prove
 (`!numerator denominator. ~(denominator = 0)
     ==> &numerator / &denominator <=
         &(candle_q_ceil_div numerator denominator)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < denominator` ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT] THEN
  MP_TAC
    (SPECL [`denominator:num`; `numerator:num`]
      candle_q_ceil_div_step) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; REAL_OF_NUM_MUL]);;

let candle_fs_floor_div_sound = prove
 (`!z denominator. ~(denominator = 0)
     ==> candle_lc_zreal (candle_fs_floor_div z denominator) <=
         candle_lc_zreal z / &denominator`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fs_floor_div_def; candle_lc_zreal_def; FST; SND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND] THENL
   [SUBGOAL_THEN `&(p2 - p1) = &p2 - &p1` ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_OF_NUM_SUB; LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC (SPECL [`(p2 - p1):num`; `denominator:num`]
      candle_nat_le_ceil_div) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&(p1 - p2) = &p1 - &p2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT];
      ALL_TAC] THEN
    MP_TAC (SPECL [`(p1 - p2):num`; `denominator:num`]
      candle_nat_floor_div_le) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC]);;

let candle_fs_ceil_div_sound = prove
 (`!z denominator. ~(denominator = 0)
     ==> candle_lc_zreal z / &denominator <=
         candle_lc_zreal (candle_fs_ceil_div z denominator)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fs_ceil_div_def; candle_lc_zreal_def; FST; SND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND] THENL
   [SUBGOAL_THEN `&(p2 - p1) = &p2 - &p1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB; LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC (SPECL [`(p2 - p1):num`; `denominator:num`]
      candle_nat_floor_div_le) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&(p1 - p2) = &p1 - &p2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_SUB; GSYM NOT_LT];
      ALL_TAC] THEN
    MP_TAC (SPECL [`(p1 - p2):num`; `denominator:num`]
      candle_nat_le_ceil_div) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC]);;

let candle_fs_raw_real_divide = prove
 (`!denominator z. 0 < denominator
     ==> candle_fs_raw_real (denominator * candle_fs_scale) z =
         (candle_lc_zreal z / &denominator) / &candle_fs_scale`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_raw_real_def; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC candle_fs_scale_pos THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  CONV_TAC REAL_FIELD);;

let candle_fs_floor_div_scaled_sound = prove
 (`!z denominator. 0 < denominator
     ==> candle_fs_real (candle_fs_floor_div z denominator) <=
         candle_fs_raw_real (denominator * candle_fs_scale) z`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_fs_real_def; candle_fs_raw_real_divide] THEN
  SUBGOAL_THEN `&0 < &(candle_fs_scale)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; candle_fs_scale_pos];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC candle_fs_floor_div_sound THEN ASM_ARITH_TAC);;

let candle_fs_ceil_div_scaled_sound = prove
 (`!z denominator. 0 < denominator
     ==> candle_fs_raw_real (denominator * candle_fs_scale) z <=
         candle_fs_real (candle_fs_ceil_div z denominator)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_fs_real_def; candle_fs_raw_real_divide] THEN
  SUBGOAL_THEN `&0 < &(candle_fs_scale)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; candle_fs_scale_pos];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC candle_fs_ceil_div_sound THEN ASM_ARITH_TAC);;

let candle_fs_raw_interval_round_sound = prove
 (`!denominator i x. 0 < denominator /\
     candle_fs_raw_interval_contains
       (denominator * candle_fs_scale) i x
     ==> candle_fs_interval_contains
           (candle_fs_raw_interval_round denominator i) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_raw_interval_contains_def;
              candle_fs_interval_contains_def;
              candle_fs_raw_interval_round_def; FST; SND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `candle_fs_raw_real (denominator * candle_fs_scale)
        (FST (i:(num#num)#(num#num)))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_fs_floor_div_scaled_sound THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `candle_fs_raw_real (denominator * candle_fs_scale)
        (SND (i:(num#num)#(num#num)))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_fs_ceil_div_scaled_sound THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_interval_mul_sound = prove
 (`!i j x y.
     candle_fs_interval_contains i x /\
     candle_fs_interval_contains j y
     ==> candle_fs_interval_contains
           (candle_fs_raw_interval_round candle_fs_scale
             (candle_fs_raw_interval_mul i j))
           (x * y)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_raw_interval_round_sound THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC candle_fs_scale_pos;
    MATCH_MP_TAC candle_fs_raw_interval_mul_sound THEN
    ASM_REWRITE_TAC[]]);;

end;;
