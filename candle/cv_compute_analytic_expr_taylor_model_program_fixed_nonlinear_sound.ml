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

end;;
