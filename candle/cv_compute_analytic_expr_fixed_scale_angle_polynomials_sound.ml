(* ========================================================================== *)
(* Logical representation of the reflected fixed-scale angle polynomials.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file establishes that the cval program    *)
(* represents ordinary HOL data.  Analytic containment and authenticated      *)
(* compiled-program dispatch are proved in the subsequent invariant layer.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_angle_polynomials_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound = struct

open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_compute;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_sound;;

let candle_fs_angle_interval_sum_def = define
 `(candle_fs_angle_interval_sum [] = candle_fs_interval_zero) /\
  (candle_fs_angle_interval_sum (CONS h t) =
     candle_fs_interval_add h (candle_fs_angle_interval_sum t))`;;

let candle_fs_angle_interval_scale_def = new_definition
 `candle_fs_angle_interval_scale factor
      (value:(num#num)#(num#num)) =
    (candle_lc_zscale factor (FST value),
     candle_lc_zscale factor (SND value))`;;

let candle_fs_angle_interval_scale_neg_two_def = new_definition
 `candle_fs_angle_interval_scale_neg_two value =
    candle_fs_interval_neg (candle_fs_angle_interval_scale 2 value)`;;

let candle_fs_angle_interval_mul_def = new_definition
 `candle_fs_angle_interval_mul left right =
    candle_fsn_interval_mul left right`;;

let candle_fs_angle_delta_value_def = new_definition
 `candle_fs_angle_delta_value environment =
    let x0 = candle_fs_interval_lookup 0 environment in
    let x1 = candle_fs_interval_lookup 1 environment in
    let x2 = candle_fs_interval_lookup 2 environment in
    let x3 = candle_fs_interval_lookup 3 environment in
    let x4 = candle_fs_interval_lookup 4 environment in
    let x5 = candle_fs_interval_lookup 5 environment in
    let l0 = candle_fs_angle_interval_sum
      [candle_fs_interval_neg x0; x1; x2;
       candle_fs_interval_neg x3; x4; x5] in
    let l1 = candle_fs_angle_interval_sum
      [x0; candle_fs_interval_neg x1; x2; x3;
       candle_fs_interval_neg x4; x5] in
    let l2 = candle_fs_angle_interval_sum
      [x0; x1; candle_fs_interval_neg x2; x3; x4;
       candle_fs_interval_neg x5] in
    let p03 = candle_fs_angle_interval_mul x0 x3 in
    let p14 = candle_fs_angle_interval_mul x1 x4 in
    let p25 = candle_fs_angle_interval_mul x2 x5 in
    candle_fs_angle_interval_sum
      [candle_fs_angle_interval_mul p03 l0;
       candle_fs_angle_interval_mul p14 l1;
       candle_fs_angle_interval_mul p25 l2;
       candle_fs_interval_neg
         (candle_fs_angle_interval_mul
           (candle_fs_angle_interval_mul x1 x2) x3);
       candle_fs_interval_neg
         (candle_fs_angle_interval_mul
           (candle_fs_angle_interval_mul x0 x2) x4);
       candle_fs_interval_neg
         (candle_fs_angle_interval_mul
           (candle_fs_angle_interval_mul x0 x1) x5);
       candle_fs_interval_neg
         (candle_fs_angle_interval_mul
           (candle_fs_angle_interval_mul x3 x4) x5)]`;;

let candle_fs_angle_delta_gradient_def = new_definition
 `candle_fs_angle_delta_gradient environment =
    let x0 = candle_fs_interval_lookup 0 environment in
    let x1 = candle_fs_interval_lookup 1 environment in
    let x2 = candle_fs_interval_lookup 2 environment in
    let x3 = candle_fs_interval_lookup 3 environment in
    let x4 = candle_fs_interval_lookup 4 environment in
    let x5 = candle_fs_interval_lookup 5 environment in
    let p00 = candle_fs_angle_interval_mul x0 x0 in
    let p01 = candle_fs_angle_interval_mul x0 x1 in
    let p02 = candle_fs_angle_interval_mul x0 x2 in
    let p03 = candle_fs_angle_interval_mul x0 x3 in
    let p04 = candle_fs_angle_interval_mul x0 x4 in
    let p05 = candle_fs_angle_interval_mul x0 x5 in
    let p11 = candle_fs_angle_interval_mul x1 x1 in
    let p12 = candle_fs_angle_interval_mul x1 x2 in
    let p13 = candle_fs_angle_interval_mul x1 x3 in
    let p14 = candle_fs_angle_interval_mul x1 x4 in
    let p15 = candle_fs_angle_interval_mul x1 x5 in
    let p22 = candle_fs_angle_interval_mul x2 x2 in
    let p23 = candle_fs_angle_interval_mul x2 x3 in
    let p24 = candle_fs_angle_interval_mul x2 x4 in
    let p25 = candle_fs_angle_interval_mul x2 x5 in
    let p33 = candle_fs_angle_interval_mul x3 x3 in
    let p34 = candle_fs_angle_interval_mul x3 x4 in
    let p35 = candle_fs_angle_interval_mul x3 x5 in
    let p44 = candle_fs_angle_interval_mul x4 x4 in
    let p45 = candle_fs_angle_interval_mul x4 x5 in
    let p55 = candle_fs_angle_interval_mul x5 x5 in
    [candle_fs_angle_interval_sum
       [candle_fs_angle_interval_scale_neg_two p03; p13; p14;
        candle_fs_interval_neg p15; p23; candle_fs_interval_neg p24; p25;
        candle_fs_interval_neg p33; p34; p35];
     candle_fs_angle_interval_sum
       [p03; p04; candle_fs_interval_neg p05;
        candle_fs_angle_interval_scale_neg_two p14;
        candle_fs_interval_neg p23; p24; p25; p34;
        candle_fs_interval_neg p44; p45];
     candle_fs_angle_interval_sum
       [p03; candle_fs_interval_neg p04; p05;
        candle_fs_interval_neg p13; p14; p15;
        candle_fs_angle_interval_scale_neg_two p25; p35; p45;
        candle_fs_interval_neg p55];
     candle_fs_angle_interval_sum
       [candle_fs_interval_neg p00; p01; p02;
        candle_fs_angle_interval_scale_neg_two p03; p04; p05;
        candle_fs_interval_neg p12; p14; p25;
        candle_fs_interval_neg p45];
     candle_fs_angle_interval_sum
       [p01; candle_fs_interval_neg p02; p03;
        candle_fs_interval_neg p11; p12; p13;
        candle_fs_angle_interval_scale_neg_two p14; p15; p25;
        candle_fs_interval_neg p35];
     candle_fs_angle_interval_sum
       [candle_fs_interval_neg p01; p02; p03; p12; p14;
        candle_fs_interval_neg p22; p23; p24;
        candle_fs_angle_interval_scale_neg_two p25;
        candle_fs_interval_neg p34]]`;;

let candle_fs_angle_delta_hessian_def = new_definition
 `candle_fs_angle_delta_hessian environment =
    let x0 = candle_fs_interval_lookup 0 environment in
    let x1 = candle_fs_interval_lookup 1 environment in
    let x2 = candle_fs_interval_lookup 2 environment in
    let x3 = candle_fs_interval_lookup 3 environment in
    let x4 = candle_fs_interval_lookup 4 environment in
    let x5 = candle_fs_interval_lookup 5 environment in
    let h00 = candle_fs_angle_interval_scale_neg_two x3 in
    let h01 = candle_fs_angle_interval_sum
      [x3; x4; candle_fs_interval_neg x5] in
    let h02 = candle_fs_angle_interval_sum
      [x3; candle_fs_interval_neg x4; x5] in
    let h03 = candle_fs_angle_interval_sum
      [candle_fs_angle_interval_scale_neg_two x0; x1; x2;
       candle_fs_angle_interval_scale_neg_two x3; x4; x5] in
    let h04 = candle_fs_angle_interval_sum
      [x1; candle_fs_interval_neg x2; x3] in
    let h05 = candle_fs_angle_interval_sum
      [candle_fs_interval_neg x1; x2; x3] in
    let h11 = candle_fs_angle_interval_scale_neg_two x4 in
    let h12 = candle_fs_angle_interval_sum
      [candle_fs_interval_neg x3; x4; x5] in
    let h13 = candle_fs_angle_interval_sum
      [x0; candle_fs_interval_neg x2; x4] in
    let h14 = candle_fs_angle_interval_sum
      [x0; candle_fs_angle_interval_scale_neg_two x1; x2; x3;
       candle_fs_angle_interval_scale_neg_two x4; x5] in
    let h15 = candle_fs_angle_interval_sum
      [candle_fs_interval_neg x0; x2; x4] in
    let h22 = candle_fs_angle_interval_scale_neg_two x5 in
    let h23 = candle_fs_angle_interval_sum
      [x0; candle_fs_interval_neg x1; x5] in
    let h24 = candle_fs_angle_interval_sum
      [candle_fs_interval_neg x0; x1; x5] in
    let h25 = candle_fs_angle_interval_sum
      [x0; x1; candle_fs_angle_interval_scale_neg_two x2; x3; x4;
       candle_fs_angle_interval_scale_neg_two x5] in
    let h33 = candle_fs_angle_interval_scale_neg_two x0 in
    let h34 = candle_fs_angle_interval_sum
      [x0; x1; candle_fs_interval_neg x5] in
    let h35 = candle_fs_angle_interval_sum
      [x0; x2; candle_fs_interval_neg x4] in
    let h44 = candle_fs_angle_interval_scale_neg_two x1 in
    let h45 = candle_fs_angle_interval_sum
      [x1; x2; candle_fs_interval_neg x3] in
    let h55 = candle_fs_angle_interval_scale_neg_two x2 in
    [[h00; h01; h02; h03; h04; h05];
     [h01; h11; h12; h13; h14; h15];
     [h02; h12; h22; h23; h24; h25];
     [h03; h13; h23; h33; h34; h35];
     [h04; h14; h24; h34; h44; h45];
     [h05; h15; h25; h35; h45; h55]]`;;

let candle_fs_angle_delta_hessian_length = prove
 (`!environment.
     LENGTH (candle_fs_angle_delta_hessian environment) = 6`,
  REWRITE_TAC[candle_fs_angle_delta_hessian_def;
              LET_DEF; LET_END_DEF; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_angle_matrix_row_lookup_def = define
 `(candle_fs_angle_matrix_row_lookup rowindex [] = []) /\
  (candle_fs_angle_matrix_row_lookup 0 (CONS h t) = h) /\
  (candle_fs_angle_matrix_row_lookup (SUC n) (CONS h t) =
     candle_fs_angle_matrix_row_lookup n t)`;;

let candle_fs_angle_matrix_lookup_def = new_definition
 `candle_fs_angle_matrix_lookup rowindex colindex matrixvalue =
    candle_fs_interval_lookup colindex
      (candle_fs_angle_matrix_row_lookup rowindex matrixvalue)`;;

let candle_fs_angle_q_gradient_entry_def = new_definition
 `candle_fs_angle_q_gradient_entry
      coordinate x0 deltavalue delta_gradient =
    candle_fs_angle_interval_scale 4
      (candle_fs_interval_add
        (candle_fs_angle_interval_mul x0
          (candle_fs_interval_lookup coordinate delta_gradient))
        (if coordinate = 0 then deltavalue else candle_fs_interval_zero))`;;

let candle_fs_angle_q_hessian_entry_def = new_definition
 `candle_fs_angle_q_hessian_entry
      rowindex colindex x0 delta_gradient delta_hessian =
    candle_fs_angle_interval_scale 4
      (candle_fs_interval_add
        (candle_fs_interval_add
          (candle_fs_angle_interval_mul x0
            (candle_fs_angle_matrix_lookup
              rowindex colindex delta_hessian))
          (if rowindex = 0 then
             candle_fs_interval_lookup colindex delta_gradient
           else candle_fs_interval_zero))
        (if colindex = 0 then
           candle_fs_interval_lookup rowindex delta_gradient
         else candle_fs_interval_zero))`;;

let candle_fs_angle_q_hessian_def = new_definition
 `candle_fs_angle_q_hessian x0 delta_gradient delta_hessian =
    MAP (\rowindex.
      MAP (\colindex.
        candle_fs_angle_q_hessian_entry
          rowindex colindex x0 delta_gradient delta_hessian)
        [0;1;2;3;4;5]) [0;1;2;3;4;5]`;;

let candle_fs_angle_four_x0_delta_def = new_definition
 `candle_fs_angle_four_x0_delta center_environment box_environment radii =
    let center_x0 = candle_fs_interval_lookup 0 center_environment in
    let box_x0 = candle_fs_interval_lookup 0 box_environment in
    let center_delta = candle_fs_angle_delta_value center_environment in
    let center_delta_gradient =
      candle_fs_angle_delta_gradient center_environment in
    let box_delta_hessian =
      candle_fs_angle_delta_hessian box_environment in
    let box_delta_gradient =
      candle_fs_gradient_bounds radii center_delta_gradient
        box_delta_hessian in
    let center_gradient =
      MAP (\coordinate.
        candle_fs_angle_q_gradient_entry
          coordinate center_x0 center_delta center_delta_gradient)
        [0;1;2;3;4;5] in
    let box_hessian =
      candle_fs_angle_q_hessian box_x0 box_delta_gradient
        box_delta_hessian in
    candle_fs_result_complete_rounded radii T
      (candle_fs_first_make
        (candle_fs_angle_interval_scale 4
          (candle_fs_angle_interval_mul center_x0 center_delta))
        center_gradient)
      box_hessian`;;

(* -------------------------------------------------------------------------- *)
(* Executable representation.                                                *)
(* -------------------------------------------------------------------------- *)

let candle_cv_fs_angle_six_correct = prove
 (`!a b c d e f.
     candle_cv_fs_angle_six
       (candle_cv_fs_interval a) (candle_cv_fs_interval b)
       (candle_cv_fs_interval c) (candle_cv_fs_interval d)
       (candle_cv_fs_interval e) (candle_cv_fs_interval f) =
     candle_cv_fs_interval_list [a;b;c;d;e;f]`,
  REWRITE_TAC[candle_cv_fs_angle_six_def;
              candle_cv_fs_interval_list_def]);;

let candle_cv_fs_angle_three_correct = prove
 (`!a b c.
     Cexp_pair (candle_cv_fs_interval a)
       (Cexp_pair (candle_cv_fs_interval b)
         (Cexp_pair (candle_cv_fs_interval c) (Cexp_num 0))) =
     candle_cv_fs_interval_list [a;b;c]`,
  REWRITE_TAC[candle_cv_fs_interval_list_def]);;

let candle_cv_fs_angle_matrix_six_correct = prove
 (`!a b c d e f.
     candle_cv_fs_angle_six
       (candle_cv_fs_interval_list a) (candle_cv_fs_interval_list b)
       (candle_cv_fs_interval_list c) (candle_cv_fs_interval_list d)
       (candle_cv_fs_interval_list e) (candle_cv_fs_interval_list f) =
     candle_cv_fs_interval_matrix [a;b;c;d;e;f]`,
  REWRITE_TAC[candle_cv_fs_angle_six_def;
              candle_cv_fs_interval_matrix_def]);;

let candle_cv_fs_angle_seven_correct = prove
 (`!a b c d e f g.
     candle_cv_fs_angle_seven
       (candle_cv_fs_interval a) (candle_cv_fs_interval b)
       (candle_cv_fs_interval c) (candle_cv_fs_interval d)
       (candle_cv_fs_interval e) (candle_cv_fs_interval f)
       (candle_cv_fs_interval g) =
     candle_cv_fs_interval_list [a;b;c;d;e;f;g]`,
  REWRITE_TAC[candle_cv_fs_angle_seven_def;
              candle_cv_fs_interval_list_def]);;

let candle_cv_fs_angle_ten_correct = prove
 (`!a b c d e f g h i j.
     candle_cv_fs_angle_ten
       (candle_cv_fs_interval a) (candle_cv_fs_interval b)
       (candle_cv_fs_interval c) (candle_cv_fs_interval d)
       (candle_cv_fs_interval e) (candle_cv_fs_interval f)
       (candle_cv_fs_interval g) (candle_cv_fs_interval h)
       (candle_cv_fs_interval i) (candle_cv_fs_interval j) =
     candle_cv_fs_interval_list [a;b;c;d;e;f;g;h;i;j]`,
  REWRITE_TAC[candle_cv_fs_angle_ten_def;
              candle_cv_fs_interval_list_def]);;

let candle_cv_fs_angle_interval_sum_correct = prove
 (`!items.
     candle_cv_fs_angle_interval_sum
       (candle_cv_fs_interval_list items) =
     candle_cv_fs_interval (candle_fs_angle_interval_sum items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_angle_interval_sum_def;
                  candle_fs_angle_interval_sum_def;
                  candle_cv_fs_interval_list_def;
                  candle_cv_fs_interval_zero_correct;
                  candle_cv_fs_interval_add_correct]);;

let candle_cv_fs_angle_interval_scale_correct = prove
 (`!factor value.
     candle_cv_fs_angle_interval_scale (Cexp_num factor)
       (candle_cv_fs_interval value) =
     candle_cv_fs_interval
       (candle_fs_angle_interval_scale factor value)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_angle_interval_scale_def;
              candle_fs_angle_interval_scale_def;
              candle_cv_fs_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_fs_raw_scale_correct; FST; SND]);;

let candle_cv_fs_angle_interval_scale_neg_two_correct = prove
 (`!value.
     candle_cv_fs_angle_interval_scale_neg_two
       (candle_cv_fs_interval value) =
     candle_cv_fs_interval
       (candle_fs_angle_interval_scale_neg_two value)`,
  REWRITE_TAC[candle_cv_fs_angle_interval_scale_neg_two_def;
              candle_fs_angle_interval_scale_neg_two_def;
              candle_cv_fs_angle_interval_scale_correct;
              candle_cv_fs_interval_neg_correct]);;

let candle_cv_fs_angle_interval_mul_correct = prove
 (`!left right.
     candle_cv_fs_angle_interval_mul
       (candle_cv_fs_interval left) (candle_cv_fs_interval right) =
     candle_cv_fs_interval
       (candle_fs_angle_interval_mul left right)`,
  REWRITE_TAC[candle_cv_fs_angle_interval_mul_def;
              candle_fs_angle_interval_mul_def;
              candle_fsn_interval_mul_def;
              candle_cv_fs_scale_correct;
              candle_cv_fs_raw_interval_mul_correct;
              candle_cv_fs_raw_interval_round_correct]);;

let candle_cv_fs_angle_delta_value_correct = prove
 (`!environment.
     candle_cv_fs_angle_delta_value
       (candle_cv_fs_interval_list environment) =
     candle_cv_fs_interval
       (candle_fs_angle_delta_value environment)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_angle_delta_value_def;
              candle_fs_angle_delta_value_def;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_interval_neg_correct;
              candle_cv_fs_angle_six_correct;
              candle_cv_fs_angle_seven_correct;
              candle_cv_fs_angle_interval_sum_correct;
              candle_cv_fs_angle_interval_mul_correct;
              LET_DEF; LET_END_DEF]);;

let candle_cv_fs_angle_delta_gradient_correct = prove
 (`!environment.
     candle_cv_fs_angle_delta_gradient
       (candle_cv_fs_interval_list environment) =
     candle_cv_fs_interval_list
       (candle_fs_angle_delta_gradient environment)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_angle_delta_gradient_def;
              candle_fs_angle_delta_gradient_def;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_interval_neg_correct;
              candle_cv_fs_angle_interval_scale_neg_two_correct;
              candle_cv_fs_angle_interval_mul_correct;
              LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[candle_cv_fs_angle_ten_correct;
              candle_cv_fs_angle_interval_sum_correct;
              candle_cv_fs_angle_six_correct]);;

let candle_cv_fs_angle_delta_hessian_correct = prove
 (`!environment.
     candle_cv_fs_angle_delta_hessian
       (candle_cv_fs_interval_list environment) =
     candle_cv_fs_interval_matrix
       (candle_fs_angle_delta_hessian environment)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_angle_delta_hessian_def;
              candle_fs_angle_delta_hessian_def;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_interval_neg_correct;
              candle_cv_fs_angle_interval_scale_neg_two_correct;
              LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[candle_cv_fs_angle_three_correct;
              candle_cv_fs_angle_six_correct;
              candle_cv_fs_angle_interval_sum_correct;
              candle_cv_fs_angle_matrix_six_correct]);;

let candle_cv_fs_angle_matrix_row_lookup_correct = prove
 (`!rowindex matrixvalue.
     rowindex < LENGTH matrixvalue
     ==>
     candle_cv_fs_interval_lookup (Cexp_num rowindex)
       (candle_cv_fs_interval_matrix matrixvalue) =
     candle_cv_fs_interval_list
       (candle_fs_angle_matrix_row_lookup rowindex matrixvalue)`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_lookup_def;
                  candle_cv_fs_interval_matrix_def;
                  candle_cv_fs_interval_list_def;
                  candle_fs_angle_matrix_row_lookup_def;
                  LENGTH; LT; LT_SUC]);;

let candle_cv_fs_angle_matrix_lookup_correct = prove
 (`!rowindex colindex matrixvalue.
     rowindex < LENGTH matrixvalue
     ==>
     candle_cv_fs_angle_matrix_lookup
       (Cexp_num rowindex) (Cexp_num colindex)
       (candle_cv_fs_interval_matrix matrixvalue) =
     candle_cv_fs_interval
       (candle_fs_angle_matrix_lookup rowindex colindex matrixvalue)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_cv_fs_angle_matrix_lookup_def;
              candle_fs_angle_matrix_lookup_def] THEN
  SUBGOAL_THEN
   `candle_cv_fs_interval_lookup (Cexp_num rowindex)
      (candle_cv_fs_interval_matrix matrixvalue) =
    candle_cv_fs_interval_list
      (candle_fs_angle_matrix_row_lookup rowindex matrixvalue)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC candle_cv_fs_angle_matrix_row_lookup_correct THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_cv_fs_interval_lookup_correct]]);;

let candle_cv_fs_angle_q_gradient_entry_correct = prove
 (`!coordinate x0 deltavalue delta_gradient.
     candle_cv_fs_angle_q_gradient_entry
       (Cexp_num coordinate) (candle_cv_fs_interval x0)
       (candle_cv_fs_interval deltavalue)
       (candle_cv_fs_interval_list delta_gradient) =
     candle_cv_fs_interval
       (candle_fs_angle_q_gradient_entry
         coordinate x0 deltavalue delta_gradient)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_angle_q_gradient_entry_def;
              candle_fs_angle_q_gradient_entry_def;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_angle_interval_mul_correct;
              candle_cv_fs_interval_add_correct;
              candle_cv_fs_angle_interval_scale_correct;
              cexp_eq_def; injectivity "cval"] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_zero_correct; cexp_if_def] THEN
  REWRITE_TAC[candle_cv_fs_interval_add_correct;
              candle_cv_fs_angle_interval_scale_correct]);;

let candle_cv_fs_angle_q_hessian_entry_correct = prove
 (`!rowindex colindex x0 delta_gradient delta_hessian.
     rowindex < LENGTH delta_hessian
     ==>
     candle_cv_fs_angle_q_hessian_entry
       (Cexp_num rowindex) (Cexp_num colindex)
       (candle_cv_fs_interval x0)
       (candle_cv_fs_interval_list delta_gradient)
       (candle_cv_fs_interval_matrix delta_hessian) =
     candle_cv_fs_interval
       (candle_fs_angle_q_hessian_entry
         rowindex colindex x0 delta_gradient delta_hessian)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_cv_fs_angle_q_hessian_entry_def;
              candle_fs_angle_q_hessian_entry_def] THEN
  SUBGOAL_THEN
   `candle_cv_fs_angle_matrix_lookup
      (Cexp_num rowindex) (Cexp_num colindex)
      (candle_cv_fs_interval_matrix delta_hessian) =
    candle_cv_fs_interval
      (candle_fs_angle_matrix_lookup
        rowindex colindex delta_hessian)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC candle_cv_fs_angle_matrix_lookup_correct THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_lookup_correct;
                  candle_cv_fs_angle_interval_mul_correct;
                  candle_cv_fs_interval_add_correct;
                  candle_cv_fs_angle_interval_scale_correct;
                  cexp_eq_def; injectivity "cval"] THEN
  REPEAT(COND_CASES_TAC THEN
    ASM_REWRITE_TAC[candle_cv_fs_interval_zero_correct; cexp_if_def]) THEN
  ASM_REWRITE_TAC[candle_cv_fs_interval_lookup_correct;
                  candle_cv_fs_angle_interval_mul_correct;
                  candle_cv_fs_interval_zero_correct;
                  candle_cv_fs_interval_add_correct;
                  candle_cv_fs_angle_interval_scale_correct]);;

let candle_cv_fs_angle_q_hessian_row_correct = prove
 (`!rowindex x0 delta_gradient delta_hessian.
     rowindex < LENGTH delta_hessian
     ==>
     candle_cv_fs_angle_six
       (candle_cv_fs_angle_q_hessian_entry
         (Cexp_num rowindex) (Cexp_num 0)
         (candle_cv_fs_interval x0)
         (candle_cv_fs_interval_list delta_gradient)
         (candle_cv_fs_interval_matrix delta_hessian))
       (candle_cv_fs_angle_q_hessian_entry
         (Cexp_num rowindex) (Cexp_num 1)
         (candle_cv_fs_interval x0)
         (candle_cv_fs_interval_list delta_gradient)
         (candle_cv_fs_interval_matrix delta_hessian))
       (candle_cv_fs_angle_q_hessian_entry
         (Cexp_num rowindex) (Cexp_num 2)
         (candle_cv_fs_interval x0)
         (candle_cv_fs_interval_list delta_gradient)
         (candle_cv_fs_interval_matrix delta_hessian))
       (candle_cv_fs_angle_q_hessian_entry
         (Cexp_num rowindex) (Cexp_num 3)
         (candle_cv_fs_interval x0)
         (candle_cv_fs_interval_list delta_gradient)
         (candle_cv_fs_interval_matrix delta_hessian))
       (candle_cv_fs_angle_q_hessian_entry
         (Cexp_num rowindex) (Cexp_num 4)
         (candle_cv_fs_interval x0)
         (candle_cv_fs_interval_list delta_gradient)
         (candle_cv_fs_interval_matrix delta_hessian))
       (candle_cv_fs_angle_q_hessian_entry
         (Cexp_num rowindex) (Cexp_num 5)
         (candle_cv_fs_interval x0)
         (candle_cv_fs_interval_list delta_gradient)
         (candle_cv_fs_interval_matrix delta_hessian)) =
     candle_cv_fs_interval_list
       [candle_fs_angle_q_hessian_entry
          rowindex 0 x0 delta_gradient delta_hessian;
        candle_fs_angle_q_hessian_entry
          rowindex 1 x0 delta_gradient delta_hessian;
        candle_fs_angle_q_hessian_entry
          rowindex 2 x0 delta_gradient delta_hessian;
        candle_fs_angle_q_hessian_entry
          rowindex 3 x0 delta_gradient delta_hessian;
        candle_fs_angle_q_hessian_entry
          rowindex 4 x0 delta_gradient delta_hessian;
        candle_fs_angle_q_hessian_entry
          rowindex 5 x0 delta_gradient delta_hessian]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!colindex.
      candle_cv_fs_angle_q_hessian_entry
        (Cexp_num rowindex) (Cexp_num colindex)
        (candle_cv_fs_interval x0)
        (candle_cv_fs_interval_list delta_gradient)
        (candle_cv_fs_interval_matrix delta_hessian) =
      candle_cv_fs_interval
        (candle_fs_angle_q_hessian_entry
          rowindex colindex x0 delta_gradient delta_hessian)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MATCH_MP_TAC candle_cv_fs_angle_q_hessian_entry_correct THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[candle_cv_fs_angle_six_correct]]);;

let candle_cv_fs_angle_q_hessian_correct = prove
 (`!x0 delta_gradient delta_hessian.
     LENGTH delta_hessian = 6
     ==>
     candle_cv_fs_angle_q_hessian
       (candle_cv_fs_interval x0)
       (candle_cv_fs_interval_list delta_gradient)
       (candle_cv_fs_interval_matrix delta_hessian) =
     candle_cv_fs_interval_matrix
       (candle_fs_angle_q_hessian x0 delta_gradient delta_hessian)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `0 < LENGTH (delta_hessian:(((num#num)#(num#num))list)list)`
  ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `1 < LENGTH (delta_hessian:(((num#num)#(num#num))list)list)`
  ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `2 < LENGTH (delta_hessian:(((num#num)#(num#num))list)list)`
  ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `3 < LENGTH (delta_hessian:(((num#num)#(num#num))list)list)`
  ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `4 < LENGTH (delta_hessian:(((num#num)#(num#num))list)list)`
  ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `5 < LENGTH (delta_hessian:(((num#num)#(num#num))list)list)`
  ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC
   (SPECL [`0`; `x0:(num#num)#(num#num)`;
           `delta_gradient:((num#num)#(num#num))list`;
           `delta_hessian:(((num#num)#(num#num))list)list`]
     candle_cv_fs_angle_q_hessian_row_correct) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < 6`] THEN DISCH_TAC THEN
  MP_TAC
   (SPECL [`1`; `x0:(num#num)#(num#num)`;
           `delta_gradient:((num#num)#(num#num))list`;
           `delta_hessian:(((num#num)#(num#num))list)list`]
     candle_cv_fs_angle_q_hessian_row_correct) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 < 6`] THEN DISCH_TAC THEN
  MP_TAC
   (SPECL [`2`; `x0:(num#num)#(num#num)`;
           `delta_gradient:((num#num)#(num#num))list`;
           `delta_hessian:(((num#num)#(num#num))list)list`]
     candle_cv_fs_angle_q_hessian_row_correct) THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 < 6`] THEN DISCH_TAC THEN
  MP_TAC
   (SPECL [`3`; `x0:(num#num)#(num#num)`;
           `delta_gradient:((num#num)#(num#num))list`;
           `delta_hessian:(((num#num)#(num#num))list)list`]
     candle_cv_fs_angle_q_hessian_row_correct) THEN
  ASM_REWRITE_TAC[ARITH_RULE `3 < 6`] THEN DISCH_TAC THEN
  MP_TAC
   (SPECL [`4`; `x0:(num#num)#(num#num)`;
           `delta_gradient:((num#num)#(num#num))list`;
           `delta_hessian:(((num#num)#(num#num))list)list`]
     candle_cv_fs_angle_q_hessian_row_correct) THEN
  ASM_REWRITE_TAC[ARITH_RULE `4 < 6`] THEN DISCH_TAC THEN
  MP_TAC
   (SPECL [`5`; `x0:(num#num)#(num#num)`;
           `delta_gradient:((num#num)#(num#num))list`;
           `delta_hessian:(((num#num)#(num#num))list)list`]
     candle_cv_fs_angle_q_hessian_row_correct) THEN
  ASM_REWRITE_TAC[ARITH_RULE `5 < 6`] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fs_angle_q_hessian_def;
                  candle_fs_angle_q_hessian_def;
                  MAP] THEN
  REWRITE_TAC[candle_cv_fs_angle_matrix_six_correct]);;

let candle_cv_fs_angle_q_delta_hessian_correct = prove
 (`!x0 delta_gradient environment.
     candle_cv_fs_angle_q_hessian
       (candle_cv_fs_interval x0)
       (candle_cv_fs_interval_list delta_gradient)
       (candle_cv_fs_interval_matrix
         (candle_fs_angle_delta_hessian environment)) =
     candle_cv_fs_interval_matrix
       (candle_fs_angle_q_hessian x0 delta_gradient
         (candle_fs_angle_delta_hessian environment))`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC candle_cv_fs_angle_q_hessian_correct THEN
  REWRITE_TAC[candle_fs_angle_delta_hessian_length]);;

let candle_cv_fs_angle_four_x0_delta_correct = prove
 (`!center_environment box_environment radii.
     candle_cv_fs_angle_four_x0_delta
       (candle_cv_fs_interval_list center_environment)
       (candle_cv_fs_interval_list box_environment)
       (candle_cv_lc_vec radii) =
     candle_cv_fs_result
       (candle_fs_angle_four_x0_delta
         center_environment box_environment radii)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_angle_four_x0_delta_def;
              candle_fs_angle_four_x0_delta_def;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_angle_delta_value_correct;
              candle_cv_fs_angle_delta_gradient_correct;
              candle_cv_fs_angle_delta_hessian_correct;
              candle_cv_fs_gradient_bounds_correct;
              candle_cv_fs_angle_q_gradient_entry_correct;
              candle_cv_fs_angle_q_delta_hessian_correct;
              candle_cv_fs_angle_interval_mul_correct;
              candle_cv_fs_angle_interval_scale_correct;
              candle_cv_fs_angle_six_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_result_complete_true_correct;
              MAP; LET_DEF; LET_END_DEF]);;

let candle_cv_fs_angle_four_x0_delta_q_correct = prove
 (`!center_boxes boxes radii.
     candle_cv_fs_angle_four_x0_delta_q
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii) =
     candle_cv_fs_result
       (candle_fs_angle_four_x0_delta
         (candle_fs_interval_list_of_q center_boxes)
         (candle_fs_interval_list_of_q boxes)
         (candle_fs_list_of_q radii))`,
  REWRITE_TAC[candle_cv_fs_angle_four_x0_delta_q_def;
              candle_cv_fs_interval_list_of_q_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fs_angle_four_x0_delta_correct]);;

end;;
