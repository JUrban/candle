(* ========================================================================== *)
(* Component contract for the supplied historical square root of 4 * x0.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_delta_x4_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_root_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_x4_sound;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_fixed_scale_sound;;

let candle_fs_hist_four_x0_real_def = new_definition
 `candle_fs_hist_four_x0_real (values:num->real) = &4 * values 0`;;

let candle_fs_hist_four_x0_gradient_real_def = new_definition
 `candle_fs_hist_four_x0_gradient_real coordinate =
    if coordinate = 0 then &4 else &0`;;

let candle_fs_hist_four_x0_hessian_real_def = new_definition
 `candle_fs_hist_four_x0_hessian_real i j = &0`;;

let candle_fs_hist_four_x0_gradient_def = new_definition
 `candle_fs_hist_four_x0_gradient =
    [candle_fs_angle_interval_scale 4 candle_fs_interval_one;
     candle_fs_interval_zero;
     candle_fs_interval_zero;
     candle_fs_interval_zero;
     candle_fs_interval_zero;
     candle_fs_interval_zero]`;;

let candle_fs_hist_four_x0_second_def = new_definition
 `candle_fs_hist_four_x0_second boxes =
    candle_fs_hist_second_make
      (candle_fs_angle_interval_scale 4
        (candle_fs_interval_lookup 0 boxes))
      candle_fs_hist_four_x0_gradient
      (candle_fs_interval_zero_matrix boxes boxes)`;;

let candle_fs_hist_four_x0_gradient_contains = prove
 (`ALL2 candle_fs_interval_contains
     candle_fs_hist_four_x0_gradient
     (list_of_seq candle_fs_hist_four_x0_gradient_real 6)`,
  REWRITE_TAC[candle_fs_hist_four_x0_gradient_def;
              candle_fs_hist_four_x0_gradient_real_def;
              num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND; o_THM;
              ALL2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [MATCH_ACCEPT_TAC candle_fs_interval_zero_contains;
    MP_TAC
      (SPECL
        [`4`; `candle_fs_interval_one`; `&1`]
        candle_fs_angle_interval_scale_contains) THEN
    REWRITE_TAC[candle_fs_interval_one_contains; REAL_MUL_RID]]);;

let candle_fs_hist_four_x0_hessian_real_row = prove
 (`!i. candle_fs_hist_four_x0_hessian_real i = (\j. &0)`,
  REWRITE_TAC[FUN_EQ_THM;
              candle_fs_hist_four_x0_hessian_real_def]);;

let candle_fs_hist_four_x0_hessian_contains = prove
 (`!boxes.
     LENGTH boxes = 6
     ==> ALL2 (ALL2 candle_fs_interval_contains)
           (candle_fs_interval_zero_matrix boxes boxes)
           (list_of_seq
             (\i. list_of_seq
               (candle_fs_hist_four_x0_hessian_real i) 6) 6)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`boxes:((num#num)#(num#num))list`;
       `boxes:((num#num)#(num#num))list`]
      candle_fs_interval_zero_matrix_contains) THEN
  ASM_REWRITE_TAC[candle_fs_hist_four_x0_hessian_real_row]);;

let candle_fs_hist_four_x0_hessian_real_symmetric = prove
 (`!i j.
     candle_fs_hist_four_x0_hessian_real i j =
     candle_fs_hist_four_x0_hessian_real j i`,
  REWRITE_TAC[candle_fs_hist_four_x0_hessian_real_def]);;

let candle_fs_hist_four_x0_second_value_contains = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6)
     ==> candle_fs_interval_contains
           (candle_fs_hist_second_value
             (candle_fs_hist_four_x0_second boxes))
           (candle_fs_hist_four_x0_real values)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_four_x0_second_def;
              candle_fs_hist_second_value_def;
              candle_fs_hist_second_make_def;
              candle_fs_hist_four_x0_real_def; FST] THEN
  MATCH_MP_TAC candle_fs_angle_interval_scale_contains THEN
  MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_four_x0_second_data_shape = prove
 (`!boxes.
     LENGTH boxes = 6
     ==> LENGTH
           (candle_fs_hist_second_gradient
             (candle_fs_hist_four_x0_second boxes)) = 6 /\
         LENGTH
           (candle_fs_hist_second_hessian
             (candle_fs_hist_four_x0_second boxes)) = 6 /\
         ALL (\row. LENGTH row = 6)
           (candle_fs_hist_second_hessian
             (candle_fs_hist_four_x0_second boxes))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_fs_hist_four_x0_second_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_hessian_def;
              candle_fs_hist_second_make_def; FST; SND] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_fs_hist_four_x0_gradient_def; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV;
    MP_TAC
      (SPECL
        [`boxes:((num#num)#(num#num))list`;
         `boxes:((num#num)#(num#num))list`]
        candle_fs_interval_zero_matrix_shape) THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_four_x0_second_to_q_shape = prove
 (`!boxes.
     LENGTH boxes = 6
     ==> candle_q_dim_jet_shape 6
           (candle_fs_hist_second_to_q
             (candle_fs_hist_four_x0_second boxes))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_second_to_q_def;
              candle_fs_first_to_q_shape;
              candle_fs_first_make_def;
              candle_fs_first_gradient_def;
              candle_fs_hist_four_x0_second_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_hessian_def;
              candle_fs_hist_second_make_def; FST; SND;
              candle_fs_hist_four_x0_gradient_def; LENGTH] THEN
  MP_TAC
    (SPECL
      [`boxes:((num#num)#(num#num))list`;
       `boxes:((num#num)#(num#num))list`]
      candle_fs_interval_zero_matrix_shape) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_four_x0_second_components = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6)
     ==> candle_q_dim_jet_contains_components 6
           (candle_fs_hist_second_to_q
             (candle_fs_hist_four_x0_second boxes))
           (candle_fs_hist_four_x0_real values)
           candle_fs_hist_four_x0_gradient_real
           candle_fs_hist_four_x0_hessian_real`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_second_to_q_def] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM candle_fs_hist_second_to_q_def] THEN
    MATCH_MP_TAC candle_fs_hist_four_x0_second_to_q_shape THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_first_value_def;
                candle_fs_first_make_def; FST] THEN
    MATCH_MP_TAC candle_fs_hist_four_x0_second_value_contains THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_first_gradient_def;
                candle_fs_first_make_def; SND;
                candle_fs_hist_four_x0_second_def;
                candle_fs_hist_second_gradient_def;
                candle_fs_hist_second_make_def; FST] THEN
    MATCH_ACCEPT_TAC candle_fs_hist_four_x0_gradient_contains;
    REWRITE_TAC[candle_fs_hist_four_x0_second_def;
                candle_fs_hist_second_hessian_def;
                candle_fs_hist_second_make_def; SND] THEN
    MATCH_MP_TAC candle_fs_hist_four_x0_hessian_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_root_four_x0_components = prove
 (`!boxes (values:num->real)
      input_lower input_upper root_lower root_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     candle_fs_hist_second_value
       (candle_fs_hist_four_x0_second boxes) =
       ((input_lower,0),(input_upper,0)) /\
     0 < input_lower /\ input_lower <= input_upper /\
     0 < root_lower /\ root_lower <= root_upper /\
     &0 < candle_fs_hist_four_x0_real values /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values))
     ==>
     candle_q_dim_jet_contains_components 6
       (candle_fs_hist_second_to_q
         (candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_four_x0_second boxes)
           ((root_lower,0),(root_upper,0))))
       (sqrt (candle_fs_hist_four_x0_real values))
       (\i.
          inv
            (sqrt (candle_fs_hist_four_x0_real values) +
             sqrt (candle_fs_hist_four_x0_real values)) *
          candle_fs_hist_four_x0_gradient_real i)
       (\i j.
          (--inv
            ((sqrt (candle_fs_hist_four_x0_real values) +
              sqrt (candle_fs_hist_four_x0_real values)) *
             (candle_fs_hist_four_x0_real values +
              candle_fs_hist_four_x0_real values))) *
            (candle_fs_hist_four_x0_gradient_real i *
             candle_fs_hist_four_x0_gradient_real j) +
          inv
            (sqrt (candle_fs_hist_four_x0_real values) +
             sqrt (candle_fs_hist_four_x0_real values)) *
            candle_fs_hist_four_x0_hessian_real i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      ((input_lower,0),(input_upper,0))
      (candle_fs_hist_four_x0_real values)`
  ASSUME_TAC THENL
   [MP_TAC
      (SPECL
        [`boxes:((num#num)#(num#num))list`; `values:num->real`]
        candle_fs_hist_four_x0_second_value_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (ISPEC `boxes:((num#num)#(num#num))list`
      candle_fs_hist_four_x0_second_data_shape) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC
    [GSYM (ISPEC `candle_fs_hist_four_x0_second boxes`
      candle_fs_hist_second_eta)] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_fs_hist_second_sqrt_supplied_components THEN
  ASM_REWRITE_TAC[candle_fs_hist_four_x0_hessian_real_symmetric] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_fs_hist_four_x0_second_def;
                candle_fs_hist_second_gradient_def;
                candle_fs_hist_second_make_def; FST; SND] THEN
    MATCH_ACCEPT_TAC candle_fs_hist_four_x0_gradient_contains;
    REWRITE_TAC[candle_fs_hist_four_x0_second_def;
                candle_fs_hist_second_hessian_def;
                candle_fs_hist_second_make_def; FST; SND] THEN
    MATCH_MP_TAC candle_fs_hist_four_x0_hessian_contains THEN
    ASM_REWRITE_TAC[]]);;

end;;
