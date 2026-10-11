(* ========================================================================== *)
(* Complete component contract for the historical delta_x4 second-order jet. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_delta_root_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_delta_x4_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_root_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_fixed_scale_sound;;

let candle_fs_hist_delta_x4_hessian_real_def = new_definition
 `candle_fs_hist_delta_x4_hessian_real =
    [[--(&2 * &1); &1; &1; --(&2 * &1); &1; &1];
     [&1; &0; -- &1; &0; &1; &0];
     [&1; -- &1; &0; &0; &0; &1];
     [--(&2 * &1); &0; &0; &0; &0; &0];
     [&1; &1; &0; &0; &0; -- &1];
     [&1; &0; &1; &0; -- &1; &0]]`;;

let candle_fs_hist_delta_x4_hessian_contains = prove
 (`ALL2 (ALL2 candle_fs_interval_contains)
     candle_fs_hist_delta_x4_hessian
     candle_fs_hist_delta_x4_hessian_real`,
  REWRITE_TAC[candle_fs_hist_delta_x4_hessian_def;
              candle_fs_hist_delta_x4_hessian_real_def;
              LET_DEF; LET_END_DEF; ALL2] THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [MATCH_ACCEPT_TAC candle_fs_interval_zero_contains;
    MATCH_ACCEPT_TAC candle_fs_interval_one_contains;
    MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_ACCEPT_TAC candle_fs_interval_one_contains;
    MATCH_MP_TAC candle_fs_hist_scale_neg_two_contains THEN
    MATCH_ACCEPT_TAC candle_fs_interval_one_contains]);;

let candle_fs_hist_delta_x4_hessian_real_length = prove
 (`LENGTH candle_fs_hist_delta_x4_hessian_real = 6`,
  REWRITE_TAC[candle_fs_hist_delta_x4_hessian_real_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_delta_x4_hessian_real_rows = prove
 (`ALL (\row. LENGTH (row:real list) = 6)
     candle_fs_hist_delta_x4_hessian_real`,
  REWRITE_TAC[candle_fs_hist_delta_x4_hessian_real_def; ALL; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_delta_x4_hessian_real_symmetric = prove
 (`!i j.
     i < 6 /\ j < 6
     ==> EL j (EL i candle_fs_hist_delta_x4_hessian_real) =
         EL i (EL j candle_fs_hist_delta_x4_hessian_real)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN
    `i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5`
   MP_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)]) THEN
  (SUBGOAL_THEN
    `j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5`
   MP_TAC THENL
    [ASM_ARITH_TAC;
     DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)]) THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_hessian_real_def] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  REFL_TAC);;

let candle_fs_hist_delta_x4_hessian_component_real_def = new_definition
 `candle_fs_hist_delta_x4_hessian_component_real i j =
    if i < 6 /\ j < 6 then
      EL j (EL i candle_fs_hist_delta_x4_hessian_real)
    else &0`;;

let candle_fs_hist_delta_x4_hessian_component_real_symmetric = prove
 (`!i j.
     candle_fs_hist_delta_x4_hessian_component_real i j =
     candle_fs_hist_delta_x4_hessian_component_real j i`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_hessian_component_real_def;
              CONJ_SYM] THEN
  ASM_CASES_TAC `i < 6 /\ j < 6` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_fs_hist_delta_x4_hessian_real_symmetric THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_delta_x4_hessian_component_real_list_of_seq = prove
 (`candle_fs_hist_delta_x4_hessian_real =
   list_of_seq
     (\i. list_of_seq
       (\j. candle_fs_hist_delta_x4_hessian_component_real i j) 6) 6`,
  MP_TAC
    (SPECL [`6`; `candle_fs_hist_delta_x4_hessian_real`]
      candle_fs_hist_matrix_list_of_seq) THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_hessian_real_length;
              candle_fs_hist_delta_x4_hessian_real_rows] THEN
  DISCH_THEN (fun matrix_form -> ONCE_REWRITE_TAC[matrix_form]) THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ;
               candle_fs_hist_delta_x4_hessian_component_real_def]);;

let candle_fs_hist_delta_x4_second_gradient_contains = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6)
     ==> ALL2 candle_fs_interval_contains
           (candle_fs_hist_second_gradient
             (candle_fs_hist_delta_x4_second boxes))
           (list_of_seq (candle_fs_hist_delta_x4_derivative values) 6)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM candle_fs_hist_delta_x4_gradient_real_list_of_seq] THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_second_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  MATCH_MP_TAC candle_fs_hist_delta_x4_gradient_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_delta_x4_second_hessian_contains = prove
 (`!boxes.
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_delta_x4_second boxes))
       (list_of_seq
         (\i. list_of_seq
           (\j. candle_fs_hist_delta_x4_hessian_component_real i j) 6) 6)`,
  GEN_TAC THEN
  REWRITE_TAC
    [GSYM candle_fs_hist_delta_x4_hessian_component_real_list_of_seq] THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_second_def;
              candle_fs_hist_second_hessian_def;
              candle_fs_hist_second_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_fs_hist_delta_x4_hessian_contains);;

let candle_fs_hist_delta_x4_second_data_shape = prove
 (`!boxes.
     LENGTH
       (candle_fs_hist_second_gradient
         (candle_fs_hist_delta_x4_second boxes)) = 6 /\
     LENGTH
       (candle_fs_hist_second_hessian
         (candle_fs_hist_delta_x4_second boxes)) = 6 /\
     ALL (\row. LENGTH row = 6)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_delta_x4_second boxes))`,
  REWRITE_TAC[candle_fs_hist_delta_x4_second_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_hessian_def;
              candle_fs_hist_second_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_gradient_def; LENGTH;
              candle_fs_hist_delta_x4_hessian_def;
              LET_DEF; LET_END_DEF; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_delta_x4_second_to_q_shape = prove
 (`!boxes.
     candle_q_dim_jet_shape 6
       (candle_fs_hist_second_to_q
         (candle_fs_hist_delta_x4_second boxes))`,
  REWRITE_TAC[candle_fs_hist_second_to_q_def;
              candle_fs_first_to_q_shape;
              candle_fs_first_make_def;
              candle_fs_first_gradient_def;
              candle_fs_hist_delta_x4_second_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_hessian_def;
              candle_fs_hist_second_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_gradient_def; LENGTH;
              candle_fs_hist_delta_x4_hessian_def;
              LET_DEF; LET_END_DEF; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_delta_x4_second_components = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6)
     ==> candle_q_dim_jet_contains_components 6
           (candle_fs_hist_second_to_q
             (candle_fs_hist_delta_x4_second boxes))
           (candle_fs_hist_delta_x4_real values)
           (candle_fs_hist_delta_x4_derivative values)
           candle_fs_hist_delta_x4_hessian_component_real`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_second_to_q_def] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM candle_fs_hist_second_to_q_def] THEN
    MATCH_ACCEPT_TAC candle_fs_hist_delta_x4_second_to_q_shape;
    REWRITE_TAC[candle_fs_first_value_def;
                candle_fs_first_make_def; FST] THEN
    MATCH_MP_TAC candle_fs_hist_delta_x4_second_value_contains THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_first_gradient_def;
                candle_fs_first_make_def; SND] THEN
    MATCH_MP_TAC candle_fs_hist_delta_x4_second_gradient_contains THEN
    ASM_REWRITE_TAC[];
    MATCH_ACCEPT_TAC
      (CONV_RULE (DEPTH_CONV ETA_CONV)
        candle_fs_hist_delta_x4_second_hessian_contains)]);;

end;;
