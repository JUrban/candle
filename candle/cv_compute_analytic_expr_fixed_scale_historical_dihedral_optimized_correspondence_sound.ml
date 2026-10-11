(* ========================================================================== *)
(* Low-work historical dihedral arithmetic against the analytic reference.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_reference_instantiation.ml";;

module Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound = struct

open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_root_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_x4_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_instantiation;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_sound;;

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

let candle_fs_hist_root_delta_gradient_fixed_contains = prove
 (`!boxes values root_lower root_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     0 < root_lower /\ root_lower <= root_upper /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0))
       (sqrt (candle_fs_hist_delta_real values))
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_second_gradient
         (candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_delta_second boxes)
           ((root_lower,0),(root_upper,0))))
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_root_delta_real_jet values)) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_root_delta_real_jet_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_make_def;
              candle_fs_hist_second_sqrt_supplied_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  REWRITE_TAC[GSYM candle_map_scale_list_of_seq] THEN
  REWRITE_TAC[GSYM candle_fs_hist_positive_sqrt_gradient_def] THEN
  MATCH_MP_TAC candle_fs_hist_positive_sqrt_gradient_universal_contains THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC
    (SPECL
      [`boxes:((num#num)#(num#num))list`; `values:num->real`]
      candle_fs_hist_delta_second_gradient_contains) THEN
  ASM_REWRITE_TAC[candle_fs_hist_second_gradient_def] THEN
  DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM candle_fs_hist_delta_gradient_real_list_of_seq] THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_root_four_x0_gradient_fixed_contains = prove
 (`!boxes values root_lower root_upper.
     0 < root_lower /\ root_lower <= root_upper /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values))
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_second_gradient
         (candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_four_x0_second boxes)
           ((root_lower,0),(root_upper,0))))
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_root_four_x0_real_jet values)) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_root_four_x0_real_jet_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_make_def;
              candle_fs_hist_second_sqrt_supplied_def;
              candle_fs_hist_four_x0_second_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  REWRITE_TAC[GSYM candle_map_scale_list_of_seq] THEN
  REWRITE_TAC[GSYM candle_fs_hist_positive_sqrt_gradient_def] THEN
  MATCH_MP_TAC candle_fs_hist_positive_sqrt_gradient_universal_contains THEN
  ASM_REWRITE_TAC[candle_fs_hist_four_x0_gradient_contains]);;

let candle_fs_hist_b_gradient_target_def = new_definition
 `candle_fs_hist_b_gradient_target values coordinate =
    sqrt (candle_fs_hist_four_x0_real values) *
      candle_hist_real_jet_gradient
        (candle_fs_hist_root_delta_real_jet values) coordinate +
    (if coordinate = 0 then
       sqrt (candle_fs_hist_delta_real values) *
         (&2 * inv (sqrt (candle_fs_hist_four_x0_real values)))
     else &0)`;;

let candle_fs_hist_b_gradient_target_eq = prove
 (`!values coordinate.
     candle_hist_real_jet_gradient
       (candle_fs_hist_b_real_jet values) coordinate =
     candle_fs_hist_b_gradient_target values coordinate`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_b_gradient_target_def;
              candle_fs_hist_b_real_jet_def;
              candle_hist_real_jet_mul_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_make_def;
              candle_fs_hist_root_delta_real_jet_def;
              candle_fs_hist_root_four_x0_real_jet_def;
              FST; SND] THEN
  ASM_CASES_TAC `coordinate = 0` THEN
  ASM_REWRITE_TAC[candle_fs_hist_four_x0_gradient_real_def] THEN
  REWRITE_TAC[REAL_ARITH `x + x = &2 * x`; REAL_INV_MUL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC REAL_RING);;

let candle_fs_hist_b_gradient_contains = prove
 (`!values root_delta_value root_four_x0 root_delta_gradient
      two_over_root_four_x0.
     candle_fs_interval_contains root_delta_value
       (sqrt (candle_fs_hist_delta_real values)) /\
     candle_fs_interval_contains root_four_x0
       (sqrt (candle_fs_hist_four_x0_real values)) /\
     ALL2 candle_fs_interval_contains root_delta_gradient
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_root_delta_real_jet values)) 6) /\
     candle_fs_interval_contains two_over_root_four_x0
       (&2 * inv (sqrt (candle_fs_hist_four_x0_real values)))
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_b_gradient root_four_x0 root_delta_value
         root_delta_gradient two_over_root_four_x0)
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_b_real_jet values)) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains
      (candle_fsn_interval_list_scale root_four_x0 root_delta_gradient)
      (list_of_seq
        (\coordinate.
          sqrt (candle_fs_hist_four_x0_real values) *
          candle_hist_real_jet_gradient
            (candle_fs_hist_root_delta_real_jet values) coordinate) 6)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_map_scale_list_of_seq] THEN
    MATCH_MP_TAC candle_fsn_interval_list_scale_contains THEN
    CONV_TAC (DEPTH_CONV ETA_CONV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_fsn_interval_list_scale root_four_x0 root_delta_gradient) = 6`
  ASSUME_TAC THENL
   [REWRITE_TAC[candle_fsn_interval_list_scale_length] THEN
    MP_TAC
      (MATCH_MP candle_all2_length
        (ASSUME
          `ALL2 candle_fs_interval_contains root_delta_gradient
            (list_of_seq
              (candle_hist_real_jet_gradient
                (candle_fs_hist_root_delta_real_jet values)) 6)`)) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!coordinate. coordinate < 6
      ==> candle_fs_interval_contains
        (candle_fs_interval_lookup coordinate
          (candle_fsn_interval_list_scale
            root_four_x0 root_delta_gradient))
        (sqrt (candle_fs_hist_four_x0_real values) *
         candle_hist_real_jet_gradient
           (candle_fs_hist_root_delta_real_jet values) coordinate)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (SPECL
          [`6`;
           `candle_fsn_interval_list_scale
              root_four_x0 root_delta_gradient`;
           `\coordinate.
              sqrt (candle_fs_hist_four_x0_real values) *
              candle_hist_real_jet_gradient
                (candle_fs_hist_root_delta_real_jet values) coordinate`;
           `coordinate:num`]
          candle_fs_hist_interval_lookup_contains)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_mul
        root_delta_value two_over_root_four_x0)
      (sqrt (candle_fs_hist_delta_real values) *
       (&2 * inv (sqrt (candle_fs_hist_four_x0_real values))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_b_gradient_target_eq;
              candle_fs_hist_b_gradient_def;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[candle_fs_hist_b_gradient_target_eq;
              candle_fs_hist_b_gradient_target_def; ALL2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ADD_RID] THEN
  let lookup_tac index =
    MATCH_MP_TAC
      (SPEC index
        (ASSUME
          `!coordinate. coordinate < 6
             ==> candle_fs_interval_contains
               (candle_fs_interval_lookup coordinate
                 (candle_fsn_interval_list_scale
                   root_four_x0 root_delta_gradient))
               (sqrt (candle_fs_hist_four_x0_real values) *
                candle_hist_real_jet_gradient
                  (candle_fs_hist_root_delta_real_jet values) coordinate)`))
    THEN ARITH_TAC in
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_interval_add_sound THEN
    CONJ_TAC THENL
     [lookup_tac `0`;
      ASM_REWRITE_TAC[]];
    lookup_tac `1`;
    lookup_tac `2`;
    lookup_tac `3`;
    lookup_tac `4`;
    lookup_tac `5`]);;

let candle_fs_hist_b_gradient_fixed_contains = prove
 (`!boxes values root_delta_lower root_delta_upper
      root_four_x0_lower root_four_x0_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     0 < root_delta_lower /\ root_delta_lower <= root_delta_upper /\
     candle_fs_interval_contains
       ((root_delta_lower,0),(root_delta_upper,0))
       (sqrt (candle_fs_hist_delta_real values)) /\
     0 < root_four_x0_lower /\
     root_four_x0_lower <= root_four_x0_upper /\
     candle_fs_interval_contains
       ((root_four_x0_lower,0),(root_four_x0_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values))
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_b_gradient
         ((root_four_x0_lower,0),(root_four_x0_upper,0))
         ((root_delta_lower,0),(root_delta_upper,0))
         (candle_fs_hist_second_gradient
           (candle_fs_hist_second_sqrt_supplied
             (candle_fs_hist_delta_second boxes)
             ((root_delta_lower,0),(root_delta_upper,0))))
         (candle_fs_hist_two_over_positive_root
           ((root_four_x0_lower,0),(root_four_x0_upper,0))))
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_b_real_jet values)) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_b_gradient_contains THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_root_delta_gradient_fixed_contains THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_two_over_positive_root_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_root_delta_hessian_fixed_contains = prove
 (`!boxes values input_lower input_upper root_lower root_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     candle_fs_hist_second_value
       (candle_fs_hist_delta_second boxes) =
       ((input_lower,0),(input_upper,0)) /\
     0 < input_lower /\ input_lower <= input_upper /\
     0 < root_lower /\ root_lower <= root_upper /\
     &0 < candle_fs_hist_delta_real values /\
     candle_fs_interval_contains
       ((root_lower,0),(root_upper,0))
       (sqrt (candle_fs_hist_delta_real values))
     ==> ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_second_sqrt_supplied
           (candle_fs_hist_delta_second boxes)
           ((root_lower,0),(root_upper,0))))
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_root_delta_real_jet values) i) 6) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      ((input_lower,0),(input_upper,0))
      (candle_fs_hist_delta_real values)`
  ASSUME_TAC THENL
   [MP_TAC
      (SPECL
        [`boxes:((num#num)#(num#num))list`; `values:num->real`]
        candle_fs_hist_delta_second_value_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_root_delta_real_jet_def;
              candle_hist_real_jet_hessian_def;
              candle_hist_real_jet_make_def] THEN
  ONCE_REWRITE_TAC[candle_fs_hist_second_hessian_def] THEN
  REWRITE_TAC[
              candle_fs_hist_second_sqrt_supplied_def;
              candle_fs_hist_second_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MP_TAC (ISPEC `boxes:((num#num)#(num#num))list`
    candle_fs_hist_delta_second_data_shape) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains
      (candle_fs_hist_second_gradient
        (candle_fs_hist_delta_second boxes))
      (list_of_seq
        (\i. EL i (candle_fs_hist_delta_gradient_real values)) 6)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_fs_hist_delta_gradient_real_list_of_seq] THEN
    MP_TAC
      (SPECL
        [`boxes:((num#num)#(num#num))list`; `values:num->real`]
        candle_fs_hist_delta_second_gradient_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 (ALL2 candle_fs_interval_contains)
      (candle_fs_hist_second_hessian
        (candle_fs_hist_delta_second boxes))
      (list_of_seq
        (\i. list_of_seq
          (candle_fs_hist_delta_hessian_component_real values i) 6) 6)`
  ASSUME_TAC THENL
   [REWRITE_TAC
      [GSYM
        (CONV_RULE (DEPTH_CONV ETA_CONV)
          candle_fs_hist_delta_hessian_component_real_list_of_seq)] THEN
    MP_TAC
      (SPECL
        [`boxes:((num#num)#(num#num))list`; `values:num->real`]
        candle_fs_hist_delta_second_hessian_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC
    (CONV_RULE (DEPTH_CONV BETA_CONV)
      (REWRITE_RULE[REAL_MUL_ASSOC]
        (SPECL
          [`input_lower:num`; `input_upper:num`;
           `root_lower:num`; `root_upper:num`;
           `candle_fs_hist_delta_real (values:num->real)`;
           `candle_fs_hist_second_gradient
              (candle_fs_hist_delta_second boxes)`;
           `candle_fs_hist_second_hessian
              (candle_fs_hist_delta_second boxes)`;
           `\i. EL i (candle_fs_hist_delta_gradient_real values)`;
          `candle_fs_hist_delta_hessian_component_real values`]
          candle_fs_hist_positive_sqrt_hessian_universal_contains))) THEN
  ASM_REWRITE_TAC[
    candle_fs_hist_delta_hessian_component_real_symmetric]);;

let candle_fs_hist_matrix_scale_eq = prove
 (`!scalar matrixvalue.
     candle_fs_hist_matrix_scale scalar matrixvalue =
     candle_fsn_interval_matrix_scale scalar matrixvalue`,
  REWRITE_TAC[candle_fs_hist_matrix_scale_def;
              candle_fsn_interval_matrix_scale_def]);;

let candle_fs_hist_b_base_hessian_contains = prove
 (`!root_four_x0 root_delta_hessian values.
     candle_fs_interval_contains root_four_x0
       (sqrt (candle_fs_hist_four_x0_real values)) /\
     ALL2 (ALL2 candle_fs_interval_contains) root_delta_hessian
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_root_delta_real_jet values) i) 6) 6)
     ==> ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_matrix_scale root_four_x0 root_delta_hessian)
       (list_of_seq
         (\i. list_of_seq
           (\j. sqrt (candle_fs_hist_four_x0_real values) *
                candle_hist_real_jet_hessian
                  (candle_fs_hist_root_delta_real_jet values) i j)
           6) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 (ALL2 candle_fs_interval_contains) root_delta_hessian
      (list_of_seq
        (\i. list_of_seq
          (\j. candle_hist_real_jet_hessian
            (candle_fs_hist_root_delta_real_jet values) i j)
          6) 6)`
  ASSUME_TAC THENL
   [CONV_TAC (DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_matrix_scale_eq] THEN
  ONCE_REWRITE_TAC[GSYM candle_map_matrix_scale_list_of_seq] THEN
  MATCH_MP_TAC candle_fsn_interval_matrix_scale_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_b_hessian_target_def = new_definition
 `candle_fs_hist_b_hessian_target values rowindex colindex =
    let base =
      sqrt (candle_fs_hist_four_x0_real values) *
      candle_hist_real_jet_hessian
        (candle_fs_hist_root_delta_real_jet values) rowindex colindex in
    let two_over_root =
      &2 * inv (sqrt (candle_fs_hist_four_x0_real values)) in
    if rowindex = 0 then
      if colindex = 0 then
        base +
          (&2 *
             (candle_hist_real_jet_gradient
                (candle_fs_hist_root_delta_real_jet values) 0 *
              two_over_root) +
           --((sqrt (candle_fs_hist_delta_real values) * two_over_root) *
              inv (&2 * values 0)))
      else
        base +
          candle_hist_real_jet_gradient
            (candle_fs_hist_root_delta_real_jet values) colindex *
          two_over_root
    else if colindex = 0 then
      base +
        candle_hist_real_jet_gradient
          (candle_fs_hist_root_delta_real_jet values) rowindex *
        two_over_root
    else base`;;

let candle_fs_hist_b_hessian_target_eq = prove
 (`!values rowindex colindex.
     candle_hist_real_jet_hessian
       (candle_fs_hist_b_real_jet values) rowindex colindex =
     candle_fs_hist_b_hessian_target values rowindex colindex`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_b_hessian_target_def;
              candle_fs_hist_b_real_jet_def;
              candle_hist_real_jet_mul_def;
              candle_hist_real_jet_hessian_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_make_def;
              candle_fs_hist_root_delta_real_jet_def;
              candle_fs_hist_root_four_x0_real_jet_def;
              FST; SND; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `rowindex = 0` THEN
  ASM_CASES_TAC `colindex = 0` THEN
  ASM_REWRITE_TAC[candle_fs_hist_four_x0_gradient_real_def;
                  candle_fs_hist_four_x0_hessian_real_def;
                  candle_fs_hist_four_x0_real_def] THEN
  REWRITE_TAC[REAL_ARITH `x + x = &2 * x`; REAL_INV_MUL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC REAL_RING);;

let candle_fs_hist_b_hessian_entry_contains = prove
 (`!values rowindex colindex base_hessian root_delta_value
      root_delta_gradient two_over_root_four_x0 x0.
     LENGTH base_hessian = 6 /\
     ALL (\matrix_row. LENGTH matrix_row = 6) base_hessian /\
     ALL2 (ALL2 candle_fs_interval_contains) base_hessian
       (list_of_seq
         (\i. list_of_seq
           (\j. sqrt (candle_fs_hist_four_x0_real values) *
                candle_hist_real_jet_hessian
                  (candle_fs_hist_root_delta_real_jet values) i j)
           6) 6) /\
     LENGTH root_delta_gradient = 6 /\
     ALL2 candle_fs_interval_contains root_delta_gradient
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_root_delta_real_jet values)) 6) /\
     candle_fs_interval_contains root_delta_value
       (sqrt (candle_fs_hist_delta_real values)) /\
     candle_fs_interval_contains two_over_root_four_x0
       (&2 * inv (sqrt (candle_fs_hist_four_x0_real values))) /\
     candle_fs_interval_contains
       (candle_fs_hist_positive_inv
         (candle_fs_angle_interval_scale 2 x0))
       (inv (&2 * values 0)) /\
     rowindex < 6 /\ colindex < 6
     ==> candle_fs_interval_contains
       (candle_fs_hist_b_hessian_entry rowindex colindex base_hessian
         root_delta_value root_delta_gradient two_over_root_four_x0 x0)
       (candle_fs_hist_b_hessian_target values rowindex colindex)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_matrix_lookup rowindex colindex base_hessian)
      (sqrt (candle_fs_hist_four_x0_real values) *
       candle_hist_real_jet_hessian
         (candle_fs_hist_root_delta_real_jet values) rowindex colindex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (SPECL
          [`6`; `base_hessian:(((num#num)#(num#num))list)list`;
           `\i j. sqrt (candle_fs_hist_four_x0_real values) *
              candle_hist_real_jet_hessian
                (candle_fs_hist_root_delta_real_jet values) i j`;
           `rowindex:num`; `colindex:num`]
          candle_fs_hist_matrix_lookup_contains)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < 6
      ==> candle_fs_interval_contains
        (candle_fs_angle_interval_mul
          (candle_fs_interval_lookup i root_delta_gradient)
          two_over_root_four_x0)
        (candle_hist_real_jet_gradient
           (candle_fs_hist_root_delta_real_jet values) i *
         (&2 * inv (sqrt (candle_fs_hist_four_x0_real values))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`6`; `root_delta_gradient:((num#num)#(num#num))list`;
           `candle_hist_real_jet_gradient
              (candle_fs_hist_root_delta_real_jet values)`;
           `i:num`]
          candle_fs_hist_interval_lookup_contains) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_scale 2
        (candle_fs_angle_interval_mul
          (candle_fs_interval_lookup 0 root_delta_gradient)
          two_over_root_four_x0))
      (&2 *
        (candle_hist_real_jet_gradient
           (candle_fs_hist_root_delta_real_jet values) 0 *
         (&2 * inv (sqrt (candle_fs_hist_four_x0_real values)))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_angle_interval_scale_contains THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_neg
        (candle_fs_angle_interval_mul
          (candle_fs_angle_interval_mul
            root_delta_value two_over_root_four_x0)
          (candle_fs_hist_positive_inv
            (candle_fs_angle_interval_scale 2 x0))))
      (--((sqrt (candle_fs_hist_delta_real values) *
            (&2 * inv (sqrt (candle_fs_hist_four_x0_real values)))) *
          inv (&2 * values 0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_b_hessian_entry_def;
              candle_fs_hist_b_hessian_target_def;
              LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `rowindex = 0` THEN
  ASM_CASES_TAC `colindex = 0` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[candle_fs_interval_add_sound]);;

let candle_fs_hist_b_hessian_contains = prove
 (`!values root_four_x0 root_delta_value root_delta_gradient
      root_delta_hessian two_over_root_four_x0 x0.
     LENGTH root_delta_hessian = 6 /\
     ALL (\matrix_row. LENGTH matrix_row = 6) root_delta_hessian /\
     candle_fs_interval_contains root_four_x0
       (sqrt (candle_fs_hist_four_x0_real values)) /\
     ALL2 (ALL2 candle_fs_interval_contains) root_delta_hessian
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_root_delta_real_jet values) i) 6) 6) /\
     LENGTH root_delta_gradient = 6 /\
     ALL2 candle_fs_interval_contains root_delta_gradient
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_root_delta_real_jet values)) 6) /\
     candle_fs_interval_contains root_delta_value
       (sqrt (candle_fs_hist_delta_real values)) /\
     candle_fs_interval_contains two_over_root_four_x0
       (&2 * inv (sqrt (candle_fs_hist_four_x0_real values))) /\
     candle_fs_interval_contains
       (candle_fs_hist_positive_inv
         (candle_fs_angle_interval_scale 2 x0))
       (inv (&2 * values 0))
     ==> ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_b_hessian root_four_x0 root_delta_value
         root_delta_gradient root_delta_hessian
         two_over_root_four_x0 x0)
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_b_real_jet values) i) 6) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_fs_hist_matrix_scale root_four_x0 root_delta_hessian) = 6`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[candle_fs_hist_matrix_scale_length];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL (\matrix_row. LENGTH matrix_row = 6)
      (candle_fs_hist_matrix_scale root_four_x0 root_delta_hessian)`
  ASSUME_TAC THENL
   [REWRITE_TAC[candle_fs_hist_matrix_scale_eq] THEN
    MP_TAC
      (SPECL
        [`root_four_x0:(num#num)#(num#num)`;
         `root_delta_hessian:(((num#num)#(num#num))list)list`; `6`]
        candle_fsn_interval_matrix_scale_shape) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 (ALL2 candle_fs_interval_contains)
      (candle_fs_hist_matrix_scale root_four_x0 root_delta_hessian)
      (list_of_seq
        (\i. list_of_seq
          (\j. sqrt (candle_fs_hist_four_x0_real values) *
               candle_hist_real_jet_hessian
                 (candle_fs_hist_root_delta_real_jet values) i j)
          6) 6)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_b_base_hessian_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_b_hessian_def;
              candle_fs_hist_b_hessian_row_def;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC (DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[candle_fs_hist_b_hessian_target_eq; ALL2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC candle_fs_hist_b_hessian_entry_contains THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_second_sqrt_supplied_hessian_shape = prove
 (`!input root_value.
     LENGTH
       (candle_fs_hist_second_hessian
         (candle_fs_hist_second_sqrt_supplied input root_value)) = 6 /\
     ALL (\matrix_row. LENGTH matrix_row = 6)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_second_sqrt_supplied input root_value))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_second_sqrt_supplied_def;
              candle_fs_hist_second_hessian_def;
              candle_fs_hist_second_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_fs_hist_sqrt_hessian_shape);;

let candle_fs_hist_second_sqrt_supplied_gradient_length = prove
 (`!input root_value.
     LENGTH
       (candle_fs_hist_second_gradient
         (candle_fs_hist_second_sqrt_supplied input root_value)) =
     LENGTH (candle_fs_hist_second_gradient input)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_second_sqrt_supplied_def;
              candle_fs_hist_second_gradient_def;
              candle_fs_hist_second_make_def;
              candle_fsn_interval_list_scale_length;
              LET_DEF; LET_END_DEF; FST; SND]);;

let candle_fs_hist_positive_inv_double_contains = prove
 (`!lower upper x.
     0 < lower /\ lower <= upper /\
     candle_fs_interval_contains ((lower,0),(upper,0)) x
     ==> candle_fs_interval_contains
       (candle_fs_hist_positive_inv
         (candle_fs_angle_interval_scale 2
           ((lower,0),(upper,0))))
       (inv (&2 * x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_scale 2 ((lower,0),(upper,0)))
      (&2 * x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_angle_interval_scale_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_fs_angle_interval_scale_def;
                  candle_lc_zscale_def; FST; SND; MULT_CLAUSES]) THEN
  REWRITE_TAC[candle_fs_angle_interval_scale_def;
              candle_lc_zscale_def; FST; SND; MULT_CLAUSES] THEN
  MATCH_MP_TAC candle_fs_hist_positive_inv_contains THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Discharge the abstract [b] Hessian contract at the exact executable
   boundary used by the historical checker.  In particular, the coordinate
   zero reciprocal is authorized through the checked box lookup rather than
   by a detached numerical premise. *)

let candle_fs_hist_b_hessian_fixed_contains = prove
 (`!boxes values delta_lower delta_upper
      root_delta_lower root_delta_upper
      root_four_x0_lower root_four_x0_upper
      x0_lower x0_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     candle_fs_hist_second_value
       (candle_fs_hist_delta_second boxes) =
       ((delta_lower,0),(delta_upper,0)) /\
     0 < delta_lower /\ delta_lower <= delta_upper /\
     0 < root_delta_lower /\ root_delta_lower <= root_delta_upper /\
     &0 < candle_fs_hist_delta_real values /\
     candle_fs_interval_contains
       ((root_delta_lower,0),(root_delta_upper,0))
       (sqrt (candle_fs_hist_delta_real values)) /\
     0 < root_four_x0_lower /\
     root_four_x0_lower <= root_four_x0_upper /\
     candle_fs_interval_contains
       ((root_four_x0_lower,0),(root_four_x0_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values)) /\
     candle_fs_interval_lookup 0 boxes =
       ((x0_lower,0),(x0_upper,0)) /\
     0 < x0_lower /\ x0_lower <= x0_upper
     ==> ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_b_hessian
         ((root_four_x0_lower,0),(root_four_x0_upper,0))
         ((root_delta_lower,0),(root_delta_upper,0))
         (candle_fs_hist_second_gradient
           (candle_fs_hist_second_sqrt_supplied
             (candle_fs_hist_delta_second boxes)
             ((root_delta_lower,0),(root_delta_upper,0))))
         (candle_fs_hist_second_hessian
           (candle_fs_hist_second_sqrt_supplied
             (candle_fs_hist_delta_second boxes)
             ((root_delta_lower,0),(root_delta_upper,0))))
         (candle_fs_hist_two_over_positive_root
           ((root_four_x0_lower,0),(root_four_x0_upper,0)))
         (candle_fs_interval_lookup 0 boxes))
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_b_real_jet values) i) 6) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_b_hessian_contains THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_fs_hist_second_sqrt_supplied_hessian_shape];
    REWRITE_TAC[candle_fs_hist_second_sqrt_supplied_hessian_shape];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`boxes:((num#num)#(num#num))list`; `values:num->real`;
         `delta_lower:num`; `delta_upper:num`;
         `root_delta_lower:num`; `root_delta_upper:num`]
        candle_fs_hist_root_delta_hessian_fixed_contains) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_hist_second_sqrt_supplied_gradient_length] THEN
    MP_TAC
      (SPEC `boxes:((num#num)#(num#num))list`
        candle_fs_hist_delta_second_data_shape) THEN
    MESON_TAC[];
    MATCH_MP_TAC candle_fs_hist_root_delta_gradient_fixed_contains THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_two_over_positive_root_contains THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `candle_fs_interval_contains
        (candle_fs_interval_lookup 0 boxes) (values 0)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`6`; `boxes:((num#num)#(num#num))list`;
           `values:num->real`; `0`]
          candle_fs_hist_interval_lookup_contains) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ONCE_REWRITE_TAC
        [ASSUME
          `candle_fs_interval_lookup 0 boxes =
           ((x0_lower,0),(x0_upper,0))`] THEN
      MATCH_MP_TAC candle_fs_hist_positive_inv_double_contains THEN
      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC
        [GSYM
          (ASSUME
            `candle_fs_interval_lookup 0 boxes =
             ((x0_lower,0),(x0_upper,0))`)] THEN
      MATCH_ACCEPT_TAC
        (ASSUME
          `candle_fs_interval_contains
             (candle_fs_interval_lookup 0 boxes) (values 0)`)]]);;

(* The historical checker forms the numerator of the final gradient directly:
   [-delta_x4' * b + delta_x4 * b'].  Keep that low-work vector tied to the
   already authenticated analytic source jets before introducing the shared
   positive denominator. *)

let candle_fs_hist_c_real_def = new_definition
 `candle_fs_hist_c_real values coordinate =
    --(candle_fs_hist_delta_x4_derivative values coordinate *
       candle_hist_real_jet_value (candle_fs_hist_b_real_jet values)) +
    candle_fs_hist_delta_x4_real values *
      candle_hist_real_jet_gradient
        (candle_fs_hist_b_real_jet values) coordinate`;;

let candle_fs_hist_c_entry_contains = prove
 (`!values coordinate delta_x4_value b
      delta_x4_gradient b_gradient.
     LENGTH delta_x4_gradient = 6 /\
     ALL2 candle_fs_interval_contains delta_x4_gradient
       (list_of_seq (candle_fs_hist_delta_x4_derivative values) 6) /\
     LENGTH b_gradient = 6 /\
     ALL2 candle_fs_interval_contains b_gradient
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_b_real_jet values)) 6) /\
     candle_fs_interval_contains delta_x4_value
       (candle_fs_hist_delta_x4_real values) /\
     candle_fs_interval_contains b
       (candle_hist_real_jet_value
         (candle_fs_hist_b_real_jet values)) /\
     coordinate < 6
     ==> candle_fs_interval_contains
       (candle_fs_hist_c_entry coordinate delta_x4_value b
         delta_x4_gradient b_gradient)
       (candle_fs_hist_c_real values coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_lookup coordinate delta_x4_gradient)
      (candle_fs_hist_delta_x4_derivative values coordinate)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`6`; `delta_x4_gradient:((num#num)#(num#num))list`;
         `candle_fs_hist_delta_x4_derivative (values:num->real)`;
         `coordinate:num`]
        candle_fs_hist_interval_lookup_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_lookup coordinate b_gradient)
      (candle_hist_real_jet_gradient
        (candle_fs_hist_b_real_jet values) coordinate)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`6`; `b_gradient:((num#num)#(num#num))list`;
         `candle_hist_real_jet_gradient
            (candle_fs_hist_b_real_jet (values:num->real))`;
         `coordinate:num`]
        candle_fs_hist_interval_lookup_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_c_entry_def;
              candle_fs_hist_c_real_def] THEN
  MATCH_MP_TAC candle_fs_interval_add_sound THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_interval_neg_sound THEN
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_c_vector_contains = prove
 (`!values delta_x4_value b delta_x4_gradient b_gradient.
     LENGTH delta_x4_gradient = 6 /\
     ALL2 candle_fs_interval_contains delta_x4_gradient
       (list_of_seq (candle_fs_hist_delta_x4_derivative values) 6) /\
     LENGTH b_gradient = 6 /\
     ALL2 candle_fs_interval_contains b_gradient
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_b_real_jet values)) 6) /\
     candle_fs_interval_contains delta_x4_value
       (candle_fs_hist_delta_x4_real values) /\
     candle_fs_interval_contains b
       (candle_hist_real_jet_value
         (candle_fs_hist_b_real_jet values))
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_c_vector delta_x4_value b
         delta_x4_gradient b_gradient)
       (list_of_seq (candle_fs_hist_c_real values) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_c_vector_def] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[ALL2] THEN
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC candle_fs_hist_c_entry_contains THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_c_vector_fixed_contains = prove
 (`!boxes values root_delta_lower root_delta_upper
      root_four_x0_lower root_four_x0_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     0 < root_delta_lower /\ root_delta_lower <= root_delta_upper /\
     candle_fs_interval_contains
       ((root_delta_lower,0),(root_delta_upper,0))
       (sqrt (candle_fs_hist_delta_real values)) /\
     0 < root_four_x0_lower /\
     root_four_x0_lower <= root_four_x0_upper /\
     candle_fs_interval_contains
       ((root_four_x0_lower,0),(root_four_x0_upper,0))
       (sqrt (candle_fs_hist_four_x0_real values))
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_c_vector
         (candle_fs_hist_second_value
           (candle_fs_hist_delta_x4_second boxes))
         (candle_fs_angle_interval_mul
           ((root_delta_lower,0),(root_delta_upper,0))
           ((root_four_x0_lower,0),(root_four_x0_upper,0)))
         (candle_fs_hist_second_gradient
           (candle_fs_hist_delta_x4_second boxes))
         (candle_fs_hist_b_gradient
           ((root_four_x0_lower,0),(root_four_x0_upper,0))
           ((root_delta_lower,0),(root_delta_upper,0))
           (candle_fs_hist_second_gradient
             (candle_fs_hist_second_sqrt_supplied
               (candle_fs_hist_delta_second boxes)
               ((root_delta_lower,0),(root_delta_upper,0))))
           (candle_fs_hist_two_over_positive_root
             ((root_four_x0_lower,0),(root_four_x0_upper,0)))))
       (list_of_seq (candle_fs_hist_c_real values) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_c_vector_contains THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC
      (SPEC `boxes:((num#num)#(num#num))list`
        candle_fs_hist_delta_x4_second_data_shape) THEN
    MESON_TAC[];
    MATCH_MP_TAC candle_fs_hist_delta_x4_second_gradient_contains THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fs_hist_b_gradient_length];
    MATCH_MP_TAC candle_fs_hist_b_gradient_fixed_contains THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_delta_x4_second_value_contains THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_b_value_contains THEN
    ASM_REWRITE_TAC[]]);;

end;;
