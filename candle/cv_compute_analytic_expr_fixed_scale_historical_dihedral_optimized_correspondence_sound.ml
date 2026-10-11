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

let candle_fs_hist_u_gradient_form_contains = prove
 (`!first second third x y z.
     candle_fs_interval_contains first x /\
     candle_fs_interval_contains second y /\
     candle_fs_interval_contains third z
     ==> candle_fs_interval_contains
       (candle_fs_angle_interval_scale 2
         (candle_fs_angle_interval_sum
           [first;second;third]))
       (&2 * (x + y + z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_angle_interval_scale_contains THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_angle_interval_sum
        [first;second;third])
      (ITLIST (\item total:real. item + total) [x;y;z] (&0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_interval_sum_contains THEN
    ASM_REWRITE_TAC[ALL2];
    ALL_TAC] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[ITLIST; REAL_ADD_RID]) THEN
  ASM_REWRITE_TAC[REAL_ADD_ASSOC]);;

let candle_fs_hist_u_three_gradient_def = prove
 (`!x0 x1 x2.
     SND (candle_fs_hist_u_three x0 x1 x2) =
     [candle_fs_angle_interval_scale 2
        (candle_fs_angle_interval_sum
          [candle_fs_interval_neg x0;x1;x2]);
      candle_fs_angle_interval_scale 2
        (candle_fs_angle_interval_sum
          [x0;candle_fs_interval_neg x1;x2]);
      candle_fs_angle_interval_scale 2
        (candle_fs_angle_interval_sum
          [x0;x1;candle_fs_interval_neg x2])]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_three_def;
              candle_fs_hist_u_def;
              LET_DEF; LET_END_DEF; FST; SND]);;

let candle_fs_hist_interval_lookup_three = prove
 (`!first second third.
     candle_fs_interval_lookup 0 [first;second;third] = first /\
     candle_fs_interval_lookup 1 [first;second;third] = second /\
     candle_fs_interval_lookup 2 [first;second;third] = third`,
  REPEAT GEN_TAC THEN
  MP_TAC (ARITH_RULE `1 = SUC 0`) THEN
  MP_TAC (ARITH_RULE `2 = SUC (SUC 0)`) THEN
  REPEAT (DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[candle_fs_interval_lookup_def]);;

let candle_fs_hist_u126_gradient_real_def = new_definition
 `candle_fs_hist_u126_gradient_real values coordinate =
    if coordinate = 0 then
      &2 * (--(values 0) + values 1 + values 5)
    else if coordinate = 1 then
      &2 * (values 0 + --(values 1) + values 5)
    else if coordinate = 5 then
      &2 * (values 0 + values 1 + --(values 5))
    else &0`;;

let candle_fs_hist_u135_gradient_real_def = new_definition
 `candle_fs_hist_u135_gradient_real values coordinate =
    if coordinate = 0 then
      &2 * (--(values 0) + values 2 + values 4)
    else if coordinate = 2 then
      &2 * (values 0 + --(values 2) + values 4)
    else if coordinate = 4 then
      &2 * (values 0 + values 2 + --(values 4))
    else &0`;;

let candle_fs_hist_u126_gradient_contains = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6)
     ==> ALL2 candle_fs_interval_contains
       (SND (candle_fs_hist_u126 boxes))
       (list_of_seq (candle_fs_hist_u126_gradient_real values) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_lookup 0 boxes) (values 0) /\
    candle_fs_interval_contains
      (candle_fs_interval_lookup 1 boxes) (values 1) /\
    candle_fs_interval_contains
      (candle_fs_interval_lookup 5 boxes) (values 5)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_u126_def;
              candle_fs_hist_u_def;
              LET_DEF; LET_END_DEF; FST; SND;
              candle_fs_hist_u_three_gradient_def] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[candle_fs_hist_u126_gradient_real_def;
              candle_fs_interval_lookup_def; ALL2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[candle_fs_hist_interval_lookup_three] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_u_gradient_form_contains THEN
    ASM_MESON_TAC[candle_fs_interval_neg_sound];
    MATCH_MP_TAC candle_fs_hist_u_gradient_form_contains THEN
    ASM_MESON_TAC[candle_fs_interval_neg_sound];
    MATCH_ACCEPT_TAC candle_fs_interval_zero_contains;
    MATCH_ACCEPT_TAC candle_fs_interval_zero_contains;
    MATCH_ACCEPT_TAC candle_fs_interval_zero_contains;
    MATCH_MP_TAC candle_fs_hist_u_gradient_form_contains THEN
    ASM_MESON_TAC[candle_fs_interval_neg_sound]]);;

let candle_fs_hist_u135_gradient_contains = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6)
     ==> ALL2 candle_fs_interval_contains
       (SND (candle_fs_hist_u135 boxes))
       (list_of_seq (candle_fs_hist_u135_gradient_real values) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_lookup 0 boxes) (values 0) /\
    candle_fs_interval_contains
      (candle_fs_interval_lookup 2 boxes) (values 2) /\
    candle_fs_interval_contains
      (candle_fs_interval_lookup 4 boxes) (values 4)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_u135_def;
              candle_fs_hist_u_def;
              LET_DEF; LET_END_DEF; FST; SND;
              candle_fs_hist_u_three_gradient_def] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[candle_fs_hist_u135_gradient_real_def;
              candle_fs_interval_lookup_def; ALL2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[candle_fs_hist_interval_lookup_three] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_u_gradient_form_contains THEN
    ASM_MESON_TAC[candle_fs_interval_neg_sound];
    MATCH_ACCEPT_TAC candle_fs_interval_zero_contains;
    MATCH_MP_TAC candle_fs_hist_u_gradient_form_contains THEN
    ASM_MESON_TAC[candle_fs_interval_neg_sound];
    MATCH_ACCEPT_TAC candle_fs_interval_zero_contains;
    MATCH_MP_TAC candle_fs_hist_u_gradient_form_contains THEN
    ASM_MESON_TAC[candle_fs_interval_neg_sound];
    MATCH_ACCEPT_TAC candle_fs_interval_zero_contains]);;

let candle_fs_hist_u_three_real_def = new_definition
 `candle_fs_hist_u_three_real x0 x1 x2 =
    --(x0 * x0) - x1 * x1 - x2 * x2 +
    &2 * (x0 * x1) + &2 * (x1 * x2) + &2 * (x2 * x0)`;;

let candle_fs_hist_u126_real_def = new_definition
 `candle_fs_hist_u126_real (values:num->real) =
    candle_fs_hist_u_three_real (values 0) (values 1) (values 5)`;;

let candle_fs_hist_u135_real_def = new_definition
 `candle_fs_hist_u135_real (values:num->real) =
    candle_fs_hist_u_three_real (values 0) (values 2) (values 4)`;;

let candle_fs_hist_log_u_gradient_real_def = new_definition
 `candle_fs_hist_log_u_gradient_real (values:num->real) coordinate =
    candle_fs_hist_u126_gradient_real values coordinate *
      inv (candle_fs_hist_u126_real values) +
    candle_fs_hist_u135_gradient_real values coordinate *
      inv (candle_fs_hist_u135_real values)`;;

let candle_fs_hist_log_u_gradient_real_eta = prove
 (`!values.
     candle_fs_hist_log_u_gradient_real values =
     (\coordinate.
       candle_fs_hist_u126_gradient_real values coordinate *
         inv (candle_fs_hist_u126_real values) +
       candle_fs_hist_u135_gradient_real values coordinate *
         inv (candle_fs_hist_u135_real values))`,
  REWRITE_TAC[FUN_EQ_THM; candle_fs_hist_log_u_gradient_real_def]);;

let candle_fs_hist_log_u_gradient_entry_contains = prove
 (`!coordinate u126_gradient reciprocal_u126
      u135_gradient reciprocal_u135 u126_real_gradient
      u135_real_gradient reciprocal_u126_real reciprocal_u135_real.
     LENGTH u126_gradient = 6 /\
     ALL2 candle_fs_interval_contains u126_gradient
       (list_of_seq u126_real_gradient 6) /\
     LENGTH u135_gradient = 6 /\
     ALL2 candle_fs_interval_contains u135_gradient
       (list_of_seq u135_real_gradient 6) /\
     candle_fs_interval_contains reciprocal_u126 reciprocal_u126_real /\
     candle_fs_interval_contains reciprocal_u135 reciprocal_u135_real /\
     coordinate < 6
     ==> candle_fs_interval_contains
       (candle_fs_hist_log_u_gradient_entry coordinate
         u126_gradient reciprocal_u126 u135_gradient reciprocal_u135)
       (u126_real_gradient coordinate * reciprocal_u126_real +
        u135_real_gradient coordinate * reciprocal_u135_real)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_lookup coordinate u126_gradient)
      (u126_real_gradient coordinate)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (SPECL
          [`6`; `u126_gradient:((num#num)#(num#num))list`;
           `u126_real_gradient:num->real`; `coordinate:num`]
          candle_fs_hist_interval_lookup_contains)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_lookup coordinate u135_gradient)
      (u135_real_gradient coordinate)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (SPECL
          [`6`; `u135_gradient:((num#num)#(num#num))list`;
           `u135_real_gradient:num->real`; `coordinate:num`]
          candle_fs_hist_interval_lookup_contains)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_log_u_gradient_entry_def] THEN
  MATCH_MP_TAC candle_fs_interval_add_sound THEN
  CONJ_TAC THEN MATCH_MP_TAC candle_fs_hist_angle_mul_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_log_u_gradient_contains = prove
 (`!u126_gradient reciprocal_u126 u135_gradient reciprocal_u135
      u126_real_gradient u135_real_gradient
      reciprocal_u126_real reciprocal_u135_real.
     LENGTH u126_gradient = 6 /\
     ALL2 candle_fs_interval_contains u126_gradient
       (list_of_seq u126_real_gradient 6) /\
     LENGTH u135_gradient = 6 /\
     ALL2 candle_fs_interval_contains u135_gradient
       (list_of_seq u135_real_gradient 6) /\
     candle_fs_interval_contains reciprocal_u126 reciprocal_u126_real /\
     candle_fs_interval_contains reciprocal_u135 reciprocal_u135_real
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_log_u_gradient
         u126_gradient reciprocal_u126 u135_gradient reciprocal_u135)
       (list_of_seq
         (\coordinate.
           u126_real_gradient coordinate * reciprocal_u126_real +
           u135_real_gradient coordinate * reciprocal_u135_real) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_log_u_gradient_def] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[ALL2] THEN
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC candle_fs_hist_log_u_gradient_entry_contains THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_log_u_gradient_fixed_contains = prove
 (`!boxes (values:num->real)
      u126_lower u126_upper u135_lower u135_upper.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     FST (candle_fs_hist_u126 boxes) =
       ((u126_lower,0),(u126_upper,0)) /\
     0 < u126_lower /\ u126_lower <= u126_upper /\
     candle_fs_interval_contains (FST (candle_fs_hist_u126 boxes))
       (candle_fs_hist_u126_real values) /\
     FST (candle_fs_hist_u135 boxes) =
       ((u135_lower,0),(u135_upper,0)) /\
     0 < u135_lower /\ u135_lower <= u135_upper /\
     candle_fs_interval_contains (FST (candle_fs_hist_u135 boxes))
       (candle_fs_hist_u135_real values)
     ==> ALL2 candle_fs_interval_contains
       (candle_fs_hist_log_u_gradient
         (SND (candle_fs_hist_u126 boxes))
         (candle_fs_hist_positive_inv (FST (candle_fs_hist_u126 boxes)))
         (SND (candle_fs_hist_u135 boxes))
         (candle_fs_hist_positive_inv (FST (candle_fs_hist_u135 boxes))))
       (list_of_seq
         (candle_fs_hist_log_u_gradient_real values) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains
      (SND (candle_fs_hist_u126 boxes))
      (list_of_seq (candle_fs_hist_u126_gradient_real values) 6)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_u126_gradient_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains
      (SND (candle_fs_hist_u135 boxes))
      (list_of_seq (candle_fs_hist_u135_gradient_real values) 6)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_u135_gradient_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_hist_positive_inv (FST (candle_fs_hist_u126 boxes)))
      (inv (candle_fs_hist_u126_real values))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_positive_inv_contains];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_hist_positive_inv (FST (candle_fs_hist_u135 boxes)))
      (inv (candle_fs_hist_u135_real values))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_positive_inv_contains];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH (SND (candle_fs_hist_u126 boxes)) = 6`
  ASSUME_TAC THENL
   [MP_TAC (MATCH_MP candle_all2_length
      (ASSUME
        `ALL2 candle_fs_interval_contains
          (SND (candle_fs_hist_u126 boxes))
          (list_of_seq (candle_fs_hist_u126_gradient_real values) 6)`)) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH (SND (candle_fs_hist_u135 boxes)) = 6`
  ASSUME_TAC THENL
   [MP_TAC (MATCH_MP candle_all2_length
      (ASSUME
        `ALL2 candle_fs_interval_contains
          (SND (candle_fs_hist_u135 boxes))
          (list_of_seq (candle_fs_hist_u135_gradient_real values) 6)`)) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_hist_log_u_gradient_real_eta] THEN
  MATCH_MP_TAC candle_fs_hist_log_u_gradient_contains THEN
  CONV_TAC (DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[]);;

(* The specialized U denominator is the exact squared arctangent denominator.
   This polynomial identity is the algebraic bridge from the historical
   low-work formulas to the universal dihedral composition. *)

let candle_fs_hist_u_product_identity = prove
 (`!values.
     candle_fs_hist_u126_real values *
       candle_fs_hist_u135_real values =
     &4 * values 0 * candle_fs_hist_delta_real values +
       candle_fs_hist_delta_x4_real values *
       candle_fs_hist_delta_x4_real values`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_u126_real_def;
              candle_fs_hist_u135_real_def;
              candle_fs_hist_u_three_real_def;
              candle_fs_hist_delta_real_def;
              candle_fs_hist_delta_x4_real_def;
              LET_DEF; LET_END_DEF; ITLIST] THEN
  CONV_TAC REAL_RING);;

let candle_fs_hist_u_value_formula_real_def = new_definition
 `candle_fs_hist_u_value_formula_real
      negative0 negative1 negative2 positive0 positive1 positive2 =
    ITLIST (\item total:real. item + total)
      [--(negative0 * negative0);
       --(negative1 * negative1);
       --(negative2 * negative2);
       &2 * (positive0 * positive1);
       &2 * (positive1 * positive2);
       &2 * (positive2 * positive0)] (&0)`;;

let candle_fs_hist_u_value_formula_real_polynomial = prove
 (`!negative0 negative1 negative2 positive0 positive1 positive2.
     candle_fs_hist_u_value_formula_real
       negative0 negative1 negative2 positive0 positive1 positive2 =
     --(negative0 * negative0) - negative1 * negative1 -
       negative2 * negative2 + &2 * (positive0 * positive1) +
       &2 * (positive1 * positive2) + &2 * (positive2 * positive0)`,
  REWRITE_TAC[candle_fs_hist_u_value_formula_real_def; ITLIST] THEN
  CONV_TAC REAL_RING);;

let candle_fs_hist_u_value_formula_contains = prove
 (`!selector points0 points1 points2
      negative0 negative1 negative2 positive0 positive1 positive2.
     candle_fs_interval_contains
       (candle_fs_interval_lookup selector points0) negative0 /\
     candle_fs_interval_contains
       (candle_fs_interval_lookup selector points1) negative1 /\
     candle_fs_interval_contains
       (candle_fs_interval_lookup selector points2) negative2 /\
     candle_fs_interval_contains
       (candle_fs_interval_lookup (selector + 1) points0) positive0 /\
     candle_fs_interval_contains
       (candle_fs_interval_lookup (selector + 1) points1) positive1 /\
     candle_fs_interval_contains
       (candle_fs_interval_lookup (selector + 1) points2) positive2
     ==> candle_fs_interval_contains
       (candle_fs_hist_u_value_formula selector points0 points1 points2)
       (candle_fs_hist_u_value_formula_real
         negative0 negative1 negative2 positive0 positive1 positive2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_value_formula_def;
              candle_fs_hist_u_value_formula_real_def;
              LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC candle_fs_raw_interval_round_sound THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC candle_fs_scale_pos;
    MATCH_MP_TAC candle_fs_hist_raw_interval_sum_contains THEN
    REWRITE_TAC[ALL2] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_raw_interval_neg_contains THEN
      MATCH_MP_TAC candle_fs_raw_interval_mul_sound THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_fs_hist_raw_interval_neg_contains THEN
      MATCH_MP_TAC candle_fs_raw_interval_mul_sound THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_fs_hist_raw_interval_neg_contains THEN
      MATCH_MP_TAC candle_fs_raw_interval_mul_sound THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_fs_hist_raw_angle_interval_scale_contains THEN
      CONJ_TAC THENL
       [MATCH_ACCEPT_TAC candle_fs_product_denominator_pos;
        MATCH_MP_TAC candle_fs_raw_interval_mul_sound THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC candle_fs_hist_raw_angle_interval_scale_contains THEN
      CONJ_TAC THENL
       [MATCH_ACCEPT_TAC candle_fs_product_denominator_pos;
        MATCH_MP_TAC candle_fs_raw_interval_mul_sound THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC candle_fs_hist_raw_angle_interval_scale_contains THEN
      CONJ_TAC THENL
       [MATCH_ACCEPT_TAC candle_fs_product_denominator_pos;
        MATCH_MP_TAC candle_fs_raw_interval_mul_sound THEN
        ASM_REWRITE_TAC[]]]]);;

let candle_fs_hist_u_points_real_def = new_definition
 `candle_fs_hist_u_points_real
      (x:(num#num)#(num#num))
      (gradient:(num#num)#(num#num)) =
    let lower_point = candle_fs_real (FST x) in
    let upper_point = candle_fs_real (SND x) in
    if candle_fs_raw_le (0,0) (FST gradient) then
      [upper_point;upper_point;lower_point;lower_point]
    else if candle_fs_raw_le (SND gradient) (0,0) then
      [lower_point;lower_point;upper_point;upper_point]
    else
      [lower_point;upper_point;upper_point;lower_point]`;;

let candle_fs_hist_u_points_real_contains = prove
 (`!x gradient.
     ALL2 candle_fs_interval_contains
       (candle_fs_hist_u_points x gradient)
       (candle_fs_hist_u_points_real x gradient)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_points_def;
              candle_fs_hist_u_points_real_def;
              LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN
    ASM_REWRITE_TAC[ALL2; candle_fs_interval_contains_def;
                    FST; SND; REAL_LE_REFL]));;

let candle_fs_hist_u_points_length = prove
 (`!x gradient. LENGTH (candle_fs_hist_u_points x gradient) = 4`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_points_def; LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_u_value_formula_points_contains = prove
 (`!selector x0 gradient0 x1 gradient1 x2 gradient2.
     selector + 1 < 4
     ==> candle_fs_interval_contains
       (candle_fs_hist_u_value_formula selector
         (candle_fs_hist_u_points x0 gradient0)
         (candle_fs_hist_u_points x1 gradient1)
         (candle_fs_hist_u_points x2 gradient2))
       (candle_fs_hist_u_value_formula_real
         (EL selector (candle_fs_hist_u_points_real x0 gradient0))
         (EL selector (candle_fs_hist_u_points_real x1 gradient1))
         (EL selector (candle_fs_hist_u_points_real x2 gradient2))
         (EL (selector + 1)
           (candle_fs_hist_u_points_real x0 gradient0))
         (EL (selector + 1)
           (candle_fs_hist_u_points_real x1 gradient1))
         (EL (selector + 1)
           (candle_fs_hist_u_points_real x2 gradient2)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  let lookup_tac =
    MATCH_MP_TAC candle_fs_interval_lookup_contains THEN
    CONJ_TAC THENL
     [MATCH_ACCEPT_TAC candle_fs_hist_u_points_real_contains;
      REWRITE_TAC[candle_fs_hist_u_points_length] THEN ASM_ARITH_TAC] in
  MATCH_MP_TAC candle_fs_hist_u_value_formula_contains THEN
  REPEAT CONJ_TAC THEN lookup_tac);;

let candle_fs_hist_nonnegative_product_bounds = prove
 (`!lower_left x upper_left lower_right y upper_right.
     &0 <= lower_left /\ lower_left <= x /\ x <= upper_left /\
     &0 <= lower_right /\ lower_right <= y /\ y <= upper_right
     ==> lower_left * lower_right <= x * y /\
         x * y <= upper_left * upper_right`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC);;

let candle_fs_hist_u_termwise_bounds = prove
 (`!lower0 x0 upper0 lower1 x1 upper1 lower2 x2 upper2.
     &0 <= lower0 /\ lower0 <= x0 /\ x0 <= upper0 /\
     &0 <= lower1 /\ lower1 <= x1 /\ x1 <= upper1 /\
     &0 <= lower2 /\ lower2 <= x2 /\ x2 <= upper2
     ==> candle_fs_hist_u_value_formula_real
           upper0 upper1 upper2 lower0 lower1 lower2 <=
         candle_fs_hist_u_three_real x0 x1 x2 /\
         candle_fs_hist_u_three_real x0 x1 x2 <=
         candle_fs_hist_u_value_formula_real
           lower0 lower1 lower2 upper0 upper1 upper2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL [`lower0:real`; `x0:real`; `upper0:real`;
            `lower0:real`; `x0:real`; `upper0:real`]
      candle_fs_hist_nonnegative_product_bounds) THEN
  MP_TAC
    (SPECL [`lower1:real`; `x1:real`; `upper1:real`;
            `lower1:real`; `x1:real`; `upper1:real`]
      candle_fs_hist_nonnegative_product_bounds) THEN
  MP_TAC
    (SPECL [`lower2:real`; `x2:real`; `upper2:real`;
            `lower2:real`; `x2:real`; `upper2:real`]
      candle_fs_hist_nonnegative_product_bounds) THEN
  MP_TAC
    (SPECL [`lower0:real`; `x0:real`; `upper0:real`;
            `lower1:real`; `x1:real`; `upper1:real`]
      candle_fs_hist_nonnegative_product_bounds) THEN
  MP_TAC
    (SPECL [`lower1:real`; `x1:real`; `upper1:real`;
            `lower2:real`; `x2:real`; `upper2:real`]
      candle_fs_hist_nonnegative_product_bounds) THEN
  MP_TAC
    (SPECL [`lower2:real`; `x2:real`; `upper2:real`;
            `lower0:real`; `x0:real`; `upper0:real`]
      candle_fs_hist_nonnegative_product_bounds) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_value_formula_real_polynomial;
              candle_fs_hist_u_three_real_def] THEN
  ASM_REAL_ARITH_TAC);;

let candle_fs_hist_u_three_vector_real_def = new_definition
 `candle_fs_hist_u_three_vector_real (values:num->real) =
    candle_fs_hist_u_three_real (values 0) (values 1) (values 2)`;;

let candle_fs_hist_u_three_gradient_real_def = new_definition
 `candle_fs_hist_u_three_gradient_real (values:num->real) coordinate =
    if coordinate = 0 then
      &2 * (--(values 0) + values 1 + values 2)
    else if coordinate = 1 then
      &2 * (values 0 + --(values 1) + values 2)
    else if coordinate = 2 then
      &2 * (values 0 + values 1 + --(values 2))
    else &0`;;

let candle_fs_hist_u_three_gradient_contains = prove
 (`!x0 x1 x2 (values:num->real).
     candle_fs_interval_contains x0 (values 0) /\
     candle_fs_interval_contains x1 (values 1) /\
     candle_fs_interval_contains x2 (values 2)
     ==> ALL2 candle_fs_interval_contains
       (SND (candle_fs_hist_u_three x0 x1 x2))
       (list_of_seq (candle_fs_hist_u_three_gradient_real values) 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_three_gradient_def] THEN
  CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
  REWRITE_TAC[candle_fs_hist_u_three_gradient_real_def; ALL2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC candle_fs_hist_u_gradient_form_contains THEN
  ASM_MESON_TAC[candle_fs_interval_neg_sound]);;

let candle_fs_hist_u_three_coordinate_secant = prove
 (`!values coordinate replacement.
     coordinate < 3
     ==> candle_fs_hist_u_three_vector_real
           (candle_fs_hist_delta_x4_update
             values coordinate replacement) -
         candle_fs_hist_u_three_vector_real values =
         (replacement - values coordinate) *
         ((candle_fs_hist_u_three_gradient_real
             (candle_fs_hist_delta_x4_update
               values coordinate replacement) coordinate +
           candle_fs_hist_u_three_gradient_real values coordinate) / &2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2`
  MP_TAC THENL
   [ASM_ARITH_TAC;
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[candle_fs_hist_u_three_vector_real_def;
                candle_fs_hist_u_three_real_def;
                candle_fs_hist_u_three_gradient_real_def;
                candle_fs_hist_delta_x4_update_def] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC REAL_RING]);;

let candle_fs_hist_u_three_coordinate_nondecreasing = prove
 (`!(values:num->real) coordinate replacement.
     coordinate < 3 /\
     values coordinate <= replacement /\
     &0 <= candle_fs_hist_u_three_gradient_real values coordinate /\
     &0 <= candle_fs_hist_u_three_gradient_real
       (candle_fs_hist_delta_x4_update
         values coordinate replacement) coordinate
     ==> candle_fs_hist_u_three_vector_real values <=
         candle_fs_hist_u_three_vector_real
           (candle_fs_hist_delta_x4_update
             values coordinate replacement)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_vector_real
       (candle_fs_hist_delta_x4_update
         values coordinate replacement) -
     candle_fs_hist_u_three_vector_real values =
     (replacement - values coordinate) *
     ((candle_fs_hist_u_three_gradient_real
         (candle_fs_hist_delta_x4_update
           values coordinate replacement) coordinate +
       candle_fs_hist_u_three_gradient_real values coordinate) / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_u_three_coordinate_secant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (replacement - values coordinate) *
     ((candle_fs_hist_u_three_gradient_real
         (candle_fs_hist_delta_x4_update
           values coordinate replacement) coordinate +
       candle_fs_hist_u_three_gradient_real values coordinate) / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let candle_fs_hist_u_three_coordinate_nonincreasing = prove
 (`!(values:num->real) coordinate replacement.
     coordinate < 3 /\
     values coordinate <= replacement /\
     candle_fs_hist_u_three_gradient_real values coordinate <= &0 /\
     candle_fs_hist_u_three_gradient_real
       (candle_fs_hist_delta_x4_update
         values coordinate replacement) coordinate <= &0
     ==> candle_fs_hist_u_three_vector_real
           (candle_fs_hist_delta_x4_update
             values coordinate replacement) <=
         candle_fs_hist_u_three_vector_real values`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_vector_real
       (candle_fs_hist_delta_x4_update
         values coordinate replacement) -
     candle_fs_hist_u_three_vector_real values =
     (replacement - values coordinate) *
     ((candle_fs_hist_u_three_gradient_real
         (candle_fs_hist_delta_x4_update
           values coordinate replacement) coordinate +
       candle_fs_hist_u_three_gradient_real values coordinate) / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_u_three_coordinate_secant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (replacement - values coordinate) *
     --((candle_fs_hist_u_three_gradient_real
          (candle_fs_hist_delta_x4_update
            values coordinate replacement) coordinate +
        candle_fs_hist_u_three_gradient_real values coordinate) / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let candle_fs_hist_u_three_coordinate_nondecreasing_backward = prove
 (`!(values:num->real) coordinate replacement.
     coordinate < 3 /\
     replacement <= values coordinate /\
     &0 <= candle_fs_hist_u_three_gradient_real values coordinate /\
     &0 <= candle_fs_hist_u_three_gradient_real
       (candle_fs_hist_delta_x4_update
         values coordinate replacement) coordinate
     ==> candle_fs_hist_u_three_vector_real
           (candle_fs_hist_delta_x4_update
             values coordinate replacement) <=
         candle_fs_hist_u_three_vector_real values`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_vector_real
       (candle_fs_hist_delta_x4_update
         values coordinate replacement) -
     candle_fs_hist_u_three_vector_real values =
     (replacement - values coordinate) *
     ((candle_fs_hist_u_three_gradient_real
         (candle_fs_hist_delta_x4_update
           values coordinate replacement) coordinate +
       candle_fs_hist_u_three_gradient_real values coordinate) / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_u_three_coordinate_secant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (values coordinate - replacement) *
     ((candle_fs_hist_u_three_gradient_real
         (candle_fs_hist_delta_x4_update
           values coordinate replacement) coordinate +
       candle_fs_hist_u_three_gradient_real values coordinate) / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let candle_fs_hist_u_three_coordinate_nonincreasing_backward = prove
 (`!(values:num->real) coordinate replacement.
     coordinate < 3 /\
     replacement <= values coordinate /\
     candle_fs_hist_u_three_gradient_real values coordinate <= &0 /\
     candle_fs_hist_u_three_gradient_real
       (candle_fs_hist_delta_x4_update
         values coordinate replacement) coordinate <= &0
     ==> candle_fs_hist_u_three_vector_real values <=
         candle_fs_hist_u_three_vector_real
           (candle_fs_hist_delta_x4_update
             values coordinate replacement)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_vector_real
       (candle_fs_hist_delta_x4_update
         values coordinate replacement) -
     candle_fs_hist_u_three_vector_real values =
     (replacement - values coordinate) *
     ((candle_fs_hist_u_three_gradient_real
         (candle_fs_hist_delta_x4_update
           values coordinate replacement) coordinate +
       candle_fs_hist_u_three_gradient_real values coordinate) / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_u_three_coordinate_secant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (values coordinate - replacement) *
     --((candle_fs_hist_u_three_gradient_real
          (candle_fs_hist_delta_x4_update
            values coordinate replacement) coordinate +
        candle_fs_hist_u_three_gradient_real values coordinate) / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let candle_fs_hist_u_selected_real_def = new_definition
 `candle_fs_hist_u_selected_real upper
      (x:(num#num)#(num#num))
      (gradient:(num#num)#(num#num)) value =
    if candle_fs_raw_le (0,0) (FST gradient) then
      candle_fs_real (if upper then SND x else FST x)
    else if candle_fs_raw_le (SND gradient) (0,0) then
      candle_fs_real (if upper then FST x else SND x)
    else value`;;

let candle_fs_hist_u_selected_real_contains = prove
 (`!upper x gradient value.
     candle_fs_interval_contains x value
     ==> candle_fs_interval_contains x
       (candle_fs_hist_u_selected_real upper x gradient value)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_selected_real_def] THEN
  COND_CASES_TAC THENL
   [BOOL_CASES_TAC `upper:bool` THEN
    ASM_REWRITE_TAC[candle_fs_interval_contains_def] THEN
    REAL_ARITH_TAC;
    COND_CASES_TAC THENL
     [BOOL_CASES_TAC `upper:bool` THEN
      ASM_REWRITE_TAC[candle_fs_interval_contains_def] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]]]);;

let candle_fs_hist_u_selected_real_nonnegative = prove
 (`!upper x gradient value.
     candle_fs_raw_le (0,0) (FST x) /\
     candle_fs_interval_contains x value
     ==> &0 <= candle_fs_hist_u_selected_real upper x gradient value`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_interval_contains_nonnegative THEN
  EXISTS_TAC `x:(num#num)#(num#num)` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_u_selected_real_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_u_selected_upper_point_bounds = prove
 (`!x gradient value.
     candle_fs_interval_contains x value
     ==> EL 0 (candle_fs_hist_u_points_real x gradient) <=
         candle_fs_hist_u_selected_real T x gradient value /\
         candle_fs_hist_u_selected_real T x gradient value <=
         EL 1 (candle_fs_hist_u_points_real x gradient)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  POP_ASSUM
    (fun th ->
      MP_TAC (REWRITE_RULE[candle_fs_interval_contains_def] th)) THEN
  STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_points_real_def;
              candle_fs_hist_u_selected_real_def;
              LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let candle_fs_hist_u_selected_lower_point_bounds = prove
 (`!x gradient value.
     candle_fs_interval_contains x value
     ==> EL 3 (candle_fs_hist_u_points_real x gradient) <=
         candle_fs_hist_u_selected_real F x gradient value /\
         candle_fs_hist_u_selected_real F x gradient value <=
         EL 2 (candle_fs_hist_u_points_real x gradient)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  POP_ASSUM
    (fun th ->
      MP_TAC (REWRITE_RULE[candle_fs_interval_contains_def] th)) THEN
  STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_points_real_def;
              candle_fs_hist_u_selected_real_def;
              LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let candle_fs_hist_u_three_boxes_def = new_definition
 `candle_fs_hist_u_three_boxes
      (boxes:((num#num)#(num#num))list) =
    candle_fs_hist_u_three
      (candle_fs_interval_lookup 0 boxes)
      (candle_fs_interval_lookup 1 boxes)
      (candle_fs_interval_lookup 2 boxes)`;;

let candle_fs_hist_u_three_boxes_gradient_length = prove
 (`!boxes. LENGTH (SND (candle_fs_hist_u_three_boxes boxes)) = 3`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_three_boxes_def;
              candle_fs_hist_u_three_def;
              candle_fs_hist_u_def;
              LET_DEF; LET_END_DEF; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_u_three_derivative_contains = prove
 (`!boxes (values:num->real) coordinate.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3
     ==> candle_fs_interval_contains
       (candle_fs_interval_lookup coordinate
         (SND (candle_fs_hist_u_three_boxes boxes)))
       (candle_fs_hist_u_three_gradient_real values coordinate)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_lookup 0 boxes) (values 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
              `values:num->real`; `0`]
        candle_fs_hist_interval_lookup_contains) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_lookup 1 boxes) (values 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
              `values:num->real`; `1`]
        candle_fs_hist_interval_lookup_contains) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_lookup 2 boxes) (values 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
              `values:num->real`; `2`]
        candle_fs_hist_interval_lookup_contains) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains
      (SND (candle_fs_hist_u_three_boxes boxes))
      (list_of_seq (candle_fs_hist_u_three_gradient_real values) 3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[candle_fs_hist_u_three_boxes_def] THEN
    MATCH_MP_TAC candle_fs_hist_u_three_gradient_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC
    (SPECL
      [`3`;
       `SND (candle_fs_hist_u_three_boxes
         (boxes:((num#num)#(num#num))list))`;
       `candle_fs_hist_u_three_gradient_real (values:num->real)`;
       `coordinate:num`]
      candle_fs_hist_interval_lookup_contains) THEN
  ASM_REWRITE_TAC[candle_fs_hist_u_three_boxes_gradient_length]);;

let candle_fs_hist_u_three_derivative_nonnegative = prove
 (`!boxes (values:num->real) coordinate.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3 /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup coordinate
         (SND (candle_fs_hist_u_three_boxes boxes))))
     ==> &0 <= candle_fs_hist_u_three_gradient_real values coordinate`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_interval_contains_nonnegative THEN
  EXISTS_TAC
   `candle_fs_interval_lookup coordinate
      (SND (candle_fs_hist_u_three_boxes boxes))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_u_three_derivative_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_u_three_derivative_nonpositive = prove
 (`!boxes (values:num->real) coordinate.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3 /\
     candle_fs_raw_le
       (SND (candle_fs_interval_lookup coordinate
         (SND (candle_fs_hist_u_three_boxes boxes)))) (0,0)
     ==> candle_fs_hist_u_three_gradient_real values coordinate <= &0`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_hist_interval_contains_nonpositive THEN
  EXISTS_TAC
   `candle_fs_interval_lookup coordinate
      (SND (candle_fs_hist_u_three_boxes boxes))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fs_hist_u_three_derivative_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_u_three_nondecreasing_forward = prove
 (`!boxes (values:num->real) coordinate replacement.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3 /\
     candle_fs_interval_contains
       (candle_fs_interval_lookup coordinate boxes) replacement /\
     values coordinate <= replacement /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup coordinate
         (SND (candle_fs_hist_u_three_boxes boxes))))
     ==> candle_fs_hist_u_three_vector_real values <=
         candle_fs_hist_u_three_vector_real
           (candle_fs_hist_delta_x4_update
             values coordinate replacement)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains boxes
      (list_of_seq
        (candle_fs_hist_delta_x4_update
          (values:num->real) coordinate replacement) 3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
              `values:num->real`; `coordinate:num`; `replacement:real`]
        candle_fs_hist_delta_x4_update_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= candle_fs_hist_u_three_gradient_real values coordinate`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_u_three_derivative_nonnegative];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= candle_fs_hist_u_three_gradient_real
      (candle_fs_hist_delta_x4_update values coordinate replacement)
      coordinate`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_u_three_derivative_nonnegative];
    ALL_TAC] THEN
  ASM_MESON_TAC[candle_fs_hist_u_three_coordinate_nondecreasing]);;

let candle_fs_hist_u_three_nondecreasing_backward = prove
 (`!boxes (values:num->real) coordinate replacement.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3 /\
     candle_fs_interval_contains
       (candle_fs_interval_lookup coordinate boxes) replacement /\
     replacement <= values coordinate /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup coordinate
         (SND (candle_fs_hist_u_three_boxes boxes))))
     ==> candle_fs_hist_u_three_vector_real
           (candle_fs_hist_delta_x4_update
             values coordinate replacement) <=
         candle_fs_hist_u_three_vector_real values`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains boxes
      (list_of_seq
        (candle_fs_hist_delta_x4_update
          (values:num->real) coordinate replacement) 3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
              `values:num->real`; `coordinate:num`; `replacement:real`]
        candle_fs_hist_delta_x4_update_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= candle_fs_hist_u_three_gradient_real values coordinate`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_u_three_derivative_nonnegative];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= candle_fs_hist_u_three_gradient_real
      (candle_fs_hist_delta_x4_update values coordinate replacement)
      coordinate`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_u_three_derivative_nonnegative];
    ALL_TAC] THEN
  ASM_MESON_TAC
   [candle_fs_hist_u_three_coordinate_nondecreasing_backward]);;

let candle_fs_hist_u_three_nonincreasing_forward = prove
 (`!boxes (values:num->real) coordinate replacement.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3 /\
     candle_fs_interval_contains
       (candle_fs_interval_lookup coordinate boxes) replacement /\
     values coordinate <= replacement /\
     candle_fs_raw_le
       (SND (candle_fs_interval_lookup coordinate
         (SND (candle_fs_hist_u_three_boxes boxes)))) (0,0)
     ==> candle_fs_hist_u_three_vector_real
           (candle_fs_hist_delta_x4_update
             values coordinate replacement) <=
         candle_fs_hist_u_three_vector_real values`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains boxes
      (list_of_seq
        (candle_fs_hist_delta_x4_update
          (values:num->real) coordinate replacement) 3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
              `values:num->real`; `coordinate:num`; `replacement:real`]
        candle_fs_hist_delta_x4_update_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_gradient_real values coordinate <= &0`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_u_three_derivative_nonpositive];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_gradient_real
      (candle_fs_hist_delta_x4_update values coordinate replacement)
      coordinate <= &0`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_u_three_derivative_nonpositive];
    ALL_TAC] THEN
  ASM_MESON_TAC[candle_fs_hist_u_three_coordinate_nonincreasing]);;

let candle_fs_hist_u_three_nonincreasing_backward = prove
 (`!boxes (values:num->real) coordinate replacement.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3 /\
     candle_fs_interval_contains
       (candle_fs_interval_lookup coordinate boxes) replacement /\
     replacement <= values coordinate /\
     candle_fs_raw_le
       (SND (candle_fs_interval_lookup coordinate
         (SND (candle_fs_hist_u_three_boxes boxes)))) (0,0)
     ==> candle_fs_hist_u_three_vector_real values <=
         candle_fs_hist_u_three_vector_real
           (candle_fs_hist_delta_x4_update
             values coordinate replacement)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_fs_interval_contains boxes
      (list_of_seq
        (candle_fs_hist_delta_x4_update
          (values:num->real) coordinate replacement) 3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
      (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
              `values:num->real`; `coordinate:num`; `replacement:real`]
        candle_fs_hist_delta_x4_update_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_gradient_real values coordinate <= &0`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_u_three_derivative_nonpositive];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_gradient_real
      (candle_fs_hist_delta_x4_update values coordinate replacement)
      coordinate <= &0`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_fs_hist_u_three_derivative_nonpositive];
    ALL_TAC] THEN
  ASM_MESON_TAC
   [candle_fs_hist_u_three_coordinate_nonincreasing_backward]);;

let candle_fs_hist_u_three_selected_value_def = new_definition
 `candle_fs_hist_u_three_selected_value upper coordinate boxes
      (values:num->real) =
    candle_fs_hist_u_selected_real upper
      (candle_fs_interval_lookup coordinate boxes)
      (candle_fs_interval_lookup coordinate
        (SND (candle_fs_hist_u_three_boxes boxes)))
      (values coordinate)`;;

let candle_fs_hist_u_three_selected_value_in_box = prove
 (`!upper coordinate boxes (values:num->real).
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3
     ==> candle_fs_interval_contains
       (candle_fs_interval_lookup coordinate boxes)
       (candle_fs_hist_u_three_selected_value
         upper coordinate boxes values)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_three_selected_value_def] THEN
  MATCH_MP_TAC candle_fs_hist_u_selected_real_contains THEN
  MATCH_MP_TAC
    (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
            `values:num->real`; `coordinate:num`]
      candle_fs_hist_interval_lookup_contains) THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_u_three_monotone_step = prove
 (`!upper boxes (values:num->real) coordinate.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3
     ==> if upper then
           candle_fs_hist_u_three_vector_real values <=
           candle_fs_hist_u_three_vector_real
             (candle_fs_hist_delta_x4_update values coordinate
               (candle_fs_hist_u_three_selected_value
                 upper coordinate boxes values))
         else
           candle_fs_hist_u_three_vector_real
             (candle_fs_hist_delta_x4_update values coordinate
               (candle_fs_hist_u_three_selected_value
                 upper coordinate boxes values)) <=
           candle_fs_hist_u_three_vector_real values`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_real
      (FST (candle_fs_interval_lookup coordinate boxes)) <=
      values coordinate /\
    values coordinate <=
      candle_fs_real
        (SND (candle_fs_interval_lookup coordinate boxes))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC
      (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
              `values:num->real`; `coordinate:num`]
        candle_fs_hist_interval_lookup_contains) THEN
    ASM_REWRITE_TAC[candle_fs_interval_contains_def];
    ALL_TAC] THEN
  BOOL_CASES_TAC `upper:bool` THEN
  ASM_REWRITE_TAC[candle_fs_hist_u_three_selected_value_def;
                  candle_fs_hist_u_selected_real_def] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC
      (SPECL
        [`boxes:((num#num)#(num#num))list`; `values:num->real`;
         `coordinate:num`;
         `candle_fs_real
           (SND (candle_fs_interval_lookup coordinate boxes))`]
        candle_fs_hist_u_three_nondecreasing_forward) THEN
    ASM_REWRITE_TAC[candle_fs_interval_contains_def] THEN
    ASM_REAL_ARITH_TAC;
    COND_CASES_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`boxes:((num#num)#(num#num))list`; `values:num->real`;
           `coordinate:num`;
           `candle_fs_real
             (FST (candle_fs_interval_lookup coordinate boxes))`]
          candle_fs_hist_u_three_nonincreasing_backward) THEN
      ASM_REWRITE_TAC[candle_fs_interval_contains_def] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[candle_fs_hist_delta_x4_update_self; REAL_LE_REFL]];
    MATCH_MP_TAC
      (SPECL
        [`boxes:((num#num)#(num#num))list`; `values:num->real`;
         `coordinate:num`;
         `candle_fs_real
           (FST (candle_fs_interval_lookup coordinate boxes))`]
        candle_fs_hist_u_three_nondecreasing_backward) THEN
    ASM_REWRITE_TAC[candle_fs_interval_contains_def] THEN
    ASM_REAL_ARITH_TAC;
    COND_CASES_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`boxes:((num#num)#(num#num))list`; `values:num->real`;
           `coordinate:num`;
           `candle_fs_real
             (SND (candle_fs_interval_lookup coordinate boxes))`]
          candle_fs_hist_u_three_nonincreasing_forward) THEN
      ASM_REWRITE_TAC[candle_fs_interval_contains_def] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[candle_fs_hist_delta_x4_update_self; REAL_LE_REFL]]]);;

let candle_fs_hist_u_three_monotone_prefix_def = new_definition
 `candle_fs_hist_u_three_monotone_prefix upper boxes
      (values:num->real) prefix_length =
    \i. if i < prefix_length then
          candle_fs_hist_u_three_selected_value upper i boxes values
        else values i`;;

let candle_fs_hist_u_three_monotone_prefix_zero = prove
 (`!upper boxes (values:num->real).
     candle_fs_hist_u_three_monotone_prefix
       upper boxes values 0 = values`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FUN_EQ_THM;
              candle_fs_hist_u_three_monotone_prefix_def; LT]);;

let candle_fs_hist_u_three_monotone_prefix_suc = prove
 (`!upper boxes (values:num->real) prefix_length.
     candle_fs_hist_u_three_monotone_prefix
       upper boxes values (SUC prefix_length) =
     candle_fs_hist_delta_x4_update
       (candle_fs_hist_u_three_monotone_prefix
         upper boxes values prefix_length)
       prefix_length
       (candle_fs_hist_u_three_selected_value
         upper prefix_length boxes values)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `i:num` THEN
  REWRITE_TAC[candle_fs_hist_u_three_monotone_prefix_def;
              candle_fs_hist_delta_x4_update_def] THEN
  ASM_CASES_TAC `i:num = prefix_length` THEN ASM_REWRITE_TAC[] THENL
   [ARITH_TAC;
    ASM_CASES_TAC `i:num < prefix_length` THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let candle_fs_hist_u_three_monotone_prefix_coordinate = prove
 (`!upper boxes (values:num->real) prefix_length.
     candle_fs_hist_u_three_monotone_prefix
       upper boxes values prefix_length prefix_length =
     values prefix_length`,
  REWRITE_TAC[candle_fs_hist_u_three_monotone_prefix_def; LT_REFL]);;

let candle_fs_hist_u_three_selected_value_prefix = prove
 (`!upper boxes (values:num->real) prefix_length.
     candle_fs_hist_u_three_selected_value upper prefix_length boxes
       (candle_fs_hist_u_three_monotone_prefix
         upper boxes values prefix_length) =
     candle_fs_hist_u_three_selected_value upper prefix_length boxes values`,
  REWRITE_TAC[candle_fs_hist_u_three_selected_value_def;
              candle_fs_hist_u_three_monotone_prefix_coordinate]);;

let candle_fs_hist_u_three_monotone_prefix_contains = prove
 (`!prefix_length upper boxes (values:num->real).
     prefix_length <= 3 /\
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3)
     ==> ALL2 candle_fs_interval_contains boxes
       (list_of_seq
         (candle_fs_hist_u_three_monotone_prefix
           upper boxes values prefix_length) 3)`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[candle_fs_hist_u_three_monotone_prefix_zero];
    POP_ASSUM (LABEL_TAC "prefix_ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `prefix_length < 3` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_fs_interval_contains
        (candle_fs_interval_lookup prefix_length boxes)
        (candle_fs_hist_u_three_selected_value
          upper prefix_length boxes values)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC candle_fs_hist_u_three_selected_value_in_box THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ALL2 candle_fs_interval_contains boxes
        (list_of_seq
          (candle_fs_hist_u_three_monotone_prefix
            upper boxes values prefix_length) 3)`
    ASSUME_TAC THENL
     [USE_THEN "prefix_ih" (fun th ->
        MATCH_MP_TAC
          (SPECL
            [`upper:bool`; `boxes:((num#num)#(num#num))list`;
             `values:num->real`] th)) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[candle_fs_hist_u_three_monotone_prefix_suc] THEN
    MATCH_MP_TAC
      (SPECL
        [`3`; `boxes:((num#num)#(num#num))list`;
         `candle_fs_hist_u_three_monotone_prefix
           (upper:bool) boxes (values:num->real) prefix_length`;
         `prefix_length:num`;
         `candle_fs_hist_u_three_selected_value
           upper prefix_length boxes values`]
        candle_fs_hist_delta_x4_update_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_fs_hist_u_three_monotone_prefix_upper = prove
 (`!prefix_length boxes (values:num->real).
     prefix_length <= 3 /\
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3)
     ==> candle_fs_hist_u_three_vector_real values <=
         candle_fs_hist_u_three_vector_real
           (candle_fs_hist_u_three_monotone_prefix
             T boxes values prefix_length)`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[candle_fs_hist_u_three_monotone_prefix_zero;
                REAL_LE_REFL];
    POP_ASSUM (LABEL_TAC "upper_ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `prefix_length < 3` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ALL2 candle_fs_interval_contains boxes
        (list_of_seq
          (candle_fs_hist_u_three_monotone_prefix
            T boxes (values:num->real) prefix_length) 3)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`prefix_length:num`; `T`;
           `boxes:((num#num)#(num#num))list`; `values:num->real`]
          candle_fs_hist_u_three_monotone_prefix_contains) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_fs_hist_u_three_vector_real values <=
      candle_fs_hist_u_three_vector_real
        (candle_fs_hist_u_three_monotone_prefix
          T boxes values prefix_length)`
    ASSUME_TAC THENL
     [USE_THEN "upper_ih" (fun th ->
        MATCH_MP_TAC
          (SPECL [`boxes:((num#num)#(num#num))list`;
                  `values:num->real`] th)) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_fs_hist_u_three_vector_real
        (candle_fs_hist_u_three_monotone_prefix
          T boxes values prefix_length) <=
      candle_fs_hist_u_three_vector_real
        (candle_fs_hist_delta_x4_update
          (candle_fs_hist_u_three_monotone_prefix
            T boxes values prefix_length)
          prefix_length
          (candle_fs_hist_u_three_selected_value
            T prefix_length boxes values))`
    ASSUME_TAC THENL
     [MP_TAC
        (SPECL
          [`T`; `boxes:((num#num)#(num#num))list`;
           `candle_fs_hist_u_three_monotone_prefix
             T boxes (values:num->real) prefix_length`;
           `prefix_length:num`]
          candle_fs_hist_u_three_monotone_step) THEN
      ASM_REWRITE_TAC[candle_fs_hist_u_three_selected_value_prefix];
      ALL_TAC] THEN
    REWRITE_TAC[candle_fs_hist_u_three_monotone_prefix_suc] THEN
    ASM_REAL_ARITH_TAC]);;

let candle_fs_hist_u_three_monotone_prefix_lower = prove
 (`!prefix_length boxes (values:num->real).
     prefix_length <= 3 /\
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3)
     ==> candle_fs_hist_u_three_vector_real
           (candle_fs_hist_u_three_monotone_prefix
             F boxes values prefix_length) <=
         candle_fs_hist_u_three_vector_real values`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[candle_fs_hist_u_three_monotone_prefix_zero;
                REAL_LE_REFL];
    POP_ASSUM (LABEL_TAC "lower_ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `prefix_length < 3` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ALL2 candle_fs_interval_contains boxes
        (list_of_seq
          (candle_fs_hist_u_three_monotone_prefix
            F boxes (values:num->real) prefix_length) 3)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC
        (SPECL
          [`prefix_length:num`; `F`;
           `boxes:((num#num)#(num#num))list`; `values:num->real`]
          candle_fs_hist_u_three_monotone_prefix_contains) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_fs_hist_u_three_vector_real
        (candle_fs_hist_u_three_monotone_prefix
          F boxes values prefix_length) <=
      candle_fs_hist_u_three_vector_real values`
    ASSUME_TAC THENL
     [USE_THEN "lower_ih" (fun th ->
        MATCH_MP_TAC
          (SPECL [`boxes:((num#num)#(num#num))list`;
                  `values:num->real`] th)) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_fs_hist_u_three_vector_real
        (candle_fs_hist_delta_x4_update
          (candle_fs_hist_u_three_monotone_prefix
            F boxes values prefix_length)
          prefix_length
          (candle_fs_hist_u_three_selected_value
            F prefix_length boxes values)) <=
      candle_fs_hist_u_three_vector_real
        (candle_fs_hist_u_three_monotone_prefix
          F boxes values prefix_length)`
    ASSUME_TAC THENL
     [MP_TAC
        (SPECL
          [`F`; `boxes:((num#num)#(num#num))list`;
           `candle_fs_hist_u_three_monotone_prefix
             F boxes (values:num->real) prefix_length`;
           `prefix_length:num`]
          candle_fs_hist_u_three_monotone_step) THEN
      ASM_REWRITE_TAC[candle_fs_hist_u_three_selected_value_prefix];
      ALL_TAC] THEN
    REWRITE_TAC[candle_fs_hist_u_three_monotone_prefix_suc] THEN
    ASM_REAL_ARITH_TAC]);;

let candle_fs_hist_u_three_monotone_prefix_selected = prove
 (`!upper boxes (values:num->real) coordinate.
     coordinate < 3
     ==> candle_fs_hist_u_three_monotone_prefix
           upper boxes values 3 coordinate =
         candle_fs_hist_u_three_selected_value
           upper coordinate boxes values`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_three_monotone_prefix_def] THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_u_three_prefix_upper_point_bounds = prove
 (`!boxes (values:num->real) coordinate.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3
     ==> EL 0
           (candle_fs_hist_u_points_real
             (candle_fs_interval_lookup coordinate boxes)
             (candle_fs_interval_lookup coordinate
               (SND (candle_fs_hist_u_three_boxes boxes)))) <=
         candle_fs_hist_u_three_monotone_prefix
           T boxes values 3 coordinate /\
         candle_fs_hist_u_three_monotone_prefix
           T boxes values 3 coordinate <=
         EL 1
           (candle_fs_hist_u_points_real
             (candle_fs_interval_lookup coordinate boxes)
             (candle_fs_interval_lookup coordinate
               (SND (candle_fs_hist_u_three_boxes boxes))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REWRITE_TAC
   [MATCH_MP
     (SPECL
       [`T`; `boxes:((num#num)#(num#num))list`; `values:num->real`;
        `coordinate:num`]
       candle_fs_hist_u_three_monotone_prefix_selected)
     (ASSUME `(coordinate:num) < 3`)] THEN
  REWRITE_TAC[candle_fs_hist_u_three_selected_value_def] THEN
  MATCH_MP_TAC candle_fs_hist_u_selected_upper_point_bounds THEN
  MATCH_MP_TAC
    (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
            `values:num->real`; `coordinate:num`]
      candle_fs_hist_interval_lookup_contains) THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_u_three_prefix_lower_point_bounds = prove
 (`!boxes (values:num->real) coordinate.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3
     ==> EL 3
           (candle_fs_hist_u_points_real
             (candle_fs_interval_lookup coordinate boxes)
             (candle_fs_interval_lookup coordinate
               (SND (candle_fs_hist_u_three_boxes boxes)))) <=
         candle_fs_hist_u_three_monotone_prefix
           F boxes values 3 coordinate /\
         candle_fs_hist_u_three_monotone_prefix
           F boxes values 3 coordinate <=
         EL 2
           (candle_fs_hist_u_points_real
             (candle_fs_interval_lookup coordinate boxes)
             (candle_fs_interval_lookup coordinate
               (SND (candle_fs_hist_u_three_boxes boxes))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REWRITE_TAC
   [MATCH_MP
     (SPECL
       [`F`; `boxes:((num#num)#(num#num))list`; `values:num->real`;
        `coordinate:num`]
       candle_fs_hist_u_three_monotone_prefix_selected)
     (ASSUME `(coordinate:num) < 3`)] THEN
  REWRITE_TAC[candle_fs_hist_u_three_selected_value_def] THEN
  MATCH_MP_TAC candle_fs_hist_u_selected_lower_point_bounds THEN
  MATCH_MP_TAC
    (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
            `values:num->real`; `coordinate:num`]
      candle_fs_hist_interval_lookup_contains) THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_u_points_real_nonnegative = prove
 (`!x gradient value.
     candle_fs_raw_le (0,0) (FST x) /\
     candle_fs_interval_contains x value
     ==> ALL (\point. &0 <= point)
       (candle_fs_hist_u_points_real x gradient)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_raw_le_zero_real;
              candle_fs_interval_contains_def] THEN
  STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_points_real_def;
              LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL]) THEN
  ASM_REAL_ARITH_TAC);;

let candle_fs_hist_u_points_real_length = prove
 (`!x gradient.
     LENGTH (candle_fs_hist_u_points_real x gradient) = 4`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_points_real_def;
              LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_u_points_real_endpoints_nonnegative = prove
 (`!x gradient value.
     candle_fs_raw_le (0,0) (FST x) /\
     candle_fs_interval_contains x value
     ==> &0 <= EL 0 (candle_fs_hist_u_points_real x gradient) /\
         &0 <= EL 3 (candle_fs_hist_u_points_real x gradient)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_raw_le_zero_real;
              candle_fs_interval_contains_def] THEN
  STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_points_real_def;
              LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let candle_fs_hist_u_three_points_real_def = new_definition
 `candle_fs_hist_u_three_points_real boxes coordinate =
    candle_fs_hist_u_points_real
      (candle_fs_interval_lookup coordinate boxes)
      (candle_fs_interval_lookup coordinate
        (SND (candle_fs_hist_u_three_boxes boxes)))`;;

let candle_fs_hist_u_three_formula_real_def = new_definition
 `candle_fs_hist_u_three_formula_real selector boxes =
    candle_fs_hist_u_value_formula_real
      (EL selector (candle_fs_hist_u_three_points_real boxes 0))
      (EL selector (candle_fs_hist_u_three_points_real boxes 1))
      (EL selector (candle_fs_hist_u_three_points_real boxes 2))
      (EL (selector + 1) (candle_fs_hist_u_three_points_real boxes 0))
      (EL (selector + 1) (candle_fs_hist_u_three_points_real boxes 1))
      (EL (selector + 1) (candle_fs_hist_u_three_points_real boxes 2))`;;

let candle_fs_hist_u_three_point_zero_nonnegative = prove
 (`!boxes (values:num->real) coordinate.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3 /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup coordinate boxes))
     ==> &0 <= EL 0
       (candle_fs_hist_u_three_points_real boxes coordinate)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_three_points_real_def] THEN
  MP_TAC
   (SPECL
     [`candle_fs_interval_lookup coordinate boxes`;
      `candle_fs_interval_lookup coordinate
        (SND (candle_fs_hist_u_three_boxes boxes))`;
      `(values:num->real) coordinate`]
     candle_fs_hist_u_points_real_endpoints_nonnegative) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC
       (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
               `values:num->real`; `coordinate:num`]
         candle_fs_hist_interval_lookup_contains) THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN (fun th -> MATCH_ACCEPT_TAC (CONJUNCT1 th))]);;

let candle_fs_hist_u_three_point_three_nonnegative = prove
 (`!boxes (values:num->real) coordinate.
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     coordinate < 3 /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup coordinate boxes))
     ==> &0 <= EL 3
       (candle_fs_hist_u_three_points_real boxes coordinate)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_three_points_real_def] THEN
  MP_TAC
   (SPECL
     [`candle_fs_interval_lookup coordinate boxes`;
      `candle_fs_interval_lookup coordinate
        (SND (candle_fs_hist_u_three_boxes boxes))`;
      `(values:num->real) coordinate`]
     candle_fs_hist_u_points_real_endpoints_nonnegative) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC
       (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
               `values:num->real`; `coordinate:num`]
         candle_fs_hist_interval_lookup_contains) THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN (fun th -> MATCH_ACCEPT_TAC (CONJUNCT2 th))]);;

let candle_fs_hist_u_three_prefix_upper_formula_bound = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 0 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 1 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 2 boxes))
     ==> candle_fs_hist_u_three_vector_real
           (candle_fs_hist_u_three_monotone_prefix T boxes values 3) <=
         candle_fs_hist_u_three_formula_real 0 boxes`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_three_formula_real_def] THEN
  MP_TAC
   (SPECL
     [`EL 0 (candle_fs_hist_u_three_points_real boxes 0)`;
      `candle_fs_hist_u_three_monotone_prefix T boxes values 3 0`;
      `EL 1 (candle_fs_hist_u_three_points_real boxes 0)`;
      `EL 0 (candle_fs_hist_u_three_points_real boxes 1)`;
      `candle_fs_hist_u_three_monotone_prefix T boxes values 3 1`;
      `EL 1 (candle_fs_hist_u_three_points_real boxes 1)`;
      `EL 0 (candle_fs_hist_u_three_points_real boxes 2)`;
      `candle_fs_hist_u_three_monotone_prefix T boxes values 3 2`;
      `EL 1 (candle_fs_hist_u_three_points_real boxes 2)`]
     candle_fs_hist_u_termwise_bounds) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `0`]
         candle_fs_hist_u_three_point_zero_nonnegative) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `0`]
         candle_fs_hist_u_three_prefix_upper_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]];
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `0`]
         candle_fs_hist_u_three_prefix_upper_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]];
      MATCH_MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `1`]
         candle_fs_hist_u_three_point_zero_nonnegative) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `1`]
         candle_fs_hist_u_three_prefix_upper_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]];
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `1`]
         candle_fs_hist_u_three_prefix_upper_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]];
      MATCH_MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `2`]
         candle_fs_hist_u_three_point_zero_nonnegative) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `2`]
         candle_fs_hist_u_three_prefix_upper_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]];
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `2`]
         candle_fs_hist_u_three_prefix_upper_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]]];
    DISCH_THEN (fun th -> MP_TAC (CONJUNCT2 th)) THEN
    REWRITE_TAC[candle_fs_hist_u_three_vector_real_def] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let candle_fs_hist_u_three_prefix_lower_formula_bound = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 0 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 1 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 2 boxes))
     ==> candle_fs_hist_u_three_formula_real 2 boxes <=
         candle_fs_hist_u_three_vector_real
           (candle_fs_hist_u_three_monotone_prefix F boxes values 3)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_three_formula_real_def] THEN
  MP_TAC
   (SPECL
     [`EL 3 (candle_fs_hist_u_three_points_real boxes 0)`;
      `candle_fs_hist_u_three_monotone_prefix F boxes values 3 0`;
      `EL 2 (candle_fs_hist_u_three_points_real boxes 0)`;
      `EL 3 (candle_fs_hist_u_three_points_real boxes 1)`;
      `candle_fs_hist_u_three_monotone_prefix F boxes values 3 1`;
      `EL 2 (candle_fs_hist_u_three_points_real boxes 1)`;
      `EL 3 (candle_fs_hist_u_three_points_real boxes 2)`;
      `candle_fs_hist_u_three_monotone_prefix F boxes values 3 2`;
      `EL 2 (candle_fs_hist_u_three_points_real boxes 2)`]
     candle_fs_hist_u_termwise_bounds) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `0`]
         candle_fs_hist_u_three_point_three_nonnegative) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `0`]
         candle_fs_hist_u_three_prefix_lower_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]];
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `0`]
         candle_fs_hist_u_three_prefix_lower_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]];
      MATCH_MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `1`]
         candle_fs_hist_u_three_point_three_nonnegative) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `1`]
         candle_fs_hist_u_three_prefix_lower_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]];
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `1`]
         candle_fs_hist_u_three_prefix_lower_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]];
      MATCH_MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `2`]
         candle_fs_hist_u_three_point_three_nonnegative) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `2`]
         candle_fs_hist_u_three_prefix_lower_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]];
      MP_TAC
       (SPECL [`boxes:((num#num)#(num#num))list`;
               `values:num->real`; `2`]
         candle_fs_hist_u_three_prefix_lower_point_bounds) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        DISCH_THEN
         (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_REWRITE_TAC[candle_fs_hist_u_three_points_real_def]]];
    DISCH_THEN (fun th -> MP_TAC (CONJUNCT1 th)) THEN
    REWRITE_TAC[candle_fs_hist_u_three_vector_real_def] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let candle_fs_hist_u_three_formula_def = new_definition
 `candle_fs_hist_u_three_formula selector boxes =
    candle_fs_hist_u_value_formula selector
      (candle_fs_hist_u_points
        (candle_fs_interval_lookup 0 boxes)
        (candle_fs_interval_lookup 0
          (SND (candle_fs_hist_u_three_boxes boxes))))
      (candle_fs_hist_u_points
        (candle_fs_interval_lookup 1 boxes)
        (candle_fs_interval_lookup 1
          (SND (candle_fs_hist_u_three_boxes boxes))))
      (candle_fs_hist_u_points
        (candle_fs_interval_lookup 2 boxes)
        (candle_fs_interval_lookup 2
          (SND (candle_fs_hist_u_three_boxes boxes))))`;;

let candle_fs_hist_u_three_formula_contains = prove
 (`!selector boxes.
     selector + 1 < 4
     ==> candle_fs_interval_contains
       (candle_fs_hist_u_three_formula selector boxes)
       (candle_fs_hist_u_three_formula_real selector boxes)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_three_formula_def;
              candle_fs_hist_u_three_formula_real_def;
              candle_fs_hist_u_three_points_real_def] THEN
  MATCH_MP_TAC candle_fs_hist_u_value_formula_points_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fs_hist_u_three_value_formula_endpoints = prove
 (`!boxes.
     FST (candle_fs_hist_u_three_boxes boxes) =
     (FST (candle_fs_hist_u_three_formula 2 boxes),
      SND (candle_fs_hist_u_three_formula 0 boxes))`,
  GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_u_three_boxes_def;
              candle_fs_hist_u_three_formula_def;
              candle_fs_hist_u_three_def;
              candle_fs_hist_u_def;
              candle_fs_interval_lookup_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  REWRITE_TAC[candle_fs_hist_interval_lookup_three] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_fs_hist_u_three_value_contains = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 3 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 3) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 0 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 1 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 2 boxes))
     ==> candle_fs_interval_contains
       (FST (candle_fs_hist_u_three_boxes boxes))
       (candle_fs_hist_u_three_vector_real values)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_real
      (FST (candle_fs_hist_u_three_formula 2 boxes)) <=
    candle_fs_hist_u_three_formula_real 2 boxes`
  ASSUME_TAC THENL
   [MP_TAC
     (SPECL [`2`; `boxes:((num#num)#(num#num))list`]
       candle_fs_hist_u_three_formula_contains) THEN
    ANTS_TAC THENL
     [ARITH_TAC;
      DISCH_THEN (fun th ->
       MATCH_ACCEPT_TAC
        (CONJUNCT1
          (REWRITE_RULE[candle_fs_interval_contains_def] th)))];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_formula_real 0 boxes <=
    candle_fs_real
      (SND (candle_fs_hist_u_three_formula 0 boxes))`
  ASSUME_TAC THENL
   [MP_TAC
     (SPECL [`0`; `boxes:((num#num)#(num#num))list`]
       candle_fs_hist_u_three_formula_contains) THEN
    ANTS_TAC THENL
     [ARITH_TAC;
      DISCH_THEN (fun th ->
       MATCH_ACCEPT_TAC
        (CONJUNCT2
          (REWRITE_RULE[candle_fs_interval_contains_def] th)))];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_formula_real 2 boxes <=
    candle_fs_hist_u_three_vector_real
      (candle_fs_hist_u_three_monotone_prefix F boxes values 3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_u_three_prefix_lower_formula_bound THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_vector_real
      (candle_fs_hist_u_three_monotone_prefix F boxes values 3) <=
    candle_fs_hist_u_three_vector_real values`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
     (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
             `values:num->real`]
       candle_fs_hist_u_three_monotone_prefix_lower) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_vector_real values <=
    candle_fs_hist_u_three_vector_real
      (candle_fs_hist_u_three_monotone_prefix T boxes values 3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
     (SPECL [`3`; `boxes:((num#num)#(num#num))list`;
             `values:num->real`]
       candle_fs_hist_u_three_monotone_prefix_upper) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_hist_u_three_vector_real
      (candle_fs_hist_u_three_monotone_prefix T boxes values 3) <=
    candle_fs_hist_u_three_formula_real 0 boxes`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fs_hist_u_three_prefix_upper_formula_bound THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_fs_interval_contains_def;
              candle_fs_hist_u_three_value_formula_endpoints;
              FST; SND] THEN
  ASM_REAL_ARITH_TAC);;

let candle_fs_hist_u126_value_contains = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 0 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 1 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 5 boxes))
     ==> candle_fs_interval_contains
       (FST (candle_fs_hist_u126 boxes))
       (candle_fs_hist_u126_real values)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (SPECL
     [`[candle_fs_interval_lookup 0 boxes;
        candle_fs_interval_lookup 1 boxes;
        candle_fs_interval_lookup 5 boxes]`;
      `(\coordinate.
         if coordinate = 0 then (values:num->real) 0
         else if coordinate = 1 then values 1
         else values 5):num->real`]
     candle_fs_hist_u_three_value_contains) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
      CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
      REWRITE_TAC[ALL2] THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN
      MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[candle_fs_hist_interval_lookup_three];
      ASM_REWRITE_TAC[candle_fs_hist_interval_lookup_three];
      ASM_REWRITE_TAC[candle_fs_hist_interval_lookup_three]];
    REWRITE_TAC[candle_fs_hist_u126_def;
                candle_fs_hist_u126_real_def;
                candle_fs_hist_u_three_boxes_def;
                candle_fs_hist_u_three_vector_real_def;
                candle_fs_hist_u_def;
                LET_DEF; LET_END_DEF; FST; SND] THEN
    REWRITE_TAC[candle_fs_hist_interval_lookup_three] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let candle_fs_hist_u135_value_contains = prove
 (`!boxes (values:num->real).
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes (list_of_seq values 6) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 0 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 2 boxes)) /\
     candle_fs_raw_le (0,0)
       (FST (candle_fs_interval_lookup 4 boxes))
     ==> candle_fs_interval_contains
       (FST (candle_fs_hist_u135 boxes))
       (candle_fs_hist_u135_real values)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (SPECL
     [`[candle_fs_interval_lookup 0 boxes;
        candle_fs_interval_lookup 2 boxes;
        candle_fs_interval_lookup 4 boxes]`;
      `(\coordinate.
         if coordinate = 0 then (values:num->real) 0
         else if coordinate = 1 then values 2
         else values 4):num->real`]
     candle_fs_hist_u_three_value_contains) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
      CONV_TAC (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
      REWRITE_TAC[ALL2] THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN
      MATCH_MP_TAC candle_fs_hist_six_lookup_contains THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[candle_fs_hist_interval_lookup_three];
      ASM_REWRITE_TAC[candle_fs_hist_interval_lookup_three];
      ASM_REWRITE_TAC[candle_fs_hist_interval_lookup_three]];
    REWRITE_TAC[candle_fs_hist_u135_def;
                candle_fs_hist_u135_real_def;
                candle_fs_hist_u_three_boxes_def;
                candle_fs_hist_u_three_vector_real_def;
                candle_fs_hist_u_def;
                LET_DEF; LET_END_DEF; FST; SND] THEN
    REWRITE_TAC[candle_fs_hist_interval_lookup_three] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV]);;

end;;
