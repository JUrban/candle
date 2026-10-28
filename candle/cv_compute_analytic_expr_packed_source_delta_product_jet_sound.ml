(* ========================================================================== *)
(* Complete six-dimensional analytic jet for [4 * x_i * delta].             *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This packages the optimized center value and *)
(* gradient together with its packed whole-box Hessian as the generic        *)
(* analytic-jet invariant consumed by source-program induction.              *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_neg_derivative_jet_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_product_state_complete_sound.ml";;

module Candle_cv_analytic_expr_packed_source_delta_product_jet_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_packed_source_delta_value;;
open Candle_cv_analytic_expr_packed_source_delta_gradient;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_product_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_product_state_sound;;
open Candle_cv_analytic_expr_packed_source_delta_product_state_complete_sound;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_jet_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;

let candle_q_packed_delta_product_jet_six_def = new_definition
 `candle_q_packed_delta_product_jet_six coordinate x0 x1 x2 x3 x4 x5 =
    let coordinate_value =
      candle_q_interval_lookup coordinate [x0;x1;x2;x3;x4;x5] in
    let delta_value =
      candle_q_packed_delta_value_six x0 x1 x2 x3 x4 x5 in
    let delta_gradient =
      candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5 in
    let delta_hessian =
      candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5 in
    candle_q_dim_jet_make
      (candle_q_packed_delta_product_center_value
        coordinate_value delta_value)
      (candle_q_packed_delta_product_center_gradient_six coordinate
        coordinate_value delta_value delta_gradient)
      (candle_q_packed_hessian6_expand
        (candle_q_packed_delta_product_hessian_six coordinate
          coordinate_value delta_gradient delta_hessian))`;;

let candle_q_packed_delta_product_jet_six_shape = prove
 (`!coordinate x0 x1 x2 x3 x4 x5.
     candle_q_dim_jet_shape 6
       (candle_q_packed_delta_product_jet_six coordinate
         x0 x1 x2 x3 x4 x5)`,
  REPEAT GEN_TAC THEN
  let matrix_shape =
    ISPEC
      `candle_q_packed_delta_product_hessian_six coordinate
        (candle_q_interval_lookup coordinate [x0;x1;x2;x3;x4;x5])
        (candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5)
        (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5):
        ((((num#num)#num)#((num#num)#num))list)`
      candle_q_packed_hessian6_expand_shape in
  REWRITE_TAC[candle_q_packed_delta_product_jet_six_def;
              candle_q_dim_jet_shape_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_q_packed_delta_product_center_gradient_six_def;
              LET_DEF; LET_END_DEF; LENGTH;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_all] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCEPT_TAC matrix_shape);;

let candle_q_packed_delta_product_jet_six_analytic_contains = prove
 (`!x0 x1 x2 x3 x4 x5 v0 v1 v2 v3 v4 v5 coordinate.
     candle_q_interval_contains x0 v0 /\
     candle_q_interval_contains x1 v1 /\
     candle_q_interval_contains x2 v2 /\
     candle_q_interval_contains x3 v3 /\
     candle_q_interval_contains x4 v4 /\
     candle_q_interval_contains x5 v5 /\
     coordinate < 6
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_delta_product_jet_six coordinate
         x0 x1 x2 x3 x4 x5)
       [v0;v1;v2;v3;v4;v5]
       (candle_packed_delta_product_expr coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let input_contains =
    end_itlist CONJ
      (map ASSUME
        [`candle_q_interval_contains x0 v0`;
         `candle_q_interval_contains x1 v1`;
         `candle_q_interval_contains x2 v2`;
         `candle_q_interval_contains x3 v3`;
         `candle_q_interval_contains x4 v4`;
         `candle_q_interval_contains x5 v5`]) in
  let coordinate_lt = ASSUME `(coordinate:num) < 6` in
  SUBGOAL_THEN
   `candle_q_stack_contains [x0;x1;x2;x3;x4;x5]
      [v0;v1;v2;v3;v4;v5]`
   ASSUME_TAC THENL
   [REWRITE_TAC[candle_q_stack_contains_all2; ALL2] THEN
    ACCEPT_TAC input_contains;
    ALL_TAC] THEN
  let input_stack_contains =
    ASSUME
      `candle_q_stack_contains
        [x0;x1;x2;x3;x4;x5]
        [v0;v1;v2;v3;v4;v5]` in
  let coordinate_contains =
    MATCH_MP
      (SPECL
        [`coordinate:num`;
         `[x0;x1;x2;x3;x4;x5]:
            (((num#num)#num)#((num#num)#num))list`;
         `[v0;v1;v2;v3;v4;v5]:real list`]
        candle_q_stack_lookup_contains)
      input_stack_contains in
  let delta_value_contains =
    MATCH_MP
      (SPECL
        [`x0:((num#num)#num)#((num#num)#num)`;
         `x1:((num#num)#num)#((num#num)#num)`;
         `x2:((num#num)#num)#((num#num)#num)`;
         `x3:((num#num)#num)#((num#num)#num)`;
         `x4:((num#num)#num)#((num#num)#num)`;
         `x5:((num#num)#num)#((num#num)#num)`;
         `v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`]
        candle_q_packed_delta_value_six_sound)
      input_contains in
  let delta_gradient_contains =
    MATCH_MP
      (SPECL
        [`x0:((num#num)#num)#((num#num)#num)`;
         `x1:((num#num)#num)#((num#num)#num)`;
         `x2:((num#num)#num)#((num#num)#num)`;
         `x3:((num#num)#num)#((num#num)#num)`;
         `x4:((num#num)#num)#((num#num)#num)`;
         `x5:((num#num)#num)#((num#num)#num)`;
         `v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`]
        candle_q_packed_delta_gradient_six_sound)
      input_contains in
  let delta_gradient_contains =
    REWRITE_RULE[GSYM candle_q_stack_contains_all2]
      delta_gradient_contains in
  let delta_hessian_contains =
    MATCH_MP
      (SPECL
        [`x0:((num#num)#num)#((num#num)#num)`;
         `x1:((num#num)#num)#((num#num)#num)`;
         `x2:((num#num)#num)#((num#num)#num)`;
         `x3:((num#num)#num)#((num#num)#num)`;
         `x4:((num#num)#num)#((num#num)#num)`;
         `x5:((num#num)#num)#((num#num)#num)`;
         `v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`]
        candle_q_packed_delta_hessian_six_sound)
      input_contains in
  let delta_hessian_contains =
    REWRITE_RULE[GSYM candle_q_stack_contains_all2]
      delta_hessian_contains in
  let exact_value_contains =
    MATCH_MP
      (SPECL
        [`candle_q_interval_lookup coordinate [x0;x1;x2;x3;x4;x5]`;
         `candle_q_packed_delta_value_six x0 x1 x2 x3 x4 x5`;
         `candle_q_real_lookup coordinate [v0;v1;v2;v3;v4;v5]`;
         `candle_packed_delta_real v0 v1 v2 v3 v4 v5`]
        candle_q_packed_delta_product_center_value_sound)
      (CONJ coordinate_contains delta_value_contains) in
  let analytic_value =
    MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`]
        candle_packed_delta_product_analytic_value)
      coordinate_lt in
  let value_contains =
    REWRITE_RULE[GSYM analytic_value] exact_value_contains in
  let gradient_contains =
    MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`;
         `candle_q_interval_lookup coordinate [x0;x1;x2;x3;x4;x5]`;
         `candle_q_packed_delta_value_six x0 x1 x2 x3 x4 x5`;
         `candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5`;
         `candle_q_real_lookup coordinate [v0;v1;v2;v3;v4;v5]`;
         `candle_packed_delta_real v0 v1 v2 v3 v4 v5`;
         `candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5`]
        candle_q_packed_delta_product_center_gradient_six_sound)
      (end_itlist CONJ
        [coordinate_lt; coordinate_contains; delta_value_contains;
         delta_gradient_contains;
         REFL `candle_q_real_lookup coordinate [v0;v1;v2;v3;v4;v5]`;
         REFL `candle_packed_delta_real v0 v1 v2 v3 v4 v5`;
         REFL
           `candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5`]) in
  let packed_hessian_contains =
    MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`;
         `candle_q_interval_lookup coordinate [x0;x1;x2;x3;x4;x5]`;
         `candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5`;
         `candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5`]
        candle_q_packed_delta_product_hessian_six_sound)
      (end_itlist CONJ
        [coordinate_lt; coordinate_contains; delta_gradient_contains;
         delta_hessian_contains]) in
  let matrix_contains =
    MATCH_MP
      (ISPECL
        [`candle_q_packed_delta_product_hessian_six coordinate
            (candle_q_interval_lookup coordinate [x0;x1;x2;x3;x4;x5])
            (candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5)
            (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)`;
         `(\rowindex colindex.
            candle_analytic_dd rowindex colindex
              [v0;v1;v2;v3;v4;v5]
              (candle_packed_delta_product_expr coordinate))`]
        candle_q_packed_hessian6_expand_contains_symmetric_values)
      packed_hessian_contains in
  let matrix_contains =
    REWRITE_RULE[candle_q_symmetric_hessian6_analytic_values]
      matrix_contains in
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_packed_delta_product_jet_six_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THENL
   [ACCEPT_TAC value_contains;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC
      (MATCH_MP
        (SPECL
          [`i:num`;
           `candle_q_packed_delta_product_center_gradient_six coordinate
              (candle_q_interval_lookup coordinate [x0;x1;x2;x3;x4;x5])
              (candle_q_packed_delta_value_six x0 x1 x2 x3 x4 x5)
              (candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5)`;
           `list_of_seq
              (\derivative_coordinate.
                candle_analytic_d derivative_coordinate
                  [v0;v1;v2;v3;v4;v5]
                  (candle_packed_delta_product_expr coordinate)) 6`]
          candle_q_stack_lookup_contains)
        gradient_contains) THEN
    ASM_SIMP_TAC[candle_q_real_lookup_list_of_seq];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC candle_q_packed_matrix_list_of_seq_lookup_contains THEN
    EXISTS_TAC `6` THEN
    ASM_REWRITE_TAC[candle_q_packed_hessian6_expand_shape] THEN
    MP_TAC matrix_contains THEN ASM_REWRITE_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_delta_product_jet_six_shape;
     candle_q_packed_delta_product_jet_six_analytic_contains] then
  failwith "packed delta product jet: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_PRODUCT_JET_OK DEVELOPMENT_NON_RELEASE";;

end;;
