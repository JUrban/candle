(* ========================================================================== *)
(* Executable exact result for the three optimized product-delta steps.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the encoded ordinary Taylor state for *)
(* 4 * x_i * delta at source coordinates 0, 1, and 2.  The definitions are  *)
(* coordinate-parametric; the source dispatcher later restricts the opcodes. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_neg_derivative_result_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_product_state_complete_sound.ml";;

module Candle_cv_analytic_expr_packed_source_delta_product_result_compute = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_first_jet_representation;;
open Candle_cv_whole_box_jet;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_packed_source_delta_value;;
open Candle_cv_analytic_expr_packed_source_delta_gradient;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_product_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_product_state_sound;;
open Candle_cv_analytic_expr_packed_source_delta_product_state_complete_sound;;
open Candle_cv_analytic_expr_packed_source_delta_product_jet_sound;;
open Candle_cv_analytic_expr_packed_source_delta_specialized_result_sound;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_result_compute;;

let candle_cv_q_packed_delta_product_center_value_def = new_definition
 `candle_cv_q_packed_delta_product_center_value coordinate_value delta_value =
    candle_cv_q_packed_delta_scale4
      (candle_cv_q_interval_mul coordinate_value delta_value)`;;

let candle_cv_q_packed_delta_product_center_value_correct = prove
 (`!coordinate_value delta_value.
     candle_cv_q_packed_delta_product_center_value
       (candle_cv_q_interval coordinate_value)
       (candle_cv_q_interval delta_value) =
     candle_cv_q_interval
       (candle_q_packed_delta_product_center_value
         coordinate_value delta_value)`,
  REWRITE_TAC
    [candle_cv_q_packed_delta_product_center_value_def;
     candle_q_packed_delta_product_center_value_def;
     candle_cv_q_interval_mul_correct;
     candle_cv_q_packed_delta_scale4_correct]);;

let candle_cv_q_packed_delta_product_center_gradient_entry_def =
  new_definition
 `candle_cv_q_packed_delta_product_center_gradient_entry coordinate
      coordinate_value delta_value delta_gradient derivative_coordinate =
    let base = candle_cv_q_interval_mul coordinate_value
      (candle_cv_q_interval_lookup derivative_coordinate delta_gradient) in
    let complete =
      Cexp_if (Cexp_eq derivative_coordinate coordinate)
        (candle_cv_q_interval_add base delta_value) base in
    candle_cv_q_packed_delta_scale4 complete`;;

let candle_cv_q_packed_delta_product_center_gradient_entry_correct = prove
 (`!coordinate coordinate_value delta_value delta_gradient
       derivative_coordinate.
     candle_cv_q_packed_delta_product_center_gradient_entry
       (Cexp_num coordinate) (candle_cv_q_interval coordinate_value)
       (candle_cv_q_interval delta_value)
       (candle_cv_q_interval_list delta_gradient)
       (Cexp_num derivative_coordinate) =
     candle_cv_q_interval
       (candle_q_packed_delta_product_center_gradient_entry coordinate
         coordinate_value delta_value delta_gradient
         derivative_coordinate)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(derivative_coordinate:num) = coordinate` THEN
  ASM_REWRITE_TAC
    [candle_cv_q_packed_delta_product_center_gradient_entry_def;
     candle_q_packed_delta_product_center_gradient_entry_def;
     candle_cv_q_interval_mul_correct;
     candle_cv_q_interval_lookup_correct;
     candle_cv_q_interval_add_correct;
     candle_cv_q_packed_delta_scale4_correct;
     LET_DEF; LET_END_DEF;
     cexp_eq_def; injectivity "cval"; cexp_if_def]);;

let candle_cv_q_packed_delta_product_center_gradient_six_def =
  new_definition
 `candle_cv_q_packed_delta_product_center_gradient_six coordinate
      coordinate_value delta_value delta_gradient =
    candle_cv_q_packed_delta_six
      (candle_cv_q_packed_delta_product_center_gradient_entry coordinate
        coordinate_value delta_value delta_gradient (Cexp_num 0))
      (candle_cv_q_packed_delta_product_center_gradient_entry coordinate
        coordinate_value delta_value delta_gradient (Cexp_num 1))
      (candle_cv_q_packed_delta_product_center_gradient_entry coordinate
        coordinate_value delta_value delta_gradient (Cexp_num 2))
      (candle_cv_q_packed_delta_product_center_gradient_entry coordinate
        coordinate_value delta_value delta_gradient (Cexp_num 3))
      (candle_cv_q_packed_delta_product_center_gradient_entry coordinate
        coordinate_value delta_value delta_gradient (Cexp_num 4))
      (candle_cv_q_packed_delta_product_center_gradient_entry coordinate
        coordinate_value delta_value delta_gradient (Cexp_num 5))`;;

let candle_cv_q_packed_delta_product_center_gradient_six_correct = prove
 (`!coordinate coordinate_value delta_value delta_gradient.
     candle_cv_q_packed_delta_product_center_gradient_six
       (Cexp_num coordinate) (candle_cv_q_interval coordinate_value)
       (candle_cv_q_interval delta_value)
       (candle_cv_q_interval_list delta_gradient) =
     candle_cv_q_interval_list
       (candle_q_packed_delta_product_center_gradient_six coordinate
         coordinate_value delta_value delta_gradient)`,
  REWRITE_TAC
    [candle_cv_q_packed_delta_product_center_gradient_six_def;
     candle_q_packed_delta_product_center_gradient_six_def;
     candle_cv_q_packed_delta_product_center_gradient_entry_correct;
     candle_cv_q_packed_delta_six_correct]);;

let _ = print_endline "CANDLE_PRODUCT_DELTA_RESULT_STAGE center";;

let candle_cv_q_packed_delta_product_hessian_six_def = new_definition
 `candle_cv_q_packed_delta_product_hessian_six coordinate box_coordinate
      delta_gradient delta_hessian =
    candle_cv_q_packed_delta_product_hessian coordinate box_coordinate
      delta_gradient
      (candle_cv_q_packed_delta_indices
        candle_q_packed_delta_hessian_indices)
      delta_hessian`;;

let candle_cv_q_packed_delta_product_hessian_six_correct = prove
 (`!coordinate box_coordinate delta_gradient delta_hessian.
     candle_cv_q_packed_delta_product_hessian_six
       (Cexp_num coordinate) (candle_cv_q_interval box_coordinate)
       (candle_cv_q_interval_list delta_gradient)
       (candle_cv_q_interval_list delta_hessian) =
     candle_cv_q_interval_list
       (candle_q_packed_delta_product_hessian_six coordinate
         box_coordinate delta_gradient delta_hessian)`,
  REWRITE_TAC
    [candle_cv_q_packed_delta_product_hessian_six_def;
     candle_q_packed_delta_product_hessian_six_def;
     candle_cv_q_packed_delta_product_hessian_correct]);;

let candle_q_packed_delta_product_hessian_six_length = prove
 (`!coordinate box_coordinate delta_gradient x0 x1 x2 x3 x4 x5.
     LENGTH
       (candle_q_packed_delta_product_hessian_six coordinate
         box_coordinate delta_gradient
         (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)) = 21`,
  REWRITE_TAC
    [candle_q_packed_delta_product_hessian_six_def;
     candle_q_packed_delta_hessian_indices_def;
     candle_q_packed_delta_hessian_six_def;
     candle_q_packed_delta_hessian_rows_six_def;
     candle_q_packed_delta_sums_def;
     candle_q_packed_delta_product_hessian_def;
     LET_DEF; LET_END_DEF; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let _ = print_endline "CANDLE_PRODUCT_DELTA_RESULT_STAGE hessian";;

let candle_cv_q_packed_delta_product_jet_six_def = new_definition
 `candle_cv_q_packed_delta_product_jet_six coordinate
      x0 x1 x2 x3 x4 x5 =
    let inputs = candle_cv_q_packed_delta_six x0 x1 x2 x3 x4 x5 in
    let coordinate_value = candle_cv_q_interval_lookup coordinate inputs in
    let delta_value =
      candle_cv_q_packed_delta_value_six x0 x1 x2 x3 x4 x5 in
    let delta_gradient =
      candle_cv_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5 in
    let delta_hessian =
      candle_cv_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5 in
    candle_cv_q_dim_jet_make
      (candle_cv_q_packed_delta_product_center_value
        coordinate_value delta_value)
      (candle_cv_q_packed_delta_product_center_gradient_six coordinate
        coordinate_value delta_value delta_gradient)
      (candle_cv_q_packed_hessian6_expand
        (candle_cv_q_packed_delta_product_hessian_six coordinate
          coordinate_value delta_gradient delta_hessian))`;;

let candle_cv_q_packed_delta_product_jet_six_correct = prove
 (`!coordinate x0 x1 x2 x3 x4 x5.
     candle_cv_q_packed_delta_product_jet_six
       (Cexp_num coordinate)
       (candle_cv_q_interval x0) (candle_cv_q_interval x1)
       (candle_cv_q_interval x2) (candle_cv_q_interval x3)
       (candle_cv_q_interval x4) (candle_cv_q_interval x5) =
     candle_cv_q_dim_jet_encode
       (candle_q_packed_delta_product_jet_six coordinate
         x0 x1 x2 x3 x4 x5)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_hessian6_expand
      (candle_cv_q_interval_list
        (candle_q_packed_delta_product_hessian_six coordinate
          (candle_q_interval_lookup coordinate [x0;x1;x2;x3;x4;x5])
          (candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5)
          (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5))) =
    candle_cv_q_interval_matrix
      (candle_q_packed_hessian6_expand
        (candle_q_packed_delta_product_hessian_six coordinate
          (candle_q_interval_lookup coordinate [x0;x1;x2;x3;x4;x5])
          (candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5)
          (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_cv_q_packed_hessian6_expand_correct THEN
    REWRITE_TAC[candle_q_packed_delta_product_hessian_six_length];
    ALL_TAC] THEN
  REWRITE_TAC
    [candle_cv_q_packed_delta_product_jet_six_def;
     candle_q_packed_delta_product_jet_six_def;
     candle_cv_q_packed_delta_six_correct;
     candle_cv_q_interval_lookup_correct;
     candle_cv_q_packed_delta_value_six_correct;
     candle_cv_q_packed_delta_gradient_six_correct;
     candle_cv_q_packed_delta_hessian_six_correct;
     LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC
    [candle_cv_q_packed_delta_product_center_value_correct;
     candle_cv_q_packed_delta_product_center_gradient_six_correct;
     candle_cv_q_packed_delta_product_hessian_six_correct;
     candle_cv_q_dim_jet_make_correct]);;

let _ = print_endline "CANDLE_PRODUCT_DELTA_RESULT_STAGE jet";;

let candle_cv_q_packed_delta_product_jet_environment_def = new_definition
 `candle_cv_q_packed_delta_product_jet_environment coordinate environment =
    candle_cv_q_packed_delta_product_jet_six coordinate
      (candle_cv_q_interval_lookup (Cexp_num 0) environment)
      (candle_cv_q_interval_lookup (Cexp_num 1) environment)
      (candle_cv_q_interval_lookup (Cexp_num 2) environment)
      (candle_cv_q_interval_lookup (Cexp_num 3) environment)
      (candle_cv_q_interval_lookup (Cexp_num 4) environment)
      (candle_cv_q_interval_lookup (Cexp_num 5) environment)`;;

let candle_cv_q_packed_delta_product_jet_environment_correct = prove
 (`!coordinate environment.
     candle_cv_q_packed_delta_product_jet_environment
       (Cexp_num coordinate) (candle_cv_q_interval_list environment) =
     candle_cv_q_dim_jet_encode
       (candle_q_packed_delta_product_jet_environment
         coordinate environment)`,
  REWRITE_TAC
    [candle_cv_q_packed_delta_product_jet_environment_def;
     candle_q_packed_delta_product_jet_environment_def;
     candle_cv_q_interval_lookup_correct;
     candle_cv_q_packed_delta_product_jet_six_correct]);;

let _ = print_endline "CANDLE_PRODUCT_DELTA_RESULT_STAGE environment";;

let candle_cv_q_packed_delta_product_result_def = new_definition
 `candle_cv_q_packed_delta_product_result boxes coordinate =
    let center_jet =
      candle_cv_q_packed_delta_product_jet_environment coordinate
        (candle_cv_q_center_environment_list boxes) in
    let box_jet =
      candle_cv_q_packed_delta_product_jet_environment coordinate boxes in
    candle_cv_q_dim_taylor_model_result_complete
      (candle_cv_q_fixed_list_round_upper (candle_cv_q_radius_list boxes))
      (Cexp_num 1)
      (candle_cv_q_dim_jet_first_projection center_jet)
      (candle_cv_q_dim_jet_hessian box_jet)`;;

let candle_cv_q_packed_delta_product_result_correct = prove
 (`!boxes coordinate.
     candle_cv_q_packed_delta_product_result
       (candle_cv_q_interval_list boxes) (Cexp_num coordinate) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_packed_delta_product_result boxes coordinate)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_delta_product_jet_environment
      (Cexp_num coordinate)
      (candle_cv_q_interval_list
        (candle_q_center_environment_list boxes)) =
    candle_cv_q_dim_jet_encode
      (candle_q_packed_delta_product_jet_environment coordinate
        (candle_q_center_environment_list boxes))`
   ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC
      candle_cv_q_packed_delta_product_jet_environment_correct;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_delta_product_jet_environment
      (Cexp_num coordinate) (candle_cv_q_interval_list boxes) =
    candle_cv_q_dim_jet_encode
      (candle_q_packed_delta_product_jet_environment coordinate boxes)`
   ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC
      candle_cv_q_packed_delta_product_jet_environment_correct;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_cv_q_dim_jet_first_projection
      (candle_cv_q_packed_delta_product_jet_environment
        (Cexp_num coordinate)
        (candle_cv_q_interval_list
          (candle_q_center_environment_list boxes))) =
    candle_cv_q_dim_first_jet_encode
      (candle_q_packed_delta_product_jet_environment coordinate
        (candle_q_center_environment_list boxes))`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM candle_cv_q_dim_first_jet_encode_projection];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_cv_q_dim_jet_hessian
      (candle_cv_q_packed_delta_product_jet_environment
        (Cexp_num coordinate) (candle_cv_q_interval_list boxes)) =
    candle_cv_q_interval_matrix
      (candle_q_dim_jet_hessian
        (candle_q_packed_delta_product_jet_environment coordinate boxes))`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[candle_cv_q_dim_jet_hessian_correct];
    ALL_TAC] THEN
  REWRITE_TAC
    [candle_cv_q_packed_delta_product_result_def;
     candle_q_packed_delta_product_result_def;
     candle_cv_q_center_environment_list_correct;
     candle_cv_q_radius_list_correct;
     candle_cv_q_fixed_list_round_upper_correct;
     LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[candle_cv_bool_true_encoding] THEN
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_complete_correct]);;

let _ = print_endline "CANDLE_PRODUCT_DELTA_RESULT_STAGE result";;

let candle_cv_q_packed_source_delta_product_result_compute_eqs =
  union
    candle_cv_q_packed_source_delta_neg_derivative_result_compute_eqs
    (union
      candle_cv_q_packed_source_delta_product_hessian_compute_eqs
      (map SPEC_ALL
        [candle_cv_q_packed_delta_product_center_value_def;
         candle_cv_q_packed_delta_product_center_gradient_entry_def;
         candle_cv_q_packed_delta_product_center_gradient_six_def;
         candle_cv_q_packed_delta_indices_def;
         candle_cv_q_packed_delta_product_hessian_six_def;
         candle_cv_q_packed_delta_product_jet_six_def;
         candle_cv_q_packed_delta_product_jet_environment_def;
         candle_cv_q_packed_delta_product_result_def]));;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_delta_product_center_value_correct;
     candle_cv_q_packed_delta_product_center_gradient_entry_correct;
     candle_cv_q_packed_delta_product_center_gradient_six_correct;
     candle_cv_q_packed_delta_product_hessian_six_correct;
     candle_q_packed_delta_product_hessian_six_length;
     candle_cv_q_packed_delta_product_jet_six_correct;
     candle_cv_q_packed_delta_product_jet_environment_correct;
     candle_cv_q_packed_delta_product_result_correct] then
  failwith "packed product delta result compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_PRODUCT_RESULT_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
