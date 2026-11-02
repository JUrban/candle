(* ========================================================================== *)
(* Executable exact object-q constants and variables.                        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  These are the first executable constructors   *)
(* for the full-source exact object entry.  They use the fixed six-variable  *)
(* and packed-21 shapes proved by the analytic object layer.                  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_representation.ml";;
needs "candle/cv_compute_polynomial_expr_dim_jet_representation.ml";;

module Candle_cv_analytic_expr_packed_source_object_algebraic_compute = struct

open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_algebraic_sound;;
open Candle_cv_analytic_expr_packed_source_object_pi_half_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;

let candle_cv_q_packed_object_zero_gradient6_def = new_definition
 `candle_cv_q_packed_object_zero_gradient6 =
    candle_cv_q_interval_list candle_q_packed_object_zero_gradient6`;;

let candle_cv_q_packed_object_zero_hessian21_def = new_definition
 `candle_cv_q_packed_object_zero_hessian21 =
    candle_cv_q_interval_list candle_q_packed_object_zero_hessian21`;;

let candle_cv_q_packed_object_constant_state_def = new_definition
 `candle_cv_q_packed_object_constant_state rational_payload =
    candle_cv_q_packed_object_state_make
      (candle_cv_bool T) (Cexp_pair rational_payload rational_payload)
      candle_cv_q_packed_object_zero_gradient6
      (Cexp_pair rational_payload rational_payload)
      candle_cv_q_packed_object_zero_gradient6
      candle_cv_q_packed_object_zero_hessian21`;;

let candle_cv_q_packed_object_constant_state_correct = prove
 (`!positive negative denominator_predecessor.
     candle_cv_q_packed_object_constant_state
       (candle_cv_q ((positive,negative),denominator_predecessor)) =
     candle_cv_q_packed_object_state_encode
       (Candle_q_packed_object_state T
         (candle_q_packed_object_constant_interval
           positive negative denominator_predecessor)
         candle_q_packed_object_zero_gradient6
         (candle_q_packed_object_constant_interval
           positive negative denominator_predecessor)
         candle_q_packed_object_zero_gradient6
         candle_q_packed_object_zero_hessian21)`,
  REWRITE_TAC[candle_cv_q_packed_object_constant_state_def;
              candle_cv_q_packed_object_state_encode_def;
              candle_cv_q_packed_object_state_make_def;
              candle_cv_q_packed_object_zero_gradient6_def;
              candle_cv_q_packed_object_zero_hessian21_def;
              candle_q_packed_object_constant_interval_def;
              candle_cv_q_interval_def]);;

let candle_cv_q_packed_object_variable_state_def = new_definition
 `candle_cv_q_packed_object_variable_state center_boxes outer_boxes variable =
    candle_cv_q_packed_object_state_make
      (candle_cv_bool T)
      (candle_cv_q_interval_lookup variable center_boxes)
      (candle_cv_q_dim_interval_unit variable
        candle_cv_q_packed_object_zero_gradient6)
      (candle_cv_q_interval_lookup variable outer_boxes)
      (candle_cv_q_dim_interval_unit variable
        candle_cv_q_packed_object_zero_gradient6)
      candle_cv_q_packed_object_zero_hessian21`;;

let candle_cv_q_packed_object_variable_state_correct = prove
 (`!center_boxes outer_boxes variable.
     candle_cv_q_packed_object_variable_state
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes) (Cexp_num variable) =
     candle_cv_q_packed_object_state_encode
       (Candle_q_packed_object_state T
         (candle_q_interval_lookup variable center_boxes)
         (candle_q_packed_object_unit_gradient6 variable)
         (candle_q_interval_lookup variable outer_boxes)
         (candle_q_packed_object_unit_gradient6 variable)
         candle_q_packed_object_zero_hessian21)`,
  REWRITE_TAC[candle_cv_q_packed_object_variable_state_def;
              candle_cv_q_packed_object_state_encode_def;
              candle_cv_q_packed_object_state_make_def;
              candle_cv_q_packed_object_zero_gradient6_def;
              candle_cv_q_packed_object_zero_hessian21_def;
              candle_q_packed_object_unit_gradient6_def;
              candle_cv_q_interval_lookup_correct;
              candle_cv_q_dim_interval_unit_correct]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_constant_state_correct;
     candle_cv_q_packed_object_variable_state_correct] then
  failwith "packed object algebraic compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_ALGEBRAIC_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
