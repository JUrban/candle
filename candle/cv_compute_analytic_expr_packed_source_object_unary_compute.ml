(* ========================================================================== *)
(* Executable exact object-q unary chain-rule arithmetic.                    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  These functions preserve the raw rational   *)
(* association order of the HOL4 object-q unary constructor.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_mul_compute.ml";;

module Candle_cv_analytic_expr_packed_source_object_unary_compute = struct

open Candle_cv_exact_interval_mul_core;;
open Candle_cv_analytic_expr_packed_source_object_add_sound;;
open Candle_cv_analytic_expr_packed_source_object_unary_sound;;
open Candle_cv_analytic_expr_packed_source_object_inverse_sound;;
open Candle_cv_analytic_expr_packed_source_object_atn_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_linear_compute;;
open Candle_cv_analytic_expr_packed_source_object_mul_compute;;

let candle_cv_q_packed_object_interval_list_scale_def = define
 `(candle_cv_q_packed_object_interval_list_scale scalar (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_q_packed_object_interval_list_scale scalar
     (Cexp_pair head tail) =
     Cexp_pair (candle_cv_q_interval_mul scalar head)
       (candle_cv_q_packed_object_interval_list_scale scalar tail))`;;

let candle_cv_q_packed_object_interval_list_scale_correct = prove
 (`!scalar values.
     candle_cv_q_packed_object_interval_list_scale
       (candle_cv_q_interval scalar)
       (candle_cv_q_interval_list values) =
     candle_cv_q_interval_list
       (candle_q_packed_object_interval_list_scale scalar values)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_packed_object_interval_list_scale_def;
     candle_q_packed_object_interval_list_scale_def;
     candle_cv_q_interval_list_def;
     candle_cv_q_interval_mul_correct; MAP]);;

let _ = print_endline "CANDLE_OBJECT_UNARY_STAGE list-scale";;

let candle_cv_q_packed_object_interval_self_outer_def = define
 `(candle_cv_q_packed_object_interval_self_outer (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_q_packed_object_interval_self_outer (Cexp_pair head tail) =
     candle_cv_q_packed_object_interval_list_append
       (candle_cv_q_packed_object_interval_list_scale head
         (Cexp_pair head tail))
       (candle_cv_q_packed_object_interval_self_outer tail))`;;

let candle_cv_q_packed_object_interval_self_outer_correct = prove
 (`!values.
     candle_cv_q_packed_object_interval_self_outer
       (candle_cv_q_interval_list values) =
     candle_cv_q_interval_list
       (candle_q_packed_object_interval_self_outer values)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC
      [candle_cv_q_packed_object_interval_self_outer_def;
       candle_q_packed_object_interval_self_outer_def;
       candle_cv_q_interval_list_def];
    SUBGOAL_THEN
     `candle_cv_q_packed_object_interval_list_scale
        (candle_cv_q_interval h)
        (Cexp_pair (candle_cv_q_interval h)
          (candle_cv_q_interval_list t)) =
      candle_cv_q_interval_list
        (candle_q_packed_object_interval_list_scale h (CONS h t))`
     ASSUME_TAC THENL
     [MP_TAC
        (SPECL
          [`h:((num#num)#num)#((num#num)#num)`;
           `CONS h t:
             (((num#num)#num)#((num#num)#num))list`]
          candle_cv_q_packed_object_interval_list_scale_correct) THEN
      REWRITE_TAC[candle_cv_q_interval_list_def];
      ASM_REWRITE_TAC
        [candle_cv_q_interval_list_def;
         candle_cv_q_packed_object_interval_self_outer_def;
         candle_q_packed_object_interval_self_outer_def;
         candle_cv_q_packed_object_interval_list_append_correct]]]);;

let _ = print_endline "CANDLE_OBJECT_UNARY_STAGE self-outer";;

let candle_cv_q_packed_object_unary_hessian6_def = new_definition
 `candle_cv_q_packed_object_unary_hessian6 first_interval second_interval
      gradient packed_hessian =
    candle_cv_q_packed_object_interval_list_add
      (candle_cv_q_packed_object_interval_list_scale second_interval
        (candle_cv_q_packed_object_interval_self_outer gradient))
      (candle_cv_q_packed_object_interval_list_scale first_interval
        packed_hessian)`;;

let candle_q_packed_object_unary_hessian6_add_eq = prove
 (`!first_interval second_interval gradient packed_hessian.
     candle_q_packed_object_unary_hessian6
       first_interval second_interval gradient packed_hessian =
     candle_q_packed_object_interval_list_add
       (candle_q_packed_object_interval_list_scale second_interval
         (candle_q_packed_object_interval_self_outer gradient))
       (candle_q_packed_object_interval_list_scale first_interval
         packed_hessian)`,
  REWRITE_TAC[candle_q_packed_object_unary_hessian6_def;
              candle_q_packed_object_interval_list_add_def]);;

let candle_cv_q_packed_object_unary_hessian6_correct = prove
 (`!first_interval second_interval gradient packed_hessian.
     LENGTH gradient = 6 /\ LENGTH packed_hessian = 21
     ==>
     candle_cv_q_packed_object_unary_hessian6
       (candle_cv_q_interval first_interval)
       (candle_cv_q_interval second_interval)
       (candle_cv_q_interval_list gradient)
       (candle_cv_q_interval_list packed_hessian) =
     candle_cv_q_interval_list
       (candle_q_packed_object_unary_hessian6
         first_interval second_interval gradient packed_hessian)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_unary_hessian6_def;
     candle_q_packed_object_unary_hessian6_add_eq;
     candle_cv_q_packed_object_interval_self_outer_correct;
     candle_cv_q_packed_object_interval_list_scale_correct] THEN
  MATCH_MP_TAC candle_cv_q_packed_object_interval_list_add_correct THEN
  REWRITE_TAC[candle_q_packed_object_interval_list_scale_length] THEN
  SUBGOAL_THEN
   `LENGTH (candle_q_packed_object_interval_self_outer gradient) = 21`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_interval_self_outer6_length THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let _ = print_endline "CANDLE_OBJECT_UNARY_STAGE unary-hessian";;

let candle_cv_q_packed_object_state_unary_def = new_definition
 `candle_cv_q_packed_object_state_unary radii result_interval
      center_first box_first box_second state =
    let center_gradient =
      candle_cv_q_packed_object_interval_list_scale center_first
        (candle_cv_q_packed_object_state_center_gradient state) in
    let packed_hessian =
      candle_cv_q_packed_object_unary_hessian6 box_first box_second
        (candle_cv_q_packed_object_state_gradient_bounds state)
        (candle_cv_q_packed_object_state_packed_hessian state) in
    candle_cv_q_packed_object_state_recomplete radii
      (candle_cv_q_packed_object_state_domain state)
      result_interval center_gradient packed_hessian`;;

let candle_cv_q_packed_object_state_unary_correct = prove
 (`!radii result_interval center_first box_first box_second
       domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     LENGTH radii = 6 /\
     LENGTH center_gradient = 6 /\
     LENGTH gradient_bounds = 6 /\
     LENGTH packed_hessian = 21
     ==>
     candle_cv_q_packed_object_state_unary
       (candle_cv_q_list radii)
       (candle_cv_q_interval result_interval)
       (candle_cv_q_interval center_first)
       (candle_cv_q_interval box_first)
       (candle_cv_q_interval box_second)
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_q_packed_object_state_encode
       (Candle_q_packed_object_state domain result_interval
         (candle_q_packed_object_interval_list_scale
           center_first center_gradient)
         (candle_q_packed_object_value_bound6 radii result_interval
           (candle_q_packed_object_interval_list_scale
             center_first center_gradient)
           (candle_q_packed_object_unary_hessian6
             box_first box_second gradient_bounds packed_hessian))
         (candle_q_packed_object_gradient_complete6 radii
           (candle_q_packed_object_interval_list_scale
             center_first center_gradient)
           (candle_q_packed_object_unary_hessian6
             box_first box_second gradient_bounds packed_hessian))
         (candle_q_packed_object_unary_hessian6
           box_first box_second gradient_bounds packed_hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_interval_list_scale
      (candle_cv_q_interval center_first)
      (candle_cv_q_interval_list center_gradient) =
    candle_cv_q_interval_list
      (candle_q_packed_object_interval_list_scale
        center_first center_gradient)`
   ASSUME_TAC THENL
   [REWRITE_TAC[candle_cv_q_packed_object_interval_list_scale_correct];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_unary_hessian6
      (candle_cv_q_interval box_first)
      (candle_cv_q_interval box_second)
      (candle_cv_q_interval_list gradient_bounds)
      (candle_cv_q_interval_list packed_hessian) =
    candle_cv_q_interval_list
      (candle_q_packed_object_unary_hessian6
        box_first box_second gradient_bounds packed_hessian)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_cv_q_packed_object_unary_hessian6_correct THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_q_packed_object_unary_hessian6
        box_first box_second gradient_bounds packed_hessian) = 21`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_unary_hessian6_length THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC
    [candle_cv_q_packed_object_state_unary_def; LET_DEF; LET_END_DEF;
     candle_cv_q_packed_object_state_domain_correct;
     candle_cv_q_packed_object_state_center_gradient_correct;
     candle_cv_q_packed_object_state_gradient_bounds_correct;
     candle_cv_q_packed_object_state_packed_hessian_correct] THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_recomplete_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_UNARY_STAGE state-unary";;

let candle_cv_q_packed_object_inverse_derivative_def = new_definition
 `candle_cv_q_packed_object_inverse_derivative reciprocal =
    candle_cv_q_interval_neg
      (candle_cv_q_interval_mul reciprocal reciprocal)`;;

let candle_cv_q_packed_object_inverse_derivative_correct = prove
 (`!reciprocal.
     candle_cv_q_packed_object_inverse_derivative
       (candle_cv_q_interval reciprocal) =
     candle_cv_q_interval
       (candle_q_packed_object_inverse_derivative reciprocal)`,
  REWRITE_TAC
    [candle_cv_q_packed_object_inverse_derivative_def;
     candle_q_packed_object_inverse_derivative_def;
     candle_cv_q_interval_mul_correct;
     candle_cv_q_interval_neg_correct]);;

let candle_cv_q_packed_object_inverse_second_def = new_definition
 `candle_cv_q_packed_object_inverse_second reciprocal =
    candle_cv_q_interval_add
      (candle_cv_q_interval_mul
        (candle_cv_q_interval_mul reciprocal reciprocal) reciprocal)
      (candle_cv_q_interval_mul
        (candle_cv_q_interval_mul reciprocal reciprocal) reciprocal)`;;

let candle_cv_q_packed_object_inverse_second_correct = prove
 (`!reciprocal.
     candle_cv_q_packed_object_inverse_second
       (candle_cv_q_interval reciprocal) =
     candle_cv_q_interval
       (candle_q_packed_object_inverse_second reciprocal)`,
  REWRITE_TAC
    [candle_cv_q_packed_object_inverse_second_def;
     candle_q_packed_object_inverse_second_def;
     candle_cv_q_interval_mul_correct;
     candle_cv_q_interval_add_correct]);;

let _ = print_endline "CANDLE_OBJECT_UNARY_STAGE inverse-derivatives";;

let candle_cv_q_packed_object_state_inverse_def = new_definition
 `candle_cv_q_packed_object_state_inverse radii center_reciprocal
      box_reciprocal state =
    candle_cv_q_packed_object_state_unary radii center_reciprocal
      (candle_cv_q_packed_object_inverse_derivative center_reciprocal)
      (candle_cv_q_packed_object_inverse_derivative box_reciprocal)
      (candle_cv_q_packed_object_inverse_second box_reciprocal)
      state`;;

let candle_cv_q_packed_object_state_inverse_correct = prove
 (`!radii center_reciprocal box_reciprocal
       domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     LENGTH radii = 6 /\
     LENGTH center_gradient = 6 /\
     LENGTH gradient_bounds = 6 /\
     LENGTH packed_hessian = 21
     ==>
     candle_cv_q_packed_object_state_inverse
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_reciprocal)
       (candle_cv_q_interval box_reciprocal)
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_q_packed_object_state_encode
       (Candle_q_packed_object_state domain center_reciprocal
         (candle_q_packed_object_interval_list_scale
           (candle_q_packed_object_inverse_derivative center_reciprocal)
           center_gradient)
         (candle_q_packed_object_value_bound6 radii center_reciprocal
           (candle_q_packed_object_interval_list_scale
             (candle_q_packed_object_inverse_derivative center_reciprocal)
             center_gradient)
           (candle_q_packed_object_unary_hessian6
             (candle_q_packed_object_inverse_derivative box_reciprocal)
             (candle_q_packed_object_inverse_second box_reciprocal)
             gradient_bounds packed_hessian))
         (candle_q_packed_object_gradient_complete6 radii
           (candle_q_packed_object_interval_list_scale
             (candle_q_packed_object_inverse_derivative center_reciprocal)
             center_gradient)
           (candle_q_packed_object_unary_hessian6
             (candle_q_packed_object_inverse_derivative box_reciprocal)
             (candle_q_packed_object_inverse_second box_reciprocal)
             gradient_bounds packed_hessian))
         (candle_q_packed_object_unary_hessian6
           (candle_q_packed_object_inverse_derivative box_reciprocal)
           (candle_q_packed_object_inverse_second box_reciprocal)
           gradient_bounds packed_hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_state_inverse_def;
     candle_cv_q_packed_object_inverse_derivative_correct;
     candle_cv_q_packed_object_inverse_second_correct] THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_unary_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_UNARY_STAGE state-inverse";;

let candle_cv_q_packed_object_state_sqrt_def = new_definition
 `candle_cv_q_packed_object_state_sqrt radii center_root center_first
      box_first box_second_reciprocal state =
    candle_cv_q_packed_object_state_unary radii center_root center_first
      box_first (candle_cv_q_interval_neg box_second_reciprocal) state`;;

let candle_cv_q_packed_object_state_sqrt_correct = prove
 (`!radii center_root center_first box_first box_second_reciprocal
       domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     LENGTH radii = 6 /\
     LENGTH center_gradient = 6 /\
     LENGTH gradient_bounds = 6 /\
     LENGTH packed_hessian = 21
     ==>
     candle_cv_q_packed_object_state_sqrt
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_root)
       (candle_cv_q_interval center_first)
       (candle_cv_q_interval box_first)
       (candle_cv_q_interval box_second_reciprocal)
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_q_packed_object_state_encode
       (Candle_q_packed_object_state domain center_root
         (candle_q_packed_object_interval_list_scale
           center_first center_gradient)
         (candle_q_packed_object_value_bound6 radii center_root
           (candle_q_packed_object_interval_list_scale
             center_first center_gradient)
           (candle_q_packed_object_unary_hessian6 box_first
             (candle_q_interval_neg box_second_reciprocal)
             gradient_bounds packed_hessian))
         (candle_q_packed_object_gradient_complete6 radii
           (candle_q_packed_object_interval_list_scale
             center_first center_gradient)
           (candle_q_packed_object_unary_hessian6 box_first
             (candle_q_interval_neg box_second_reciprocal)
             gradient_bounds packed_hessian))
         (candle_q_packed_object_unary_hessian6 box_first
           (candle_q_interval_neg box_second_reciprocal)
           gradient_bounds packed_hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_state_sqrt_def;
     candle_cv_q_interval_neg_correct] THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_unary_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_UNARY_STAGE state-sqrt";;

let candle_cv_q_packed_object_atn_second_def = new_definition
 `candle_cv_q_packed_object_atn_second source derivative_square =
    candle_cv_q_interval_neg
      (candle_cv_q_interval_mul
        (candle_cv_q_interval_add source source) derivative_square)`;;

let candle_cv_q_packed_object_atn_second_correct = prove
 (`!source derivative_square.
     candle_cv_q_packed_object_atn_second
       (candle_cv_q_interval source)
       (candle_cv_q_interval derivative_square) =
     candle_cv_q_interval
       (candle_q_packed_object_atn_second source derivative_square)`,
  REWRITE_TAC
    [candle_cv_q_packed_object_atn_second_def;
     candle_q_packed_object_atn_second_def;
     candle_cv_q_interval_add_correct;
     candle_cv_q_interval_mul_correct;
     candle_cv_q_interval_neg_correct]);;

let candle_cv_q_packed_object_state_atn_def = new_definition
 `candle_cv_q_packed_object_state_atn radii center_result center_first
      box_first box_first_square state =
    candle_cv_q_packed_object_state_unary radii center_result center_first
      box_first
      (candle_cv_q_packed_object_atn_second
        (candle_cv_q_packed_object_state_value_bound state)
        box_first_square)
      state`;;

let candle_cv_q_packed_object_state_atn_correct = prove
 (`!radii center_result center_first box_first box_first_square
       domain center_value center_gradient value_bound gradient_bounds
       packed_hessian.
     LENGTH radii = 6 /\
     LENGTH center_gradient = 6 /\
     LENGTH gradient_bounds = 6 /\
     LENGTH packed_hessian = 21
     ==>
     candle_cv_q_packed_object_state_atn
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_result)
       (candle_cv_q_interval center_first)
       (candle_cv_q_interval box_first)
       (candle_cv_q_interval box_first_square)
       (candle_cv_q_packed_object_state_encode
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian)) =
     candle_cv_q_packed_object_state_encode
       (Candle_q_packed_object_state domain center_result
         (candle_q_packed_object_interval_list_scale
           center_first center_gradient)
         (candle_q_packed_object_value_bound6 radii center_result
           (candle_q_packed_object_interval_list_scale
             center_first center_gradient)
           (candle_q_packed_object_unary_hessian6 box_first
             (candle_q_packed_object_atn_second
               value_bound box_first_square)
             gradient_bounds packed_hessian))
         (candle_q_packed_object_gradient_complete6 radii
           (candle_q_packed_object_interval_list_scale
             center_first center_gradient)
           (candle_q_packed_object_unary_hessian6 box_first
             (candle_q_packed_object_atn_second
               value_bound box_first_square)
             gradient_bounds packed_hessian))
         (candle_q_packed_object_unary_hessian6 box_first
           (candle_q_packed_object_atn_second
             value_bound box_first_square)
           gradient_bounds packed_hessian))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_state_atn_def;
     candle_cv_q_packed_object_state_value_bound_correct;
     candle_cv_q_packed_object_atn_second_correct] THEN
  MATCH_MP_TAC candle_cv_q_packed_object_state_unary_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_UNARY_STAGE state-atn";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_interval_list_scale_correct;
     candle_cv_q_packed_object_interval_self_outer_correct;
     candle_q_packed_object_unary_hessian6_add_eq;
     candle_cv_q_packed_object_unary_hessian6_correct;
     candle_cv_q_packed_object_state_unary_correct;
     candle_cv_q_packed_object_inverse_derivative_correct;
     candle_cv_q_packed_object_inverse_second_correct;
     candle_cv_q_packed_object_state_inverse_correct;
     candle_cv_q_packed_object_state_sqrt_correct;
     candle_cv_q_packed_object_atn_second_correct;
     candle_cv_q_packed_object_state_atn_correct] then
  failwith "packed object unary compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_UNARY_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
