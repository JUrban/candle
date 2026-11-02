(* ========================================================================== *)
(* Analytic soundness of the exact packed object-q source program.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This layer mirrors the six logical fields of *)
(* [BoundedObjectQTaylor] rather than routing through the older normalized   *)
(* Taylor-result replay.  The first slice packages the exact state and the   *)
(* invariant that the instruction/program induction will preserve.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_algebraic_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_pi_half_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_neg_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_add_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_mul_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_inverse_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_sqrt_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_atn_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_program_sound = struct

open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_taylor_model_packed_object_gradient_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_algebraic_sound;;
open Candle_cv_analytic_expr_packed_source_object_pi_half_sound;;
open Candle_cv_analytic_expr_packed_source_object_neg_sound;;
open Candle_cv_analytic_expr_packed_source_object_add_sound;;
open Candle_cv_analytic_expr_packed_source_object_mul_sound;;
open Candle_cv_analytic_expr_packed_source_object_unary_sound;;
open Candle_cv_analytic_expr_packed_source_object_inverse_sound;;
open Candle_cv_analytic_expr_packed_source_object_sqrt_sound;;
open Candle_cv_analytic_expr_packed_source_object_atn_sound;;

let candle_q_packed_object_state_INDUCT,
    candle_q_packed_object_state_RECURSION = define_type
  "candle_q_packed_object_state =
     Candle_q_packed_object_state
       bool
       (((num#num)#num)#((num#num)#num))
       ((((num#num)#num)#((num#num)#num))list)
       (((num#num)#num)#((num#num)#num))
       ((((num#num)#num)#((num#num)#num))list)
       ((((num#num)#num)#((num#num)#num))list)";;

let candle_q_packed_object_item_INDUCT,
    candle_q_packed_object_item_RECURSION = define_type
  "candle_q_packed_object_item =
     Candle_q_packed_object_item candle_q_packed_object_state
       candle_analytic_expr candle_analytic_expr";;

let candle_q_packed_object_source_item_analytic_invariant_def = define
 `candle_q_packed_object_source_item_analytic_invariant center_boxes outer_boxes
      (Candle_q_packed_object_item
        (Candle_q_packed_object_state domain center_value center_gradient
          value_bound gradient_bounds packed_hessian)
        center_e box_e) <=>
    LENGTH center_gradient = 6 /\
    LENGTH gradient_bounds = 6 /\
    LENGTH packed_hessian = 21 /\
    candle_q_packed_object_item_analytic_invariant
      center_boxes outer_boxes domain center_value center_gradient
      value_bound gradient_bounds packed_hessian center_e box_e`;;

let candle_q_packed_object_source_stack_analytic_invariant_def = new_definition
 `candle_q_packed_object_source_stack_analytic_invariant
      center_boxes outer_boxes stack <=>
    ALL
      (candle_q_packed_object_source_item_analytic_invariant
        center_boxes outer_boxes)
      stack`;;

let candle_q_packed_object_source_item_constant_analytic_invariant = prove
 (`!center_boxes outer_boxes p n d.
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (Candle_q_packed_object_item
         (Candle_q_packed_object_state T
           (candle_q_packed_object_constant_interval p n d)
           candle_q_packed_object_zero_gradient6
           (candle_q_packed_object_constant_interval p n d)
           candle_q_packed_object_zero_gradient6
           candle_q_packed_object_zero_hessian21)
         (Candle_analytic_poly (Candle_poly_const p n d))
         (Candle_analytic_poly (Candle_poly_const p n d)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_analytic_invariant_def;
     candle_q_packed_object_zero_gradient6_length;
     candle_q_packed_object_zero_hessian21_length;
     candle_q_packed_object_constant_analytic_invariant]);;

let candle_q_packed_object_source_item_variable_analytic_invariant = prove
 (`!center_boxes outer_boxes variable.
     variable < 6 /\
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6
     ==>
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (Candle_q_packed_object_item
         (Candle_q_packed_object_state T
           (candle_q_interval_lookup variable center_boxes)
           (candle_q_packed_object_unit_gradient6 variable)
           (candle_q_interval_lookup variable outer_boxes)
           (candle_q_packed_object_unit_gradient6 variable)
           candle_q_packed_object_zero_hessian21)
         (Candle_analytic_poly (Candle_poly_var variable))
         (Candle_analytic_poly (Candle_poly_var variable)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_analytic_invariant_def;
     candle_q_packed_object_unit_gradient6_length;
     candle_q_packed_object_zero_hessian21_length] THEN
  MATCH_MP_TAC candle_q_packed_object_variable_analytic_invariant THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_object_source_item_neg_def = define
 `candle_q_packed_object_source_item_neg radii
      (Candle_q_packed_object_item
        (Candle_q_packed_object_state domain center_value center_gradient
          value_bound gradient_bounds packed_hessian)
        center_e box_e) =
    Candle_q_packed_object_item
      (Candle_q_packed_object_state domain
        (candle_q_interval_neg center_value)
        (candle_q_dim_interval_list_neg center_gradient)
        (candle_q_packed_object_value_bound6 radii
          (candle_q_interval_neg center_value)
          (candle_q_dim_interval_list_neg center_gradient)
          (candle_q_packed_object_hessian_neg packed_hessian))
        (candle_q_packed_object_gradient_complete6 radii
          (candle_q_dim_interval_list_neg center_gradient)
          (candle_q_packed_object_hessian_neg packed_hessian))
        (candle_q_packed_object_hessian_neg packed_hessian))
      (Candle_analytic_neg center_e) (Candle_analytic_neg box_e)`;;

let candle_q_packed_object_source_item_add_def = define
 `candle_q_packed_object_source_item_add radii
      (Candle_q_packed_object_item
        (Candle_q_packed_object_state left_domain left_center_value
          left_center_gradient left_value_bound left_gradient_bounds
          left_hessian) left_center_e left_box_e)
      (Candle_q_packed_object_item
        (Candle_q_packed_object_state right_domain right_center_value
          right_center_gradient right_value_bound right_gradient_bounds
          right_hessian) right_center_e right_box_e) =
    Candle_q_packed_object_item
      (Candle_q_packed_object_state (left_domain /\ right_domain)
        (candle_q_interval_add left_center_value right_center_value)
        (candle_q_packed_object_interval_list_add
          left_center_gradient right_center_gradient)
        (candle_q_packed_object_value_bound6 radii
          (candle_q_interval_add left_center_value right_center_value)
          (candle_q_packed_object_interval_list_add
            left_center_gradient right_center_gradient)
          (candle_q_packed_object_hessian_add
            left_hessian right_hessian))
        (candle_q_packed_object_gradient_complete6 radii
          (candle_q_packed_object_interval_list_add
            left_center_gradient right_center_gradient)
          (candle_q_packed_object_hessian_add
            left_hessian right_hessian))
        (candle_q_packed_object_hessian_add left_hessian right_hessian))
      (Candle_analytic_add left_center_e right_center_e)
      (Candle_analytic_add left_box_e right_box_e)`;;

let candle_q_packed_object_source_item_mul_def = define
 `candle_q_packed_object_source_item_mul radii
      (Candle_q_packed_object_item
        (Candle_q_packed_object_state left_domain left_center_value
          left_center_gradient left_value_bound left_gradient_bounds
          left_hessian) left_center_e left_box_e)
      (Candle_q_packed_object_item
        (Candle_q_packed_object_state right_domain right_center_value
          right_center_gradient right_value_bound right_gradient_bounds
          right_hessian) right_center_e right_box_e) =
    Candle_q_packed_object_item
      (Candle_q_packed_object_state (left_domain /\ right_domain)
        (candle_q_interval_mul left_center_value right_center_value)
        (candle_q_packed_object_fused_scale_add
          right_center_value left_center_gradient
          left_center_value right_center_gradient)
        (candle_q_packed_object_value_bound6 radii
          (candle_q_interval_mul left_center_value right_center_value)
          (candle_q_packed_object_fused_scale_add
            right_center_value left_center_gradient
            left_center_value right_center_gradient)
          (candle_q_packed_object_mul_hessian6
            left_value_bound right_value_bound
            left_gradient_bounds right_gradient_bounds
            left_hessian right_hessian))
        (candle_q_packed_object_gradient_complete6 radii
          (candle_q_packed_object_fused_scale_add
            right_center_value left_center_gradient
            left_center_value right_center_gradient)
          (candle_q_packed_object_mul_hessian6
            left_value_bound right_value_bound
            left_gradient_bounds right_gradient_bounds
            left_hessian right_hessian))
        (candle_q_packed_object_mul_hessian6
          left_value_bound right_value_bound
          left_gradient_bounds right_gradient_bounds
          left_hessian right_hessian))
      (Candle_analytic_mul left_center_e right_center_e)
      (Candle_analytic_mul left_box_e right_box_e)`;;

let candle_q_packed_object_source_item_pi_half_def = new_definition
 `candle_q_packed_object_source_item_pi_half =
    Candle_q_packed_object_item
      (Candle_q_packed_object_state T
        candle_q_packed_object_pi_half_scale40_interval
        candle_q_packed_object_zero_gradient6
        candle_q_packed_object_pi_half_scale40_interval
        candle_q_packed_object_zero_gradient6
        candle_q_packed_object_zero_hessian21)
      Candle_analytic_pi_half Candle_analytic_pi_half`;;

let candle_q_packed_object_source_item_inverse_def = define
 `candle_q_packed_object_source_item_inverse radii center_reciprocal
      box_reciprocal
      (Candle_q_packed_object_item
        (Candle_q_packed_object_state domain center_value center_gradient
          value_bound gradient_bounds packed_hessian)
        center_e box_e) =
    Candle_q_packed_object_item
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
          gradient_bounds packed_hessian))
      (Candle_analytic_inv center_e) (Candle_analytic_inv box_e)`;;

let candle_q_packed_object_source_item_sqrt_def = define
 `candle_q_packed_object_source_item_sqrt radii center_root
      center_derivative box_root box_derivative box_second_reciprocal
      (Candle_q_packed_object_item
        (Candle_q_packed_object_state domain center_value center_gradient
          value_bound gradient_bounds packed_hessian)
        center_e box_e) =
    Candle_q_packed_object_item
      (Candle_q_packed_object_state domain center_root
        (candle_q_packed_object_interval_list_scale
          center_derivative center_gradient)
        (candle_q_packed_object_value_bound6 radii center_root
          (candle_q_packed_object_interval_list_scale
            center_derivative center_gradient)
          (candle_q_packed_object_unary_hessian6 box_derivative
            (candle_q_interval_neg box_second_reciprocal)
            gradient_bounds packed_hessian))
        (candle_q_packed_object_gradient_complete6 radii
          (candle_q_packed_object_interval_list_scale
            center_derivative center_gradient)
          (candle_q_packed_object_unary_hessian6 box_derivative
            (candle_q_interval_neg box_second_reciprocal)
            gradient_bounds packed_hessian))
        (candle_q_packed_object_unary_hessian6 box_derivative
          (candle_q_interval_neg box_second_reciprocal)
          gradient_bounds packed_hessian))
      (candle_packed_analytic_sqrt_with_interval center_root center_e)
      (candle_packed_analytic_sqrt_with_interval box_root box_e)`;;

let candle_q_packed_object_source_item_atn_def = define
 `candle_q_packed_object_source_item_atn radii center_input center_result
      center_square center_derivative box_input box_square box_derivative
      box_derivative_square
      (Candle_q_packed_object_item
        (Candle_q_packed_object_state domain center_value center_gradient
          value_bound gradient_bounds packed_hessian)
        center_e box_e) =
    Candle_q_packed_object_item
      (Candle_q_packed_object_state domain center_result
        (candle_q_packed_object_interval_list_scale
          center_derivative center_gradient)
        (candle_q_packed_object_value_bound6 radii center_result
          (candle_q_packed_object_interval_list_scale
            center_derivative center_gradient)
          (candle_q_packed_object_unary_hessian6 box_derivative
            (candle_q_packed_object_atn_second
              value_bound box_derivative_square)
            gradient_bounds packed_hessian))
        (candle_q_packed_object_gradient_complete6 radii
          (candle_q_packed_object_interval_list_scale
            center_derivative center_gradient)
          (candle_q_packed_object_unary_hessian6 box_derivative
            (candle_q_packed_object_atn_second
              value_bound box_derivative_square)
            gradient_bounds packed_hessian))
        (candle_q_packed_object_unary_hessian6 box_derivative
          (candle_q_packed_object_atn_second
            value_bound box_derivative_square)
          gradient_bounds packed_hessian))
      (Candle_analytic_atn center_e) (Candle_analytic_atn box_e)`;;

let candle_q_packed_object_source_item_neg_analytic_invariant = prove
 (`!center_boxes outer_boxes radii domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (Candle_q_packed_object_item
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian) center_e box_e)
     ==>
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_packed_object_source_item_neg radii
         (Candle_q_packed_object_item
           (Candle_q_packed_object_state domain center_value center_gradient
             value_bound gradient_bounds packed_hessian) center_e box_e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE
      [candle_q_packed_object_source_item_analytic_invariant_def]) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_neg_def;
     candle_q_packed_object_source_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_dim_interval_list_neg_length];
    MATCH_MP_TAC candle_q_packed_object_gradient_complete6_length THEN
    ASM_REWRITE_TAC[candle_q_dim_interval_list_neg_length];
    ASM_REWRITE_TAC[candle_q_packed_object_hessian_neg_length];
    MATCH_MP_TAC candle_q_packed_object_item_neg_analytic_invariant THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `value_bound:((num#num)#num)#((num#num)#num)` THEN
    EXISTS_TAC
      `gradient_bounds:
        (((num#num)#num)#((num#num)#num))list` THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_source_item_add_analytic_invariant = prove
 (`!center_boxes outer_boxes radii
       left_domain left_center_value left_center_gradient left_value_bound
       left_gradient_bounds left_hessian left_center_e left_box_e
       right_domain right_center_value right_center_gradient right_value_bound
       right_gradient_bounds right_hessian right_center_e right_box_e.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (Candle_q_packed_object_item
         (Candle_q_packed_object_state left_domain left_center_value
           left_center_gradient left_value_bound left_gradient_bounds
           left_hessian) left_center_e left_box_e) /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (Candle_q_packed_object_item
         (Candle_q_packed_object_state right_domain right_center_value
           right_center_gradient right_value_bound right_gradient_bounds
           right_hessian) right_center_e right_box_e)
     ==>
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_packed_object_source_item_add radii
         (Candle_q_packed_object_item
           (Candle_q_packed_object_state left_domain left_center_value
             left_center_gradient left_value_bound left_gradient_bounds
             left_hessian) left_center_e left_box_e)
         (Candle_q_packed_object_item
           (Candle_q_packed_object_state right_domain right_center_value
             right_center_gradient right_value_bound right_gradient_bounds
             right_hessian) right_center_e right_box_e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE
      [candle_q_packed_object_source_item_analytic_invariant_def]) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_add_def;
     candle_q_packed_object_source_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC
      (SPECL
        [`left_center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
         `right_center_gradient:
           (((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_object_interval_list_add_length) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_packed_object_gradient_complete6_length THEN
    MP_TAC
      (SPECL
        [`left_center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
         `right_center_gradient:
           (((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_object_interval_list_add_length) THEN
    ASM_REWRITE_TAC[];
    MP_TAC
      (SPECL
        [`left_hessian:
           (((num#num)#num)#((num#num)#num))list`;
         `right_hessian:
           (((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_object_hessian_add_length) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_packed_object_item_add_analytic_invariant THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC
      `left_value_bound:((num#num)#num)#((num#num)#num)` THEN
    EXISTS_TAC
      `left_gradient_bounds:
        (((num#num)#num)#((num#num)#num))list` THEN
    EXISTS_TAC
      `right_value_bound:((num#num)#num)#((num#num)#num)` THEN
    EXISTS_TAC
      `right_gradient_bounds:
        (((num#num)#num)#((num#num)#num))list` THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_source_item_mul_analytic_invariant = prove
 (`!center_boxes outer_boxes radii
       left_domain left_center_value left_center_gradient left_value_bound
       left_gradient_bounds left_hessian left_center_e left_box_e
       right_domain right_center_value right_center_gradient right_value_bound
       right_gradient_bounds right_hessian right_center_e right_box_e.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (Candle_q_packed_object_item
         (Candle_q_packed_object_state left_domain left_center_value
           left_center_gradient left_value_bound left_gradient_bounds
           left_hessian) left_center_e left_box_e) /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (Candle_q_packed_object_item
         (Candle_q_packed_object_state right_domain right_center_value
           right_center_gradient right_value_bound right_gradient_bounds
           right_hessian) right_center_e right_box_e)
     ==>
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_packed_object_source_item_mul radii
         (Candle_q_packed_object_item
           (Candle_q_packed_object_state left_domain left_center_value
             left_center_gradient left_value_bound left_gradient_bounds
             left_hessian) left_center_e left_box_e)
         (Candle_q_packed_object_item
           (Candle_q_packed_object_state right_domain right_center_value
             right_center_gradient right_value_bound right_gradient_bounds
             right_hessian) right_center_e right_box_e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE
      [candle_q_packed_object_source_item_analytic_invariant_def]) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_mul_def;
     candle_q_packed_object_source_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC
      (SPECL
        [`right_center_value:((num#num)#num)#((num#num)#num)`;
         `left_center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
         `left_center_value:((num#num)#num)#((num#num)#num)`;
         `right_center_gradient:
           (((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_object_fused_scale_add_length) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_packed_object_gradient_complete6_length THEN
    MP_TAC
      (SPECL
        [`right_center_value:((num#num)#num)#((num#num)#num)`;
         `left_center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
         `left_center_value:((num#num)#num)#((num#num)#num)`;
         `right_center_gradient:
           (((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_object_fused_scale_add_length) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_packed_object_mul_hessian6_length THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_packed_object_item_mul_analytic_invariant THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_source_item_pi_half_analytic_invariant = prove
 (`!center_boxes outer_boxes.
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes candle_q_packed_object_source_item_pi_half`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_pi_half_def;
     candle_q_packed_object_source_item_analytic_invariant_def;
     candle_q_packed_object_zero_gradient6_length;
     candle_q_packed_object_zero_hessian21_length;
     candle_q_packed_object_pi_half_scale40_analytic_invariant]);;

let candle_q_packed_object_source_item_inverse_analytic_invariant = prove
 (`!center_boxes outer_boxes radii domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
       center_reciprocal box_reciprocal.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_interval_inv_certificate center_value center_reciprocal /\
     candle_q_interval_inv_certificate value_bound box_reciprocal /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (Candle_q_packed_object_item
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian) center_e box_e)
     ==>
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_packed_object_source_item_inverse radii center_reciprocal
         box_reciprocal
         (Candle_q_packed_object_item
           (Candle_q_packed_object_state domain center_value center_gradient
             value_bound gradient_bounds packed_hessian) center_e box_e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE
      [candle_q_packed_object_source_item_analytic_invariant_def]) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_inverse_def;
     candle_q_packed_object_source_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_packed_object_interval_list_scale_length];
    MATCH_MP_TAC candle_q_packed_object_gradient_complete6_length THEN
    ASM_REWRITE_TAC[candle_q_packed_object_interval_list_scale_length];
    MATCH_MP_TAC candle_q_packed_object_unary_hessian6_length THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`center_boxes:
           (((num#num)#num)#((num#num)#num))list`;
         `outer_boxes:
           (((num#num)#num)#((num#num)#num))list`;
         `radii:((num#num)#num)list`; `domain:bool`;
         `center_value:((num#num)#num)#((num#num)#num)`;
         `center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
         `value_bound:((num#num)#num)#((num#num)#num)`;
         `gradient_bounds:
           (((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:
           (((num#num)#num)#((num#num)#num))list`;
         `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
         `center_reciprocal:((num#num)#num)#((num#num)#num)`;
         `box_reciprocal:((num#num)#num)#((num#num)#num)`]
        candle_q_packed_object_item_inverse_analytic_invariant) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_source_item_sqrt_analytic_invariant = prove
 (`!center_boxes outer_boxes radii domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
       center_root center_derivative box_root box_derivative
       box_second_reciprocal.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_interval_sqrt_certificate center_value center_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add center_root center_root) center_derivative /\
     candle_q_interval_sqrt_certificate value_bound box_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add box_root box_root) box_derivative /\
     candle_q_interval_inv_certificate
       (candle_q_interval_mul
         (candle_q_interval_add box_root box_root)
         (candle_q_interval_add value_bound value_bound))
       box_second_reciprocal /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (Candle_q_packed_object_item
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian) center_e box_e)
     ==>
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_packed_object_source_item_sqrt radii center_root
         center_derivative box_root box_derivative box_second_reciprocal
         (Candle_q_packed_object_item
           (Candle_q_packed_object_state domain center_value center_gradient
             value_bound gradient_bounds packed_hessian) center_e box_e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE
      [candle_q_packed_object_source_item_analytic_invariant_def]) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_sqrt_def;
     candle_q_packed_object_source_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_packed_object_interval_list_scale_length];
    MATCH_MP_TAC candle_q_packed_object_gradient_complete6_length THEN
    ASM_REWRITE_TAC[candle_q_packed_object_interval_list_scale_length];
    MATCH_MP_TAC candle_q_packed_object_unary_hessian6_length THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`center_boxes:
           (((num#num)#num)#((num#num)#num))list`;
         `outer_boxes:
           (((num#num)#num)#((num#num)#num))list`;
         `radii:((num#num)#num)list`; `domain:bool`;
         `center_value:((num#num)#num)#((num#num)#num)`;
         `center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
         `value_bound:((num#num)#num)#((num#num)#num)`;
         `gradient_bounds:
           (((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:
           (((num#num)#num)#((num#num)#num))list`;
         `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
         `center_root:((num#num)#num)#((num#num)#num)`;
         `center_derivative:((num#num)#num)#((num#num)#num)`;
         `box_root:((num#num)#num)#((num#num)#num)`;
         `box_derivative:((num#num)#num)#((num#num)#num)`;
         `box_second_reciprocal:((num#num)#num)#((num#num)#num)`]
        candle_q_packed_object_item_sqrt_analytic_invariant) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_source_item_atn_analytic_invariant = prove
 (`!center_boxes outer_boxes radii domain center_value center_gradient
       value_bound gradient_bounds packed_hessian center_e box_e
       center_input center_result center_square center_derivative
       box_input box_square box_derivative box_derivative_square.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_interval_atn_outer_certificate
       center_value center_input center_result /\
     candle_q_interval_square_outer_certificate
       center_value center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator center_square)
       center_derivative /\
     candle_q_interval_square_outer_certificate
       value_bound box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_packed_object_atn_denominator box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square /\
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (Candle_q_packed_object_item
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian) center_e box_e)
     ==>
     candle_q_packed_object_source_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_packed_object_source_item_atn radii center_input
         center_result center_square center_derivative box_input box_square
         box_derivative box_derivative_square
         (Candle_q_packed_object_item
           (Candle_q_packed_object_state domain center_value center_gradient
             value_bound gradient_bounds packed_hessian) center_e box_e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE
      [candle_q_packed_object_source_item_analytic_invariant_def]) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_atn_def;
     candle_q_packed_object_source_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_packed_object_interval_list_scale_length];
    MATCH_MP_TAC candle_q_packed_object_gradient_complete6_length THEN
    ASM_REWRITE_TAC[candle_q_packed_object_interval_list_scale_length];
    MATCH_MP_TAC candle_q_packed_object_unary_hessian6_length THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (SPECL
        [`center_boxes:
           (((num#num)#num)#((num#num)#num))list`;
         `outer_boxes:
           (((num#num)#num)#((num#num)#num))list`;
         `radii:((num#num)#num)list`; `domain:bool`;
         `center_value:((num#num)#num)#((num#num)#num)`;
         `center_gradient:
           (((num#num)#num)#((num#num)#num))list`;
         `value_bound:((num#num)#num)#((num#num)#num)`;
         `gradient_bounds:
           (((num#num)#num)#((num#num)#num))list`;
         `packed_hessian:
           (((num#num)#num)#((num#num)#num))list`;
         `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
         `center_input:((num#num)#num)#((num#num)#num)`;
         `center_result:((num#num)#num)#((num#num)#num)`;
         `center_square:((num#num)#num)#((num#num)#num)`;
         `center_derivative:((num#num)#num)#((num#num)#num)`;
         `box_input:((num#num)#num)#((num#num)#num)`;
         `box_square:((num#num)#num)#((num#num)#num)`;
         `box_derivative:((num#num)#num)#((num#num)#num)`;
         `box_derivative_square:((num#num)#num)#((num#num)#num)`]
        candle_q_packed_object_item_atn_analytic_invariant) THEN
    ASM_REWRITE_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_source_item_constant_analytic_invariant;
     candle_q_packed_object_source_item_variable_analytic_invariant;
     candle_q_packed_object_source_item_neg_analytic_invariant;
     candle_q_packed_object_source_item_add_analytic_invariant;
     candle_q_packed_object_source_item_mul_analytic_invariant;
     candle_q_packed_object_source_item_pi_half_analytic_invariant;
     candle_q_packed_object_source_item_inverse_analytic_invariant;
     candle_q_packed_object_source_item_sqrt_analytic_invariant;
     candle_q_packed_object_source_item_atn_analytic_invariant] then
  failwith "packed object program sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_PROGRAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
