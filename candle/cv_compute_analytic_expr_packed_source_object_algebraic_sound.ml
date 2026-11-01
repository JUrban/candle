(* ========================================================================== *)
(* Direct analytic soundness for algebraic packed object-q source states.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The HOL4 word checker refines its executable *)
(* states to exact object-q states.  This file begins the independent HOL    *)
(* Light half of the bridge: exact source constants are connected directly  *)
(* to the universal analytic invariant, without replaying them through the  *)
(* older decimal fixed-scale evaluator.                                      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_pi_half_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_algebraic_sound = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_jet;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_pi_half_sound;;

let candle_q_packed_object_constant_interval_def = new_definition
 `candle_q_packed_object_constant_interval p n d =
    ((((p,n),d),((p,n),d)):
      ((num#num)#num)#((num#num)#num))`;;

let candle_q_packed_object_constant_interval_contains = prove
 (`!p n d.
     candle_q_interval_contains
       (candle_q_packed_object_constant_interval p n d)
       (candle_q_real ((p,n),d))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_constant_interval_def;
              candle_q_interval_contains_def; FST; SND] THEN
  REAL_ARITH_TAC);;

let candle_q_packed_object_constant_center_contains = prove
 (`!p n d environment.
     candle_q_packed_object_center_first_contains
       (candle_q_packed_object_constant_interval p n d)
       candle_q_packed_object_zero_gradient6
       environment
       (Candle_analytic_poly (Candle_poly_const p n d))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_center_first_contains_def;
              candle_analytic_value_def; candle_analytic_d_def;
              candle_poly_value_list_def; candle_poly_d_list_def] THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC candle_q_packed_object_constant_interval_contains;
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_zero_gradient6_lookup;
                 candle_q_zero_interval_contains]]);;

let candle_q_packed_object_constant_box_contains = prove
 (`!p n d environment.
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         (candle_q_packed_object_constant_interval p n d)
         candle_q_packed_object_zero_gradient6
         candle_q_packed_object_zero_hessian21)
       environment
       (Candle_analytic_poly (Candle_poly_const p n d))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_packed_object_box_jet_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_ACCEPT_TAC candle_q_packed_object_constant_interval_contains;
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_zero_gradient6_lookup;
                 candle_q_zero_interval_contains];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_zero_hessian6_lookup;
                 candle_q_zero_interval_contains]]);;

let candle_q_packed_object_constant_analytic_invariant = prove
 (`!center_boxes outer_boxes p n d.
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes T
       (candle_q_packed_object_constant_interval p n d)
       candle_q_packed_object_zero_gradient6
       (candle_q_packed_object_constant_interval p n d)
       candle_q_packed_object_zero_gradient6
       candle_q_packed_object_zero_hessian21
       (Candle_analytic_poly (Candle_poly_const p n d))
       (Candle_analytic_poly (Candle_poly_const p n d))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def;
              candle_analytic_valid_dim_def;
              candle_poly_valid_dim_def;
              candle_analytic_erase_sqrt_certificates_def] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_q_packed_object_zero_gradient6_length];
    REWRITE_TAC[candle_q_dim_jet_shape_def;
                candle_q_packed_object_box_jet_def;
                candle_q_dim_jet_gradient_def;
                candle_q_dim_jet_hessian_def;
                candle_q_dim_jet_make_def;
                candle_q_dim_interval_matrix_shape_def;
                candle_q_dim_interval_rows_width_all; FST; SND] THEN
    REWRITE_TAC[candle_q_packed_object_zero_gradient6_length;
                candle_q_packed_hessian6_expand_shape];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC
      [candle_analytic_regular_at_def;
       candle_q_packed_object_constant_center_contains];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC
      [candle_analytic_regular_at_def;
       candle_q_packed_object_constant_box_contains]]);;

let candle_q_packed_object_unit_gradient6_def = new_definition
 `candle_q_packed_object_unit_gradient6 variable =
    candle_q_dim_interval_unit_like variable
      candle_q_packed_object_zero_gradient6`;;

let candle_q_packed_object_unit_gradient6_length = prove
 (`!variable. LENGTH (candle_q_packed_object_unit_gradient6 variable) = 6`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_unit_gradient6_def;
              candle_q_dim_interval_unit_like_length;
              candle_q_packed_object_zero_gradient6_length]);;

let candle_q_packed_object_variable_center_contains = prove
 (`!boxes variable environment.
     variable < 6 /\ LENGTH boxes = 6 /\
     candle_q_stack_contains boxes environment
     ==>
     candle_q_packed_object_center_first_contains
       (candle_q_interval_lookup variable boxes)
       (candle_q_packed_object_unit_gradient6 variable)
       environment (Candle_analytic_poly (Candle_poly_var variable))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_center_first_contains_def;
              candle_analytic_value_def; candle_analytic_d_def;
              candle_poly_value_list_def; candle_poly_d_list_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_stack_lookup_contains THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[candle_q_packed_object_unit_gradient6_def] THEN
    ASM_SIMP_TAC[candle_q_dim_interval_unit_like_lookup;
                 candle_q_packed_object_zero_gradient6_length] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[candle_q_one_interval_contains;
                    candle_q_zero_interval_contains]]);;

let candle_q_packed_object_variable_box_contains = prove
 (`!boxes variable environment.
     variable < 6 /\ LENGTH boxes = 6 /\
     candle_q_stack_contains boxes environment
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         (candle_q_interval_lookup variable boxes)
         (candle_q_packed_object_unit_gradient6 variable)
         candle_q_packed_object_zero_hessian21)
       environment (Candle_analytic_poly (Candle_poly_var variable))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_packed_object_box_jet_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_stack_lookup_contains THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[candle_q_packed_object_unit_gradient6_def] THEN
    ASM_SIMP_TAC[candle_q_dim_interval_unit_like_lookup;
                 candle_q_packed_object_zero_gradient6_length] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[candle_q_one_interval_contains;
                    candle_q_zero_interval_contains];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_packed_object_zero_hessian6_lookup;
                 candle_q_zero_interval_contains]]);;

let candle_q_packed_object_variable_analytic_invariant = prove
 (`!center_boxes outer_boxes variable.
     variable < 6 /\
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes T
       (candle_q_interval_lookup variable center_boxes)
       (candle_q_packed_object_unit_gradient6 variable)
       (candle_q_interval_lookup variable outer_boxes)
       (candle_q_packed_object_unit_gradient6 variable)
       candle_q_packed_object_zero_hessian21
       (Candle_analytic_poly (Candle_poly_var variable))
       (Candle_analytic_poly (Candle_poly_var variable))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def;
              candle_analytic_valid_dim_def;
              candle_poly_valid_dim_def;
              candle_analytic_erase_sqrt_certificates_def] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_q_packed_object_unit_gradient6_length];
    REWRITE_TAC[candle_q_dim_jet_shape_def;
                candle_q_packed_object_box_jet_def;
                candle_q_dim_jet_gradient_def;
                candle_q_dim_jet_hessian_def;
                candle_q_dim_jet_make_def;
                candle_q_dim_interval_matrix_shape_def;
                candle_q_dim_interval_rows_width_all; FST; SND] THEN
    REWRITE_TAC[candle_q_packed_object_unit_gradient6_length;
                candle_q_packed_hessian6_expand_shape];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC
      [candle_analytic_regular_at_def;
       candle_q_packed_object_variable_center_contains];
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC
      [candle_analytic_regular_at_def;
       candle_q_packed_object_variable_box_contains]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_constant_interval_contains;
     candle_q_packed_object_constant_center_contains;
     candle_q_packed_object_constant_box_contains;
     candle_q_packed_object_constant_analytic_invariant;
     candle_q_packed_object_unit_gradient6_length;
     candle_q_packed_object_variable_center_contains;
     candle_q_packed_object_variable_box_contains;
     candle_q_packed_object_variable_analytic_invariant] then
  failwith "packed source object algebraic sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_ALGEBRAIC_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
