(* ========================================================================== *)
(* Soundness substrate for the fixed-scale post-nonlinear addition tail.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file first authenticates the executable  *)
(* rational-to-fixed conversion and records its outward-widening semantics.   *)
(* The mixed postfix-program invariant is layered on these representation     *)
(* facts rather than trusting the benchmark implementation.                   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compute.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_sound = struct

open Multivariate_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_polynomial_expr_dim_first_jet_representation;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;

let candle_fsa_interval_matrix_of_q_def =
  new_recursive_definition list_RECURSION
   `(candle_fsa_interval_matrix_of_q
       ([]:((((num#num)#num)#((num#num)#num))list)list) = []) /\
    (candle_fsa_interval_matrix_of_q (CONS h t) =
       CONS (candle_fs_interval_list_of_q h)
         (candle_fsa_interval_matrix_of_q t))`;;

let candle_fsa_result_of_q_def = new_definition
 `candle_fsa_result_of_q result =
    candle_fs_result_make
      (candle_q_dim_taylor_model_result_domain result)
      (candle_fs_first_make
        (candle_fs_interval_of_q
          (candle_q_dim_jet_f
            (candle_q_dim_taylor_model_result_center result)))
        (candle_fs_interval_list_of_q
          (candle_q_dim_jet_gradient
            (candle_q_dim_taylor_model_result_center result))))
      (candle_fs_interval_of_q
        (candle_q_dim_taylor_model_result_value_bound result))
      (candle_fs_interval_list_of_q
        (candle_q_dim_taylor_model_result_gradient_bounds result))
      (candle_fsa_interval_matrix_of_q
        (candle_q_dim_taylor_model_result_hessian result))`;;

let candle_cv_fsa_interval_matrix_of_q_correct = prove
 (`!row_lists.
     candle_cv_fsa_interval_matrix_of_q
       (candle_cv_q_interval_matrix row_lists) =
     candle_cv_fs_interval_matrix
       (candle_fsa_interval_matrix_of_q row_lists)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_fsa_interval_matrix_of_q_def;
                  candle_fsa_interval_matrix_of_q_def;
                  candle_cv_q_interval_matrix_def;
                  candle_cv_fs_interval_matrix_def;
                  candle_cv_fs_interval_list_of_q_correct]);;

let candle_cv_fsa_result_of_q_correct = prove
 (`!result.
     candle_cv_fsa_result_of_q
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_fs_result (candle_fsa_result_of_q result)`,
  REWRITE_TAC[candle_cv_fsa_result_of_q_def;
              candle_fsa_result_of_q_def;
              candle_cv_q_dim_taylor_model_result_domain_correct;
              candle_cv_q_dim_taylor_model_result_center_correct;
              candle_cv_q_dim_taylor_model_result_value_bound_correct;
              candle_cv_q_dim_taylor_model_result_gradient_bounds_correct;
              candle_cv_q_dim_taylor_model_result_hessian_correct;
              candle_cv_q_dim_first_jet_f_correct;
              candle_cv_q_dim_first_jet_gradient_correct;
              candle_cv_fs_interval_of_q_correct;
              candle_cv_fs_interval_list_of_q_correct;
              candle_cv_fsa_interval_matrix_of_q_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_result_make_correct]);;

let candle_fsa_interval_matrix_of_q_length = prove
 (`!row_lists.
     LENGTH (candle_fsa_interval_matrix_of_q row_lists) = LENGTH row_lists`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fsa_interval_matrix_of_q_def; LENGTH]);;

let candle_fsa_interval_matrix_of_q_rows_width = prove
 (`!n row_lists.
     ALL (\row. LENGTH row = n)
       (candle_fsa_interval_matrix_of_q row_lists) <=>
     ALL (\row. LENGTH row = n) row_lists`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fsa_interval_matrix_of_q_def; ALL;
                  candle_fs_interval_list_of_q_length]);;

let candle_fsa_interval_matrix_of_q_map = prove
 (`!row_lists.
     candle_fsa_interval_matrix_of_q row_lists =
     MAP candle_fs_interval_list_of_q row_lists`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_fsa_interval_matrix_of_q_def; MAP]);;

let candle_fsa_interval_matrix_of_q_contains = prove
 (`!row_lists values.
     ALL2 candle_q_stack_contains row_lists values
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fsa_interval_matrix_of_q row_lists) values`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC (ISPEC `values:(real list)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_fsa_interval_matrix_of_q_def; ALL2];
    POP_ASSUM (LABEL_TAC "matrix_ih") THEN
    GEN_TAC THEN
    MP_TAC (ISPEC `values:(real list)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_fsa_interval_matrix_of_q_def; ALL2] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC candle_fs_interval_list_of_q_contains THEN
      ASM_REWRITE_TAC[];
      USE_THEN "matrix_ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let candle_fsa_interval_roundtrip_contains = prove
 (`!interval x.
     candle_q_interval_contains interval x
     ==>
     candle_q_interval_contains
       (candle_fs_interval_to_q (candle_fs_interval_of_q interval)) x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_interval_to_q_contains] THEN
  MATCH_MP_TAC candle_fs_interval_of_q_sound THEN ASM_REWRITE_TAC[]);;

let candle_fsa_interval_list_roundtrip_length = prove
 (`!intervals.
     LENGTH
       (candle_fs_interval_list_to_q
         (candle_fs_interval_list_of_q intervals)) =
     LENGTH intervals`,
  REWRITE_TAC[candle_fs_interval_list_to_q_length;
              candle_fs_interval_list_of_q_length]);;

let candle_fsa_interval_list_roundtrip_contains = prove
 (`!intervals values.
     candle_q_stack_contains intervals values
     ==>
     candle_q_stack_contains
       (candle_fs_interval_list_to_q
         (candle_fs_interval_list_of_q intervals)) values`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_interval_list_to_q_contains] THEN
  MATCH_MP_TAC candle_fs_interval_list_of_q_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fsa_interval_matrix_roundtrip_shape = prove
 (`!n row_lists.
     candle_q_dim_interval_matrix_shape n row_lists
     ==>
     candle_q_dim_interval_matrix_shape n
       (candle_fs_interval_matrix_to_q
         (candle_fsa_interval_matrix_of_q row_lists))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_all;
              candle_fs_interval_matrix_to_q_length;
              candle_fs_interval_matrix_to_q_rows_width;
              candle_fsa_interval_matrix_of_q_length;
              candle_fsa_interval_matrix_of_q_rows_width] THEN
  MESON_TAC[]);;

let candle_fsa_interval_matrix_roundtrip_contains = prove
 (`!row_lists values.
     ALL2 candle_q_stack_contains row_lists values
     ==>
     ALL2 candle_q_stack_contains
       (candle_fs_interval_matrix_to_q
         (candle_fsa_interval_matrix_of_q row_lists)) values`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_interval_matrix_to_q_contains] THEN
  MATCH_MP_TAC candle_fsa_interval_matrix_of_q_contains THEN
  ASM_REWRITE_TAC[]);;

let candle_fsa_jet_of_q_def = new_definition
 `candle_fsa_jet_of_q first hessian =
    candle_q_dim_jet_make
      (candle_fs_interval_to_q
        (candle_fs_interval_of_q (candle_q_dim_jet_f first)))
      (candle_fs_interval_list_to_q
        (candle_fs_interval_list_of_q
          (candle_q_dim_jet_gradient first)))
      (candle_fs_interval_matrix_to_q
        (candle_fsa_interval_matrix_of_q hessian))`;;

let candle_fsa_jet_of_q_shape = prove
 (`!n first hessian.
     candle_q_dim_jet_shape n first /\
     candle_q_dim_interval_matrix_shape n hessian
     ==>
     candle_q_dim_jet_shape n (candle_fsa_jet_of_q first hessian)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_fsa_jet_of_q_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_fsa_interval_list_roundtrip_length; FST; SND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_fsa_interval_matrix_roundtrip_shape THEN
  ASM_REWRITE_TAC[]);;

let candle_fsa_jet_of_q_f_contains = prove
 (`!first hessian_source value.
     candle_q_interval_contains (candle_q_dim_jet_f first) value
     ==>
     candle_q_interval_contains
       (candle_q_dim_jet_f
         (candle_fsa_jet_of_q first hessian_source)) value`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_jet_of_q_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_fsa_interval_roundtrip_contains);;

let candle_fsa_jet_of_q_gradient_contains = prove
 (`!first hessian_source values.
     candle_q_stack_contains (candle_q_dim_jet_gradient first) values
     ==>
     candle_q_stack_contains
       (candle_q_dim_jet_gradient
         (candle_fsa_jet_of_q first hessian_source)) values`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_jet_of_q_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_gradient_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_fsa_interval_list_roundtrip_contains);;

let candle_fsa_jet_of_q_hessian_contains = prove
 (`!first hessian_source values.
     ALL2 candle_q_stack_contains hessian_source values
     ==>
     ALL2 candle_q_stack_contains
       (candle_q_dim_jet_hessian
         (candle_fsa_jet_of_q first hessian_source)) values`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsa_jet_of_q_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_hessian_def; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_fsa_interval_matrix_roundtrip_contains);;

let candle_fsa_jet_of_q_contains_components = prove
 (`!n first hessian_source value gradient hessian.
     candle_q_dim_jet_shape n first /\
     candle_q_dim_jet_shape n hessian_source /\
     candle_q_dim_jet_contains_components
       n first value gradient hessian /\
     candle_q_dim_jet_contains_components
       n hessian_source value gradient hessian
     ==>
     candle_q_dim_jet_contains_components n
       (candle_fsa_jet_of_q first
         (candle_q_dim_jet_hessian hessian_source))
       value gradient hessian`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let first_shape = ASSUME `candle_q_dim_jet_shape n first` in
  let source_shape = ASSUME
    `candle_q_dim_jet_shape n hessian_source` in
  let first_contains = ASSUME
    `candle_q_dim_jet_contains_components
      n first value gradient hessian` in
  let source_contains = ASSUME
    `candle_q_dim_jet_contains_components
      n hessian_source value gradient hessian` in
  let source_matrix_shape = CONJUNCT2
    (REWRITE_RULE[candle_q_dim_jet_shape_def] source_shape) in
  let result_shape = MATCH_MP candle_fsa_jet_of_q_shape
    (CONJ first_shape source_matrix_shape) in
  let result_value = MATCH_MP candle_fsa_jet_of_q_f_contains
    (CONJUNCT1
      (REWRITE_RULE[candle_q_dim_jet_contains_components_def]
        first_contains)) in
  let result_gradient = MATCH_MP candle_fsa_jet_of_q_gradient_contains
    (MATCH_MP candle_q_dim_jet_components_gradient_contains
      (CONJ first_shape first_contains)) in
  let result_hessian = MATCH_MP candle_fsa_jet_of_q_hessian_contains
    (MATCH_MP candle_q_dim_jet_components_hessian_contains
      (CONJ source_shape source_contains)) in
  MATCH_MP_TAC candle_q_dim_jet_contains_components_of_stacks THEN
  REPEAT CONJ_TAC THENL
   [MATCH_ACCEPT_TAC result_shape;
    MATCH_ACCEPT_TAC result_value;
    MATCH_ACCEPT_TAC result_gradient;
    MATCH_ACCEPT_TAC result_hessian]);;

let candle_fsa_result_of_q_domain = prove
 (`!result.
     candle_fs_result_domain (candle_fsa_result_of_q result) =
     candle_q_dim_taylor_model_result_domain result`,
  REWRITE_TAC[candle_fsa_result_of_q_def;
              candle_fs_result_domain_def;
              candle_fs_result_make_def; FST; SND]);;

let candle_fsa_result_of_q_domain_roundtrip = prove
 (`!result.
     candle_q_dim_taylor_model_result_domain
       (candle_fs_result_to_q (candle_fsa_result_of_q result)) =
     candle_q_dim_taylor_model_result_domain result`,
  REWRITE_TAC[candle_fs_result_to_q_def;
              candle_q_dim_taylor_model_result_domain_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_fsa_result_of_q_domain; FST; SND]);;

let candle_q_dim_taylor_model_proxy_hessian = prove
 (`!result.
     candle_q_dim_jet_hessian
       (candle_q_dim_taylor_model_proxy result) =
     candle_q_dim_taylor_model_result_hessian result`,
  REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND]);;

let candle_fsa_result_of_q_center = prove
 (`!result.
     candle_q_dim_taylor_model_result_center
       (candle_fs_result_to_q (candle_fsa_result_of_q result)) =
     candle_fsa_jet_of_q
       (candle_q_dim_taylor_model_result_center result)
       (candle_q_dim_taylor_model_result_hessian result)`,
  REWRITE_TAC[candle_fs_result_to_q_def;
              candle_fsa_result_of_q_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_fs_result_center_def;
              candle_fs_result_hessian_def;
              candle_fs_result_make_def;
              candle_fs_first_to_q_def;
              candle_fs_first_value_def;
              candle_fs_first_gradient_def;
              candle_fs_first_make_def;
              candle_fsa_jet_of_q_def; FST; SND]);;

let candle_fsa_result_of_q_proxy = prove
 (`!result.
     candle_q_dim_taylor_model_proxy
       (candle_fs_result_to_q (candle_fsa_result_of_q result)) =
     candle_fsa_jet_of_q
       (candle_q_dim_taylor_model_proxy result)
       (candle_q_dim_taylor_model_result_hessian result)`,
  REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
              candle_fs_result_to_q_def;
              candle_fsa_result_of_q_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_q_dim_taylor_model_result_value_bound_def;
              candle_q_dim_taylor_model_result_gradient_bounds_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_fs_result_value_bound_def;
              candle_fs_result_gradient_bounds_def;
              candle_fs_result_hessian_def;
              candle_fs_result_make_def;
              candle_fsa_jet_of_q_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def; FST; SND]);;

end;;
