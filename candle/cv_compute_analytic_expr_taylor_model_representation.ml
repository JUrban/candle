(* ========================================================================== *)
(* Ordinary-HOL representation of centered reflected Taylor-model results.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The executable result caches a rounded center *)
(* first jet plus whole-box value, gradient, and Hessian enclosures.  This   *)
(* file gives that tuple an ordinary HOL representation and proves the       *)
(* structural cval correspondence used by the later semantic invariant.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_representation = struct

open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_representation;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_first_jet_program_compute;;
open Candle_cv_exact_rational_normalize_extended;;
open Candle_cv_analytic_expr_extended_taylor;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_sound;;

(* The ordinary result has the same nesting as its cval representation:      *)
(*   (domain,(center-first-jet,(value,(gradient,Hessian)))).                  *)

let candle_q_dim_taylor_model_result_make_def = new_definition
 `candle_q_dim_taylor_model_result_make
      domain center_first value_bound gradient_bounds hessian =
    (domain,(center_first,(value_bound,(gradient_bounds,hessian))))`;;

let candle_q_dim_taylor_model_result_domain_def = new_definition
 `candle_q_dim_taylor_model_result_domain result = FST result`;;

let candle_q_dim_taylor_model_result_center_def = new_definition
 `candle_q_dim_taylor_model_result_center result = FST (SND result)`;;

let candle_q_dim_taylor_model_result_value_bound_def = new_definition
 `candle_q_dim_taylor_model_result_value_bound result =
    FST (SND (SND result))`;;

let candle_q_dim_taylor_model_result_gradient_bounds_def = new_definition
 `candle_q_dim_taylor_model_result_gradient_bounds result =
    FST (SND (SND (SND result)))`;;

let candle_q_dim_taylor_model_result_hessian_def = new_definition
 `candle_q_dim_taylor_model_result_hessian result =
    SND (SND (SND (SND result)))`;;

let candle_cv_q_dim_taylor_model_result_encode_def = new_definition
 `candle_cv_q_dim_taylor_model_result_encode result =
    candle_cv_q_dim_taylor_model_result_make
      (candle_cv_bool (candle_q_dim_taylor_model_result_domain result))
      (candle_cv_q_dim_first_jet_encode
        (candle_q_dim_taylor_model_result_center result))
      (candle_cv_q_interval
        (candle_q_dim_taylor_model_result_value_bound result))
      (candle_cv_q_interval_list
        (candle_q_dim_taylor_model_result_gradient_bounds result))
      (candle_cv_q_interval_matrix
        (candle_q_dim_taylor_model_result_hessian result))`;;

let candle_cv_q_dim_taylor_model_result_make_correct = prove
 (`!domain center_first value_bound gradient_bounds hessian.
     candle_cv_q_dim_taylor_model_result_make
       (candle_cv_bool domain)
       (candle_cv_q_dim_first_jet_encode center_first)
       (candle_cv_q_interval value_bound)
       (candle_cv_q_interval_list gradient_bounds)
       (candle_cv_q_interval_matrix hessian) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_make domain center_first
         value_bound gradient_bounds hessian)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_encode_def;
              candle_cv_q_dim_taylor_model_result_make_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_q_dim_taylor_model_result_domain_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_value_bound_def;
              candle_q_dim_taylor_model_result_gradient_bounds_def;
              candle_q_dim_taylor_model_result_hessian_def; FST; SND]);;

let candle_cv_q_dim_taylor_model_result_domain_correct = prove
 (`!result.
     candle_cv_q_dim_taylor_model_result_domain
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_bool (candle_q_dim_taylor_model_result_domain result)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_domain_def;
              candle_cv_q_dim_taylor_model_result_encode_def;
              candle_cv_q_dim_taylor_model_result_make_def;
              cexp_fst_def]);;

let candle_cv_q_dim_taylor_model_result_center_correct = prove
 (`!result.
     candle_cv_q_dim_taylor_model_result_center
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_taylor_model_result_center result)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_center_def;
              candle_cv_q_dim_taylor_model_result_encode_def;
              candle_cv_q_dim_taylor_model_result_make_def;
              cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_taylor_model_result_value_bound_correct = prove
 (`!result.
     candle_cv_q_dim_taylor_model_result_value_bound
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_interval
       (candle_q_dim_taylor_model_result_value_bound result)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_value_bound_def;
              candle_cv_q_dim_taylor_model_result_encode_def;
              candle_cv_q_dim_taylor_model_result_make_def;
              cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_taylor_model_result_gradient_bounds_correct = prove
 (`!result.
     candle_cv_q_dim_taylor_model_result_gradient_bounds
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_interval_list
       (candle_q_dim_taylor_model_result_gradient_bounds result)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_gradient_bounds_def;
              candle_cv_q_dim_taylor_model_result_encode_def;
              candle_cv_q_dim_taylor_model_result_make_def;
              cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_taylor_model_result_hessian_correct = prove
 (`!result.
     candle_cv_q_dim_taylor_model_result_hessian
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_interval_matrix
       (candle_q_dim_taylor_model_result_hessian result)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_hessian_def;
              candle_cv_q_dim_taylor_model_result_encode_def;
              candle_cv_q_dim_taylor_model_result_make_def;
              cexp_snd_def]);;

(* The first-jet encoder deliberately erases the ordinary Hessian.  Keeping  *)
(* it unchanged here lets the semantic layer state one full-jet containment  *)
(* invariant while proving that the executable value/gradient projection is  *)
(* exactly the rounded projection of that ordinary jet.                      *)

let candle_q_dim_first_jet_fixed_round_def = new_definition
 `candle_q_dim_first_jet_fixed_round jet =
    candle_q_dim_jet_make
      (candle_q_fixed_interval_round (candle_q_dim_jet_f jet))
      (candle_q_fixed_interval_list_round
        (candle_q_dim_jet_gradient jet))
      (candle_q_dim_jet_hessian jet)`;;

let candle_cv_q_dim_first_jet_fixed_round_correct = prove
 (`!jet.
     candle_cv_q_dim_first_jet_fixed_round
       (candle_cv_q_dim_first_jet_encode jet) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_first_jet_fixed_round jet)`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_fixed_round_def;
              candle_cv_q_dim_first_jet_f_correct;
              candle_cv_q_dim_first_jet_gradient_correct;
              candle_cv_q_fixed_interval_round_correct;
              candle_cv_q_fixed_interval_list_round_correct;
              candle_cv_q_dim_first_jet_encode_def;
              candle_cv_q_dim_first_jet_make_def;
              candle_q_dim_first_jet_fixed_round_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def; FST; SND]);;

let candle_q_fixed_interval_list_round_length = prove
 (`!items. LENGTH (candle_q_fixed_interval_list_round items) = LENGTH items`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_interval_list_round_def; LENGTH]);;

let candle_q_fixed_interval_list_round_lookup = prove
 (`!items i. i < LENGTH items
     ==> candle_q_interval_lookup i
           (candle_q_fixed_interval_list_round items) =
         candle_q_fixed_interval_round
           (candle_q_interval_lookup i items)`,
  LIST_INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_fixed_interval_list_round_def;
                  candle_q_interval_lookup_def; LENGTH; LT_SUC; LT]);;

let candle_q_dim_first_jet_fixed_round_shape = prove
 (`!n jet. candle_q_dim_jet_shape n jet
           ==> candle_q_dim_jet_shape n
                 (candle_q_dim_first_jet_fixed_round jet)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_first_jet_fixed_round_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_fixed_interval_list_round_length; FST; SND]);;

let candle_q_dim_first_jet_fixed_round_contains_components = prove
 (`!n jet value gradient hessian.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_jet_contains_components n jet value gradient hessian
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_first_jet_fixed_round jet)
           value gradient hessian`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_dim_first_jet_fixed_round_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_hessian_at_def; FST; SND] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_fixed_interval_round_contains THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_q_fixed_interval_list_round_lookup] THEN
    MATCH_MP_TAC candle_q_fixed_interval_round_contains THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* Ordinary counterparts of the cached centered-Taylor reconstruction. *)

let candle_q_interval_add_extended_def = new_definition
 `candle_q_interval_add_extended x y =
    (candle_q_add_normalized_extended (FST x) (FST y),
     candle_q_add_normalized_extended (SND x) (SND y))`;;

let candle_q_symmetric_interval_def = new_definition
 `candle_q_symmetric_interval radius =
    (candle_q_neg radius,radius)`;;

let candle_cv_q_interval_add_extended_correct = prove
 (`!x y.
     candle_cv_q_interval_add_extended
       (candle_cv_q_interval x) (candle_cv_q_interval y) =
     candle_cv_q_interval (candle_q_interval_add_extended x y)`,
  REWRITE_TAC[candle_cv_q_interval_add_extended_def;
              candle_q_interval_add_extended_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_add_normalized_extended_correct; FST; SND]);;

let candle_cv_q_symmetric_interval_correct = prove
 (`!radius.
     candle_cv_q_symmetric_interval (candle_cv_q radius) =
     candle_cv_q_interval (candle_q_symmetric_interval radius)`,
  REWRITE_TAC[candle_cv_q_symmetric_interval_def;
              candle_q_symmetric_interval_def;
              candle_cv_q_interval_def; candle_cv_q_neg_correct;
              FST; SND]);;

let candle_q_dim_taylor_model_error_def = new_definition
 `candle_q_dim_taylor_model_error radii center_first hessian =
    candle_q_add_normalized_extended
      (candle_q_dot_abs_upper_extended radii
        (candle_q_dim_jet_gradient center_first))
      (candle_q_mul_normalized_extended candle_q_half
        (candle_q_weighted_rows_abs_upper_extended radii radii hessian))`;;

let candle_q_dim_taylor_model_value_bound_def = new_definition
 `candle_q_dim_taylor_model_value_bound radii center_first hessian =
    candle_q_interval_add_extended
      (candle_q_dim_jet_f center_first)
      (candle_q_symmetric_interval
        (candle_q_dim_taylor_model_error radii center_first hessian))`;;

let candle_q_dim_taylor_model_gradient_bounds_def = define
 `(candle_q_dim_taylor_model_gradient_bounds radii [] row_lists = []) /\
  (candle_q_dim_taylor_model_gradient_bounds
     radii (CONS gradient_interval gradient_tail) [] = []) /\
  (candle_q_dim_taylor_model_gradient_bounds
     radii (CONS gradient_interval gradient_tail)
       (CONS interval_row row_tail) =
     CONS
       (candle_q_interval_add_extended gradient_interval
         (candle_q_symmetric_interval
           (candle_q_dot_abs_upper_extended radii interval_row)))
       (candle_q_dim_taylor_model_gradient_bounds
         radii gradient_tail row_tail))`;;

let candle_cv_q_dim_taylor_model_error_correct = prove
 (`!radii center_first hessian.
     candle_cv_q_dim_taylor_model_error
       (candle_cv_q_list radii)
       (candle_cv_q_dim_first_jet_encode center_first)
       (candle_cv_q_interval_matrix hessian) =
     candle_cv_q
       (candle_q_dim_taylor_model_error radii center_first hessian)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_error_def;
              candle_q_dim_taylor_model_error_def;
              candle_cv_q_dim_first_jet_gradient_correct;
              candle_cv_q_dot_abs_upper_extended_correct;
              candle_cv_q_weighted_rows_abs_upper_extended_correct;
              candle_cv_q_half_def;
              candle_cv_q_mul_normalized_extended_correct;
              candle_cv_q_add_normalized_extended_correct]);;

let candle_cv_q_dim_taylor_model_value_bound_correct = prove
 (`!radii center_first hessian.
     candle_cv_q_dim_taylor_model_value_bound
       (candle_cv_q_list radii)
       (candle_cv_q_dim_first_jet_encode center_first)
       (candle_cv_q_interval_matrix hessian) =
     candle_cv_q_interval
       (candle_q_dim_taylor_model_value_bound
         radii center_first hessian)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_value_bound_def;
              candle_q_dim_taylor_model_value_bound_def;
              candle_cv_q_dim_first_jet_f_correct;
              candle_cv_q_dim_taylor_model_error_correct;
              candle_cv_q_symmetric_interval_correct;
              candle_cv_q_interval_add_extended_correct]);;

let candle_cv_q_dim_taylor_model_gradient_bounds_correct = prove
 (`!radii gradient_intervals row_lists.
     candle_cv_q_dim_taylor_model_gradient_bounds
       (candle_cv_q_list radii)
       (candle_cv_q_interval_list gradient_intervals)
       (candle_cv_q_interval_matrix row_lists) =
     candle_cv_q_interval_list
       (candle_q_dim_taylor_model_gradient_bounds
         radii gradient_intervals row_lists)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN
    REWRITE_TAC[candle_cv_q_interval_list_def;
                candle_cv_q_interval_matrix_def;
                candle_cv_q_dim_taylor_model_gradient_bounds_def;
                candle_q_dim_taylor_model_gradient_bounds_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_q_interval_list_def;
                    candle_cv_q_interval_matrix_def;
                    candle_cv_q_dim_taylor_model_gradient_bounds_def;
                    candle_q_dim_taylor_model_gradient_bounds_def;
                    candle_cv_q_dot_abs_upper_extended_correct;
                    candle_cv_q_symmetric_interval_correct;
                    candle_cv_q_interval_add_extended_correct]]);;

let candle_q_dim_taylor_model_result_complete_rounded_def = new_definition
 `candle_q_dim_taylor_model_result_complete_rounded
      radii domain center_first hessian =
    candle_q_dim_taylor_model_result_make domain center_first
      (candle_q_fixed_interval_round
        (candle_q_dim_taylor_model_value_bound
          radii center_first hessian))
      (candle_q_fixed_interval_list_round
        (candle_q_dim_taylor_model_gradient_bounds radii
          (candle_q_dim_jet_gradient center_first) hessian))
      hessian`;;

let candle_q_dim_taylor_model_result_complete_def = new_definition
 `candle_q_dim_taylor_model_result_complete
      radii domain center_first hessian =
    candle_q_dim_taylor_model_result_complete_rounded radii domain
      (candle_q_dim_first_jet_fixed_round center_first)
      (candle_q_fixed_interval_matrix_round hessian)`;;

let candle_cv_q_dim_taylor_model_result_complete_rounded_correct = prove
 (`!radii domain center_first hessian.
     candle_cv_q_dim_taylor_model_result_complete_rounded
       (candle_cv_q_list radii) (candle_cv_bool domain)
       (candle_cv_q_dim_first_jet_encode center_first)
       (candle_cv_q_interval_matrix hessian) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_complete_rounded
         radii domain center_first hessian)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_complete_rounded_def;
              candle_q_dim_taylor_model_result_complete_rounded_def;
              candle_cv_q_dim_taylor_model_value_bound_correct;
              candle_cv_q_fixed_interval_round_correct;
              candle_cv_q_dim_first_jet_gradient_correct;
              candle_cv_q_dim_taylor_model_gradient_bounds_correct;
              candle_cv_q_fixed_interval_list_round_correct;
              candle_cv_q_dim_taylor_model_result_make_correct]);;

let candle_cv_q_dim_taylor_model_result_complete_correct = prove
 (`!radii domain center_first hessian.
     candle_cv_q_dim_taylor_model_result_complete
       (candle_cv_q_list radii) (candle_cv_bool domain)
       (candle_cv_q_dim_first_jet_encode center_first)
       (candle_cv_q_interval_matrix hessian) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_complete
         radii domain center_first hessian)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_complete_def;
              candle_q_dim_taylor_model_result_complete_def;
              candle_cv_q_dim_first_jet_fixed_round_correct;
              candle_cv_q_fixed_interval_matrix_round_correct;
              candle_cv_q_dim_taylor_model_result_complete_rounded_correct]);;

let candle_q_dim_taylor_model_proxy_def = new_definition
 `candle_q_dim_taylor_model_proxy result =
    candle_q_dim_jet_make
      (candle_q_dim_taylor_model_result_value_bound result)
      (candle_q_dim_taylor_model_result_gradient_bounds result)
      (candle_q_dim_taylor_model_result_hessian result)`;;

let candle_cv_q_dim_taylor_model_proxy_correct = prove
 (`!result.
     candle_cv_q_dim_taylor_model_proxy
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_taylor_model_proxy result)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_proxy_def;
              candle_q_dim_taylor_model_proxy_def;
              candle_cv_q_dim_taylor_model_result_value_bound_correct;
              candle_cv_q_dim_taylor_model_result_gradient_bounds_correct;
              candle_cv_q_dim_taylor_model_result_hessian_correct;
              candle_cv_q_dim_jet_make_correct]);;

let candle_q_dim_taylor_model_result_neg_def = new_definition
 `candle_q_dim_taylor_model_result_neg radii result =
    candle_q_dim_taylor_model_result_complete radii
      (candle_q_dim_taylor_model_result_domain result)
      (candle_q_dim_jet_normalized_neg
        (candle_q_dim_taylor_model_result_center result))
      (candle_q_dim_interval_matrix_neg
        (candle_q_dim_taylor_model_result_hessian result))`;;

let candle_q_dim_taylor_model_result_add_def = new_definition
 `candle_q_dim_taylor_model_result_add radii left right =
    candle_q_dim_taylor_model_result_complete radii
      (candle_q_dim_taylor_model_result_domain left /\
       candle_q_dim_taylor_model_result_domain right)
      (candle_q_dim_jet_normalized_add
        (candle_q_dim_taylor_model_result_center left)
        (candle_q_dim_taylor_model_result_center right))
      (candle_q_dim_interval_matrix_add_normalized
        (candle_q_dim_taylor_model_result_hessian left)
        (candle_q_dim_taylor_model_result_hessian right))`;;

let candle_q_dim_taylor_model_result_mul_def = new_definition
 `candle_q_dim_taylor_model_result_mul radii left right =
    candle_q_dim_taylor_model_result_complete radii
      (candle_q_dim_taylor_model_result_domain left /\
       candle_q_dim_taylor_model_result_domain right)
      (candle_q_dim_jet_normalized_mul
        (candle_q_dim_taylor_model_result_center left)
        (candle_q_dim_taylor_model_result_center right))
      (candle_q_dim_jet_hessian
        (candle_q_dim_jet_normalized_mul
          (candle_q_dim_taylor_model_proxy left)
          (candle_q_dim_taylor_model_proxy right)))`;;

let candle_q_dim_taylor_model_result_square_def = new_definition
 `candle_q_dim_taylor_model_result_square radii result =
    candle_q_dim_taylor_model_result_mul radii result result`;;

let candle_cv_q_dim_taylor_model_result_neg_correct = prove
 (`!radii result.
     candle_cv_q_dim_taylor_model_result_neg
       (candle_cv_q_list radii)
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_neg radii result)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_neg_def;
              candle_q_dim_taylor_model_result_neg_def;
              candle_cv_q_dim_taylor_model_result_domain_correct;
              candle_cv_q_dim_taylor_model_result_center_correct;
              candle_cv_q_dim_first_jet_neg_correct;
              candle_cv_q_dim_taylor_model_result_hessian_correct;
              candle_cv_q_dim_interval_matrix_neg_correct;
              candle_cv_q_dim_taylor_model_result_complete_correct]);;

let candle_cv_q_dim_taylor_model_result_add_correct = prove
 (`!radii left right.
     candle_cv_q_dim_taylor_model_result_add
       (candle_cv_q_list radii)
       (candle_cv_q_dim_taylor_model_result_encode left)
       (candle_cv_q_dim_taylor_model_result_encode right) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_add radii left right)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_add_def;
              candle_q_dim_taylor_model_result_add_def;
              candle_cv_q_dim_taylor_model_result_domain_correct;
              candle_cv_bool_and_correct;
              candle_cv_q_dim_taylor_model_result_center_correct;
              candle_cv_q_dim_first_jet_add_correct;
              candle_cv_q_dim_taylor_model_result_hessian_correct;
              candle_cv_q_dim_interval_matrix_add_correct;
              candle_cv_q_dim_taylor_model_result_complete_correct]);;

let candle_cv_q_dim_taylor_model_result_mul_correct = prove
 (`!radii left right.
     candle_cv_q_dim_taylor_model_result_mul
       (candle_cv_q_list radii)
       (candle_cv_q_dim_taylor_model_result_encode left)
       (candle_cv_q_dim_taylor_model_result_encode right) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_mul radii left right)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_mul_def;
              candle_q_dim_taylor_model_result_mul_def;
              candle_cv_q_dim_taylor_model_result_domain_correct;
              candle_cv_bool_and_correct;
              candle_cv_q_dim_taylor_model_result_center_correct;
              candle_cv_q_dim_first_jet_mul_correct;
              candle_cv_q_dim_taylor_model_proxy_correct;
              candle_cv_q_dim_jet_mul_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_dim_taylor_model_result_complete_correct]);;

let candle_cv_q_dim_taylor_model_result_square_correct = prove
 (`!radii result.
     candle_cv_q_dim_taylor_model_result_square
       (candle_cv_q_list radii)
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_square radii result)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_square_def;
              candle_q_dim_taylor_model_result_square_def;
              candle_cv_q_dim_taylor_model_result_mul_correct]);;

(* Ordinary stack structure and the remaining analytic result constructors. *)

let candle_q_dim_taylor_model_result_default_def = new_definition
 `candle_q_dim_taylor_model_result_default center_boxes boxes =
    candle_q_dim_taylor_model_result_make F
      (candle_q_dim_jet_normalized_zero center_boxes)
      candle_q_zero_interval
      (candle_q_dim_interval_zeros_like boxes)
      (candle_q_dim_interval_zero_matrix_like boxes boxes)`;;

let candle_q_dim_taylor_model_result_head_def = define
 `(candle_q_dim_taylor_model_result_head center_boxes boxes [] =
     candle_q_dim_taylor_model_result_default center_boxes boxes) /\
  (candle_q_dim_taylor_model_result_head center_boxes boxes (CONS h t) = h)`;;

let candle_q_dim_taylor_model_result_tail_def = define
 `(candle_q_dim_taylor_model_result_tail [] = []) /\
  (candle_q_dim_taylor_model_result_tail (CONS h t) = t)`;;

let candle_cv_q_dim_taylor_model_result_list_encode_def = define
 `(candle_cv_q_dim_taylor_model_result_list_encode [] = Cexp_num 0) /\
  (candle_cv_q_dim_taylor_model_result_list_encode (CONS h t) =
     Cexp_pair (candle_cv_q_dim_taylor_model_result_encode h)
       (candle_cv_q_dim_taylor_model_result_list_encode t))`;;

let candle_cv_q_zero_interval_correct = prove
 (`candle_cv_q_zero_interval =
   candle_cv_q_interval candle_q_zero_interval`,
  REWRITE_TAC[candle_cv_q_zero_interval_def]);;

let candle_cv_bool_true_encoding = prove
 (`Cexp_num 1 = candle_cv_bool T`,
  REWRITE_TAC[candle_cv_bool_def; ARITH_RULE `1 = SUC 0`]);;

let candle_cv_q_dim_taylor_model_result_default_correct = prove
 (`!center_boxes boxes.
     candle_cv_q_dim_taylor_model_result_default
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_default center_boxes boxes)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_default_def;
              candle_q_dim_taylor_model_result_default_def;
              candle_cv_q_dim_first_jet_zero_correct;
              candle_cv_q_zero_interval_correct;
              candle_cv_q_dim_interval_zeros_correct;
              candle_cv_q_dim_interval_zero_matrix_correct;
              candle_cv_q_dim_taylor_model_result_encode_def;
              candle_cv_q_dim_taylor_model_result_make_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_q_dim_taylor_model_result_domain_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_value_bound_def;
              candle_q_dim_taylor_model_result_gradient_bounds_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_cv_bool_def; FST; SND]);;

let candle_cv_q_dim_taylor_model_result_head_correct = prove
 (`!center_boxes boxes stack.
     candle_cv_q_dim_taylor_model_result_head
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_taylor_model_result_list_encode stack) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_head center_boxes boxes stack)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_head_def;
              candle_q_dim_taylor_model_result_head_def;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def;
              candle_cv_q_dim_taylor_model_result_default_correct]);;

let candle_cv_q_dim_taylor_model_result_tail_correct = prove
 (`!stack.
     candle_cv_q_dim_taylor_model_result_tail
       (candle_cv_q_dim_taylor_model_result_list_encode stack) =
     candle_cv_q_dim_taylor_model_result_list_encode
       (candle_q_dim_taylor_model_result_tail stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_tail_def;
              candle_q_dim_taylor_model_result_tail_def;
              candle_cv_q_dim_taylor_model_result_list_encode_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_q_dim_taylor_model_result_inv_def = new_definition
 `candle_q_dim_taylor_model_result_inv radii result =
    candle_q_dim_taylor_model_result_complete radii
      (candle_q_dim_taylor_model_result_domain result /\
       candle_q_dim_jet_inv_domain
         (candle_q_dim_taylor_model_result_center result) /\
       candle_q_dim_jet_inv_domain
         (candle_q_dim_taylor_model_proxy result))
      (candle_q_dim_jet_inv
        (candle_q_dim_taylor_model_result_center result))
      (candle_q_dim_jet_hessian
        (candle_q_dim_jet_inv
          (candle_q_dim_taylor_model_proxy result)))`;;

let candle_q_dim_taylor_model_result_sqrt_def = new_definition
 `candle_q_dim_taylor_model_result_sqrt
      radii center_s box_s result =
    candle_q_dim_taylor_model_result_complete radii
      (candle_q_dim_taylor_model_result_domain result /\
       candle_q_dim_jet_sqrt_domain center_s
         (candle_q_dim_taylor_model_result_center result) /\
       candle_q_dim_jet_sqrt_domain box_s
         (candle_q_dim_taylor_model_proxy result))
      (candle_q_dim_jet_sqrt_with center_s
        (candle_q_dim_taylor_model_result_center result))
      (candle_q_dim_jet_hessian
        (candle_q_dim_jet_sqrt_with box_s
          (candle_q_dim_taylor_model_proxy result)))`;;

let candle_cv_q_dim_taylor_model_result_inv_correct = prove
 (`!radii result.
     candle_cv_q_dim_taylor_model_result_inv
       (candle_cv_q_list radii)
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_inv radii result)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_inv_def;
              candle_q_dim_taylor_model_result_inv_def;
              candle_cv_q_dim_taylor_model_result_domain_correct;
              candle_cv_q_dim_analytic_first_jet_inv_domain_correct;
              candle_cv_q_dim_taylor_model_result_center_correct;
              candle_cv_q_dim_taylor_model_proxy_correct;
              candle_cv_q_dim_jet_inv_domain_bool_correct;
              candle_cv_bool_and_correct;
              candle_cv_q_dim_analytic_first_jet_inv_correct;
              candle_cv_q_dim_jet_inv_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_dim_taylor_model_result_complete_correct]);;

let candle_cv_q_dim_taylor_model_result_sqrt_correct = prove
 (`!radii center_s box_s result.
     candle_cv_q_dim_taylor_model_result_sqrt
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_s)
       (candle_cv_q_interval box_s)
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_sqrt
         radii center_s box_s result)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_sqrt_def;
              candle_q_dim_taylor_model_result_sqrt_def;
              candle_cv_q_dim_taylor_model_result_domain_correct;
              candle_cv_q_dim_analytic_first_jet_sqrt_domain_correct;
              candle_cv_q_dim_taylor_model_result_center_correct;
              candle_cv_q_dim_taylor_model_proxy_correct;
              candle_cv_q_dim_jet_sqrt_domain_bool_correct;
              candle_cv_bool_and_correct;
              candle_cv_q_dim_analytic_first_jet_sqrt_with_correct;
              candle_cv_q_dim_jet_sqrt_with_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_dim_taylor_model_result_complete_correct]);;

let candle_q_dim_taylor_model_poly_constant_def = new_definition
 `candle_q_dim_taylor_model_poly_constant center_boxes boxes radii q =
    candle_q_dim_taylor_model_result_complete radii T
      (candle_q_dim_jet_normalized_constant center_boxes q)
      (candle_q_dim_interval_zero_matrix_like boxes boxes)`;;

let candle_q_dim_taylor_model_poly_variable_def = new_definition
 `candle_q_dim_taylor_model_poly_variable
      center_boxes boxes radii variable =
    candle_q_dim_taylor_model_result_complete radii T
      (candle_q_dim_jet_normalized_variable center_boxes variable)
      (candle_q_dim_interval_zero_matrix_like boxes boxes)`;;

let candle_cv_q_dim_taylor_model_poly_constant_correct = prove
 (`!center_boxes boxes radii q.
     candle_cv_q_dim_taylor_model_poly_constant
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii) (candle_cv_q q) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_poly_constant
         center_boxes boxes radii q)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_poly_constant_def;
              candle_q_dim_taylor_model_poly_constant_def;
              candle_cv_q_dim_first_jet_constant_correct;
              candle_cv_q_dim_interval_zero_matrix_correct;
              candle_cv_bool_true_encoding;
              candle_cv_q_dim_taylor_model_result_complete_correct]);;

let candle_cv_q_dim_taylor_model_poly_variable_correct = prove
 (`!center_boxes boxes radii variable.
     candle_cv_q_dim_taylor_model_poly_variable
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii) (Cexp_num variable) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_poly_variable
         center_boxes boxes radii variable)`,
  REWRITE_TAC[candle_cv_q_dim_taylor_model_poly_variable_def;
              candle_q_dim_taylor_model_poly_variable_def;
              candle_cv_q_dim_first_jet_variable_correct;
              candle_cv_q_dim_interval_zero_matrix_correct;
              candle_cv_bool_true_encoding;
              candle_cv_q_dim_taylor_model_result_complete_correct]);;

end;;
