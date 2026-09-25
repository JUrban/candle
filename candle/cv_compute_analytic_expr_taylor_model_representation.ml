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
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_representation;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_expr_first_jet_program_compute;;
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

end;;
