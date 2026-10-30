(* ========================================================================== *)
(* Executable exact-result constructors for packed source certificates.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  These cval functions mirror the ordinary-HOL   *)
(* result constructors used by the authenticated source semantics.  They are  *)
(* deliberately independent of the fixed-word implementation: the eventual   *)
(* registered callback may refine them without replaying their exact rational *)
(* arithmetic inside Candle.                                                  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_certified_atn_sound.ml";;

module Candle_cv_analytic_expr_packed_source_certificate_result_compute = struct

open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_representation;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_packed_source_certificate_core;;
open Candle_cv_analytic_expr_packed_source_sqrt;;
open Candle_cv_analytic_expr_packed_source_certified_inverse_sound;;
open Candle_cv_analytic_expr_packed_source_certified_sqrt_sound;;
open Candle_cv_analytic_expr_packed_source_certified_atn_sound;;

let candle_cv_q_dim_first_jet_unary_with_def = new_definition
 `candle_cv_q_dim_first_jet_unary_with value d_interval jet =
    candle_cv_q_dim_first_jet_make value
      (candle_cv_q_dim_interval_list_scale d_interval
        (candle_cv_q_dim_first_jet_gradient jet))`;;

let candle_cv_q_dim_first_jet_unary_with_correct = prove
 (`!value d_interval second jet.
     candle_cv_q_dim_first_jet_unary_with
       (candle_cv_q_interval value)
       (candle_cv_q_interval d_interval)
       (candle_cv_q_dim_first_jet_encode jet) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_unary_with value d_interval second jet)`,
  REWRITE_TAC
    [candle_cv_q_dim_first_jet_unary_with_def;
     candle_q_dim_jet_unary_with_def;
     candle_cv_q_dim_first_jet_encode_def;
     candle_cv_q_dim_first_jet_make_def;
     candle_cv_q_dim_first_jet_gradient_def;
     candle_cv_q_dim_interval_list_scale_correct;
     candle_q_dim_jet_make_def;
     candle_q_dim_jet_f_def; candle_q_dim_jet_gradient_def;
     cexp_snd_def; FST; SND]);;

let _ = print_endline "CANDLE_CERT_RESULT_STAGE first-unary";;

let candle_cv_q_dim_first_jet_inv_with_def = new_definition
 `candle_cv_q_dim_first_jet_inv_with reciprocal jet =
    candle_cv_q_dim_first_jet_unary_with reciprocal
      (candle_cv_q_interval_neg
        (candle_cv_q_interval_mul_normalized reciprocal reciprocal)) jet`;;

let candle_cv_q_dim_first_jet_inv_with_correct = prove
 (`!reciprocal jet.
     candle_cv_q_dim_first_jet_inv_with
       (candle_cv_q_interval reciprocal)
       (candle_cv_q_dim_first_jet_encode jet) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_inv_with reciprocal jet)`,
  REWRITE_TAC
    [candle_cv_q_dim_first_jet_inv_with_def;
     candle_cv_q_dim_first_jet_unary_with_def;
     candle_q_dim_jet_inv_with_def;
     candle_cv_q_dim_first_jet_encode_def;
     candle_cv_q_dim_first_jet_make_def;
     candle_cv_q_dim_first_jet_gradient_def;
     candle_cv_q_interval_mul_normalized_correct;
     candle_cv_q_interval_neg_correct;
     candle_cv_q_dim_interval_list_scale_correct;
     candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
     candle_q_dim_jet_gradient_def; cexp_snd_def; FST; SND]);;

let _ = print_endline "CANDLE_CERT_RESULT_STAGE first-inv";;

let candle_cv_q_dim_taylor_model_result_inv_certified_def = new_definition
 `candle_cv_q_dim_taylor_model_result_inv_certified
      radii center_reciprocal box_reciprocal result =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_q_dim_taylor_model_result_domain result)
      (candle_cv_q_dim_first_jet_inv_with center_reciprocal
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_jet_inv_with box_reciprocal
          (candle_cv_q_dim_taylor_model_proxy result)))`;;

let candle_cv_q_dim_taylor_model_result_inv_certified_correct = prove
 (`!radii center_reciprocal box_reciprocal result.
     candle_cv_q_dim_taylor_model_result_inv_certified
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_reciprocal)
       (candle_cv_q_interval box_reciprocal)
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_inv_certified
         radii center_reciprocal box_reciprocal result)`,
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_result_inv_certified_def;
     candle_q_dim_taylor_model_result_inv_certified_def;
     candle_cv_q_dim_taylor_model_result_domain_correct;
     candle_cv_q_dim_taylor_model_result_center_correct;
     candle_cv_q_dim_first_jet_inv_with_correct;
     candle_cv_q_dim_taylor_model_proxy_correct;
     candle_cv_q_dim_jet_inv_with_correct;
     candle_cv_q_dim_jet_hessian_correct;
     candle_cv_q_dim_taylor_model_result_complete_correct]);;

let _ = print_endline "CANDLE_CERT_RESULT_STAGE inv";;

let candle_cv_q_dim_first_jet_sqrt_certified_correct = prove
 (`!center_root center_derivative box_second_reciprocal jet.
     candle_cv_q_dim_first_jet_unary_with
       (candle_cv_q_interval center_root)
       (candle_cv_q_interval center_derivative)
       (candle_cv_q_dim_first_jet_encode jet) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_unary_with center_root center_derivative
         (candle_q_interval_neg box_second_reciprocal) jet)`,
  REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC
    (SPECL
      [`center_root:((num#num)#num)#((num#num)#num)`;
       `center_derivative:((num#num)#num)#((num#num)#num)`;
       `candle_q_interval_neg
          (box_second_reciprocal:((num#num)#num)#((num#num)#num))`;
       `jet:((((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list)#
          ((((num#num)#num)#((num#num)#num))list)list)`]
      candle_cv_q_dim_first_jet_unary_with_correct));;

let candle_cv_q_dim_taylor_model_result_sqrt_certified_def = new_definition
 `candle_cv_q_dim_taylor_model_result_sqrt_certified radii
      center_root box_root center_derivative box_derivative
      box_second_reciprocal result =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_q_dim_taylor_model_result_domain result)
      (candle_cv_q_dim_first_jet_unary_with center_root center_derivative
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_jet_sqrt_certified box_root box_derivative
          box_second_reciprocal
          (candle_cv_q_dim_taylor_model_proxy result)))`;;

let candle_cv_q_dim_taylor_model_result_sqrt_certified_correct = prove
 (`!radii center_root box_root center_derivative box_derivative
       box_second_reciprocal result.
     candle_cv_q_dim_taylor_model_result_sqrt_certified
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_root)
       (candle_cv_q_interval box_root)
       (candle_cv_q_interval center_derivative)
       (candle_cv_q_interval box_derivative)
       (candle_cv_q_interval box_second_reciprocal)
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_sqrt_certified radii
         center_root box_root center_derivative box_derivative
         box_second_reciprocal result)`,
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_result_sqrt_certified_def;
     candle_q_dim_taylor_model_result_sqrt_certified_def;
     candle_cv_q_dim_taylor_model_result_domain_correct;
     candle_cv_q_dim_taylor_model_result_center_correct;
     candle_cv_q_dim_first_jet_sqrt_certified_correct;
     candle_cv_q_dim_taylor_model_proxy_correct;
     candle_cv_q_dim_jet_sqrt_certified_correct;
     candle_cv_q_dim_jet_hessian_correct;
     candle_cv_q_dim_taylor_model_result_complete_correct]);;

let _ = print_endline "CANDLE_CERT_RESULT_STAGE sqrt";;

let candle_cv_q_dim_jet_atn_second_with_square_def = new_definition
 `candle_cv_q_dim_jet_atn_second_with_square input derivative_square =
    candle_cv_q_interval_neg
      (candle_cv_q_interval_mul_normalized
        (candle_cv_q_interval_add_normalized input input)
        derivative_square)`;;

let candle_cv_q_dim_jet_atn_second_with_square_correct = prove
 (`!input derivative_square.
     candle_cv_q_dim_jet_atn_second_with_square
       (candle_cv_q_interval input)
       (candle_cv_q_interval derivative_square) =
     candle_cv_q_interval
       (candle_q_dim_jet_atn_second_with_square input derivative_square)`,
  REWRITE_TAC
    [candle_cv_q_dim_jet_atn_second_with_square_def;
     candle_q_dim_jet_atn_second_with_square_def;
     candle_cv_q_interval_add_normalized_correct;
     candle_cv_q_interval_mul_normalized_correct;
     candle_cv_q_interval_neg_correct]);;

let _ = print_endline "CANDLE_CERT_RESULT_STAGE atn-second";;

let candle_cv_q_atn_universal_interval_def = new_definition
 `candle_cv_q_atn_universal_interval =
    Cexp_pair
      (candle_cv_q_neg (Cexp_snd candle_cv_q_atn_pi_half_interval))
      (Cexp_snd candle_cv_q_atn_pi_half_interval)`;;

let candle_cv_q_atn_universal_interval_correct = prove
 (`candle_cv_q_atn_universal_interval =
     candle_cv_q_interval candle_q_atn_universal_interval`,
  REWRITE_TAC
    [candle_cv_q_atn_universal_interval_def;
     candle_q_atn_universal_interval_def;
     candle_cv_q_atn_pi_half_interval_def;
     candle_cv_q_interval_def; cexp_snd_def;
     candle_cv_q_neg_correct]);;

let _ = print_endline "CANDLE_CERT_RESULT_STAGE atn-universal";;

let candle_cv_q_dim_jet_atn_faithful_def = new_definition
 `candle_cv_q_dim_jet_atn_faithful
      output d_interval second_input d_square jet =
    candle_cv_q_dim_jet_unary_with output d_interval
      (candle_cv_q_dim_jet_atn_second_with_square
        second_input d_square) jet`;;

let candle_cv_q_dim_jet_atn_faithful_correct = prove
 (`!output d_interval second_input d_square jet.
     candle_cv_q_dim_jet_atn_faithful
       (candle_cv_q_interval output)
       (candle_cv_q_interval d_interval)
       (candle_cv_q_interval second_input)
       (candle_cv_q_interval d_square)
       (candle_cv_q_dim_jet_encode jet) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_jet_atn_faithful
         output d_interval second_input d_square jet)`,
  REWRITE_TAC
    [candle_cv_q_dim_jet_atn_faithful_def;
     candle_q_dim_jet_atn_faithful_def;
     candle_cv_q_dim_jet_atn_second_with_square_correct;
     candle_cv_q_dim_jet_unary_with_correct]);;

let _ = print_endline "CANDLE_CERT_RESULT_STAGE atn-jet";;

let candle_cv_q_dim_first_jet_atn_faithful_def = new_definition
 `candle_cv_q_dim_first_jet_atn_faithful
      output d_interval second_input d_square jet =
    candle_cv_q_dim_first_jet_unary_with output d_interval jet`;;

let candle_cv_q_dim_first_jet_atn_faithful_correct = prove
 (`!output d_interval second_input d_square jet.
     candle_cv_q_dim_first_jet_atn_faithful
       (candle_cv_q_interval output)
       (candle_cv_q_interval d_interval)
       (candle_cv_q_interval second_input)
       (candle_cv_q_interval d_square)
       (candle_cv_q_dim_first_jet_encode jet) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_atn_faithful
         output d_interval second_input d_square jet)`,
  REWRITE_TAC
    [candle_cv_q_dim_first_jet_atn_faithful_def;
     candle_q_dim_jet_atn_faithful_def;
     candle_cv_q_dim_first_jet_unary_with_def;
     candle_q_dim_jet_unary_with_def;
     candle_cv_q_dim_first_jet_encode_def;
     candle_cv_q_dim_first_jet_make_def;
     candle_cv_q_dim_first_jet_gradient_def;
     candle_cv_q_dim_interval_list_scale_correct;
     candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
     candle_q_dim_jet_gradient_def; cexp_snd_def; FST; SND]);;

let _ = print_endline "CANDLE_CERT_RESULT_STAGE first-atn";;

let candle_cv_q_dim_taylor_model_result_atn_faithful_def = new_definition
 `candle_cv_q_dim_taylor_model_result_atn_faithful radii box_input
      center_result center_derivative box_derivative box_derivative_square
      result =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_q_dim_taylor_model_result_domain result)
      (candle_cv_q_dim_first_jet_atn_faithful
        center_result center_derivative
        box_input box_derivative_square
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_jet_atn_faithful
          candle_cv_q_atn_universal_interval box_derivative box_input
          box_derivative_square
          (candle_cv_q_dim_taylor_model_proxy result)))`;;

let candle_cv_q_dim_taylor_model_result_atn_faithful_correct = prove
 (`!radii box_input center_result center_derivative box_derivative
       box_derivative_square result.
     candle_cv_q_dim_taylor_model_result_atn_faithful
       (candle_cv_q_list radii)
       (candle_cv_q_interval box_input)
       (candle_cv_q_interval center_result)
       (candle_cv_q_interval center_derivative)
       (candle_cv_q_interval box_derivative)
       (candle_cv_q_interval box_derivative_square)
       (candle_cv_q_dim_taylor_model_result_encode result) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_dim_taylor_model_result_atn_faithful radii box_input
         center_result center_derivative box_derivative
         box_derivative_square result)`,
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_result_atn_faithful_def;
     candle_q_dim_taylor_model_result_atn_faithful_def;
     candle_cv_q_dim_taylor_model_result_domain_correct;
     candle_cv_q_dim_taylor_model_result_center_correct;
     candle_cv_q_dim_first_jet_atn_faithful_correct;
     candle_cv_q_atn_universal_interval_correct;
     candle_cv_q_dim_taylor_model_proxy_correct;
     candle_cv_q_dim_jet_atn_faithful_correct;
     candle_cv_q_dim_jet_hessian_correct;
     candle_cv_q_dim_taylor_model_result_complete_correct]);;

let _ = print_endline "CANDLE_CERT_RESULT_STAGE atn-result";;

let candle_cv_q_packed_source_certificate_result_compute_eqs =
  map SPEC_ALL
    [candle_cv_q_dim_first_jet_unary_with_def;
     candle_cv_q_dim_first_jet_inv_with_def;
     candle_cv_q_dim_taylor_model_result_inv_certified_def;
     candle_cv_q_dim_taylor_model_result_sqrt_certified_def;
     candle_cv_q_dim_jet_atn_second_with_square_def;
     candle_cv_q_atn_universal_interval_def;
     candle_cv_q_dim_jet_atn_faithful_def;
     candle_cv_q_dim_first_jet_atn_faithful_def;
     candle_cv_q_dim_taylor_model_result_atn_faithful_def];;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_dim_first_jet_unary_with_correct;
     candle_cv_q_dim_first_jet_inv_with_correct;
     candle_cv_q_dim_first_jet_sqrt_certified_correct;
     candle_cv_q_dim_taylor_model_result_inv_certified_correct;
     candle_cv_q_dim_taylor_model_result_sqrt_certified_correct;
     candle_cv_q_dim_jet_atn_second_with_square_correct;
     candle_cv_q_atn_universal_interval_correct;
     candle_cv_q_dim_jet_atn_faithful_correct;
     candle_cv_q_dim_first_jet_atn_faithful_correct;
     candle_cv_q_dim_taylor_model_result_atn_faithful_correct] then
  failwith "packed source certificate result compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFICATE_RESULT_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
