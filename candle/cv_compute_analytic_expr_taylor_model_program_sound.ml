(* ========================================================================== *)
(* Source invariant for the paired centered Taylor-model program.            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Center and whole-box programs may use         *)
(* different square-root certificates.  When the accumulated domain bit is  *)
(* true, the rounded center jet denotes the center expression and the        *)
(* reconstructed proxy denotes the certificate-equivalent box expression.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_invariant.ml";;

module Candle_cv_analytic_expr_taylor_model_program_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_domain;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_semantics;;
open Candle_cv_analytic_expr_taylor_model_invariant;;

let candle_q_dim_taylor_model_result_analytic_invariant_def =
  new_definition
 `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N)
      (boxes:(((num#num)#num)#((num#num)#num))list)
      result center_e box_e <=>
    candle_q_dim_taylor_model_result_domain result
    ==>
    candle_q_dim_analytic_domain
      (candle_q_center_environment_list boxes) center_e /\
    candle_q_dim_analytic_domain boxes box_e /\
    candle_q_dim_jet_shape (dimindex (:N))
      (candle_q_dim_taylor_model_result_center result) /\
    candle_q_dim_analytic_contains (dimindex (:N))
      (candle_q_dim_taylor_model_result_center result)
      (list_of_seq
        (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
        (dimindex (:N))) center_e /\
    candle_q_dim_jet_shape (dimindex (:N))
      (candle_q_dim_taylor_model_proxy result) /\
    (!(p:real^N). p IN interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]
        ==> candle_q_dim_analytic_contains (dimindex (:N))
              (candle_q_dim_taylor_model_proxy result)
              (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) box_e)`;;

let candle_q_dim_taylor_model_result_complete_domain = prove
 (`!radii domain center_jet box_jet.
     candle_q_dim_taylor_model_result_domain
       (candle_q_dim_taylor_model_result_complete radii domain center_jet
         (candle_q_dim_jet_hessian box_jet)) = domain`,
  REWRITE_TAC[candle_q_dim_taylor_model_result_complete_def;
              candle_q_dim_taylor_model_result_complete_rounded_def;
              candle_q_dim_taylor_model_result_domain_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND]);;

let candle_q_dim_taylor_model_complete_analytic_invariant = prove
 (`!center_e box_e boxes domain center_jet box_jet (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     (domain ==>
       candle_q_dim_analytic_domain
         (candle_q_center_environment_list boxes) center_e /\
       candle_q_dim_analytic_domain boxes box_e /\
       candle_q_dim_jet_shape (dimindex (:N)) center_jet /\
       candle_q_dim_analytic_contains (dimindex (:N)) center_jet
         (list_of_seq
           (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
           (dimindex (:N))) center_e /\
       candle_q_dim_jet_shape (dimindex (:N)) box_jet /\
       (!(p:real^N). p IN interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]
          ==> candle_q_dim_analytic_contains (dimindex (:N)) box_jet
                (list_of_seq (\k. p$(k + 1)) (dimindex (:N))) box_e))
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant type_witness boxes
       (candle_q_dim_taylor_model_result_complete
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         domain center_jet (candle_q_dim_jet_hessian box_jet))
       center_e box_e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "complete_premises") THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_q_dim_taylor_model_result_complete_domain] THEN
  DISCH_TAC THEN
  USE_THEN "complete_premises"
    (fun th -> MP_TAC (MATCH_MP th (ASSUME `domain:bool`))) THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_complete_center_shape THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_q_dim_analytic_contains_def] THEN
    MATCH_MP_TAC candle_q_dim_taylor_model_result_complete_center_contains THEN
    ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_complete_proxy_shape THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    let center_contains_box_e =
      EQ_MP
        (MATCH_MP
          (ISPECL
            [`dimindex (:N)`; `center_jet:
               (((num#num)#num)#((num#num)#num))#
               ((((num#num)#num)#((num#num)#num))list#
                (((((num#num)#num)#((num#num)#num))list)list))`;
             `list_of_seq
               (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
               (dimindex (:N))`;
             `center_e:candle_analytic_expr`;
             `box_e:candle_analytic_expr`]
            candle_q_dim_analytic_contains_certificate_transport)
          (ASSUME
            `candle_analytic_erase_sqrt_certificates center_e =
             candle_analytic_erase_sqrt_certificates box_e`))
        (ASSUME
          `candle_q_dim_analytic_contains (dimindex (:N)) center_jet
            (list_of_seq
              (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
              (dimindex (:N))) center_e`) in
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_q_dim_analytic_taylor_model_proxy_contains THEN
    ASM_REWRITE_TAC[center_contains_box_e]]);;

end;;
