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
open Candle_cv_analytic_expr_calculus;;
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

let candle_q_dim_taylor_model_proxy_neg_hessian = prove
 (`!result.
     candle_q_dim_jet_hessian
       (candle_q_dim_jet_normalized_neg
         (candle_q_dim_taylor_model_proxy result)) =
     candle_q_dim_interval_matrix_neg
       (candle_q_dim_taylor_model_result_hessian result)`,
  REWRITE_TAC[candle_q_dim_jet_normalized_neg_def;
              candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND]);;

let candle_q_dim_taylor_model_result_neg_analytic_invariant = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes result center_e box_e
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_neg
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         result)
       (Candle_analytic_neg center_e) (Candle_analytic_neg box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "input_invariant") THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_neg_def] THEN
  ONCE_REWRITE_TAC[GSYM candle_q_dim_taylor_model_proxy_neg_hessian] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    USE_THEN "input_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    POP_ASSUM (LABEL_TAC "box_contains_all") THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_q_dim_analytic_domain_def];
      ASM_REWRITE_TAC[candle_q_dim_analytic_domain_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_neg_shape THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_neg_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_neg_shape THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      USE_THEN "box_contains_all"
        (fun th ->
          ASSUME_TAC
            (MATCH_MP (SPEC `p:real^N` th)
              (ASSUME
                `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]`))) THEN
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_neg_components_sound THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
        ASM_REWRITE_TAC[]]]]);;

let candle_q_dim_taylor_model_proxy_add_hessian = prove
 (`!left right.
     candle_q_dim_jet_hessian
       (candle_q_dim_jet_normalized_add
         (candle_q_dim_taylor_model_proxy left)
         (candle_q_dim_taylor_model_proxy right)) =
     candle_q_dim_interval_matrix_add_normalized
       (candle_q_dim_taylor_model_result_hessian left)
       (candle_q_dim_taylor_model_result_hessian right)`,
  REWRITE_TAC[candle_q_dim_jet_normalized_add_def;
              candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND]);;

let candle_q_dim_taylor_model_result_add_analytic_invariant = prove
 (`!center_a center_b box_a box_b boxes left right
      (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_a /\
     candle_analytic_valid_dim (dimindex (:N)) box_b /\
     candle_analytic_erase_sqrt_certificates center_a =
       candle_analytic_erase_sqrt_certificates box_a /\
     candle_analytic_erase_sqrt_certificates center_b =
       candle_analytic_erase_sqrt_certificates box_b /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes left center_a box_a /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes right center_b box_b
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_add
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         left right)
       (Candle_analytic_add center_a center_b)
       (Candle_analytic_add box_a box_b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM
    (fun right_th ->
      POP_ASSUM
        (fun left_th ->
          LABEL_TAC "left_invariant" left_th THEN
          LABEL_TAC "right_invariant" right_th)) THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_add_def] THEN
  ONCE_REWRITE_TAC[GSYM candle_q_dim_taylor_model_proxy_add_hessian] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    USE_THEN "left_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    POP_ASSUM (LABEL_TAC "left_box_contains_all") THEN
    USE_THEN "right_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    POP_ASSUM (LABEL_TAC "right_box_contains_all") THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_q_dim_analytic_domain_def];
      ASM_REWRITE_TAC[candle_q_dim_analytic_domain_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_add_shape THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_add_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_add_shape THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      USE_THEN "left_box_contains_all"
        (fun th ->
          ASSUME_TAC
            (MATCH_MP (SPEC `p:real^N` th)
              (ASSUME
                `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]`))) THEN
      USE_THEN "right_box_contains_all"
        (fun th ->
          ASSUME_TAC
            (MATCH_MP (SPEC `p:real^N` th)
              (ASSUME
                `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]`))) THEN
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_add_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def]]]);;

let candle_q_dim_taylor_model_result_mul_analytic_invariant = prove
 (`!center_a center_b box_a box_b boxes left right
      (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_a /\
     candle_analytic_valid_dim (dimindex (:N)) box_b /\
     candle_analytic_erase_sqrt_certificates center_a =
       candle_analytic_erase_sqrt_certificates box_a /\
     candle_analytic_erase_sqrt_certificates center_b =
       candle_analytic_erase_sqrt_certificates box_b /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes left center_a box_a /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes right center_b box_b
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_mul
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         left right)
       (Candle_analytic_mul center_a center_b)
       (Candle_analytic_mul box_a box_b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM
    (fun right_th ->
      POP_ASSUM
        (fun left_th ->
          LABEL_TAC "left_invariant" left_th THEN
          LABEL_TAC "right_invariant" right_th)) THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_mul_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    USE_THEN "left_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    POP_ASSUM (LABEL_TAC "left_box_contains_all") THEN
    USE_THEN "right_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    POP_ASSUM (LABEL_TAC "right_box_contains_all") THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[candle_q_dim_analytic_domain_def];
      ASM_REWRITE_TAC[candle_q_dim_analytic_domain_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_mul_shape THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_mul_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def];
      MATCH_MP_TAC candle_q_dim_jet_normalized_mul_shape THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      USE_THEN "left_box_contains_all"
        (fun th ->
          ASSUME_TAC
            (MATCH_MP (SPEC `p:real^N` th)
              (ASSUME
                `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]`))) THEN
      USE_THEN "right_box_contains_all"
        (fun th ->
          ASSUME_TAC
            (MATCH_MP (SPEC `p:real^N` th)
              (ASSUME
                `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]`))) THEN
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_mul_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def]]]);;

end;;
