(* ========================================================================== *)
(* Universal analytic-invariant bridge for the fixed algebraic conversion.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_invariant = struct

open Multivariate_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_sound;;

let candle_fsa_result_of_q_analytic_invariant = prove
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
       (candle_fs_result_to_q (candle_fsa_result_of_q result))
       center_e box_e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "input_invariant") THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_fsa_result_of_q_domain_roundtrip] THEN
  DISCH_TAC THEN
  USE_THEN "input_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  POP_ASSUM
   (fun box_contains_th ->
      POP_ASSUM
       (fun proxy_shape_th ->
          LABEL_TAC "box_contains_all" box_contains_th THEN
          LABEL_TAC "proxy_shape" proxy_shape_th)) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[candle_fsa_result_of_q_center] THEN
    MATCH_MP_TAC candle_fsa_jet_of_q_shape THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "proxy_shape" MP_TAC THEN
      REWRITE_TAC[candle_q_dim_jet_shape_def;
                  candle_q_dim_taylor_model_proxy_hessian] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[candle_fsa_result_of_q_center] THEN
    ONCE_REWRITE_TAC[GSYM candle_q_dim_taylor_model_proxy_hessian] THEN
    REWRITE_TAC[candle_q_dim_analytic_contains_def] THEN
    MATCH_MP_TAC candle_fsa_jet_of_q_contains_components THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      MP_TAC
       (MATCH_MP
         (ISPECL
           [`dimindex (:N)`;
            `candle_q_dim_taylor_model_proxy
              (result:
                bool#
                ((((num#num)#num)#(num#num)#num)#
                 (((num#num)#num)#(num#num)#num)list#
                 ((((num#num)#num)#(num#num)#num)list)list)#
                (((num#num)#num)#(num#num)#num)#
                (((num#num)#num)#(num#num)#num)list#
                ((((num#num)#num)#(num#num)#num)list)list)`;
            `list_of_seq
              (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
              (dimindex (:N))`;
            `center_e:candle_analytic_expr`;
            `box_e:candle_analytic_expr`]
           candle_q_dim_analytic_contains_certificate_transport)
         (ASSUME
           `candle_analytic_erase_sqrt_certificates center_e =
            candle_analytic_erase_sqrt_certificates box_e`)) THEN
      DISCH_THEN (fun th -> MATCH_MP_TAC (snd (EQ_IMP_RULE th))) THEN
      USE_THEN "box_contains_all"
       (fun th ->
          MATCH_MP_TAC
           (SPEC `(candle_q_box_center_vector boxes : real^N)` th)) THEN
      MATCH_MP_TAC y_in_domain THEN
      EXISTS_TAC `(candle_q_box_radius_vector boxes : real^N)` THEN
      MATCH_MP_TAC candle_q_box_m_cell_domain THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[candle_fsa_result_of_q_proxy] THEN
    ONCE_REWRITE_TAC[GSYM candle_q_dim_taylor_model_proxy_hessian] THEN
    MATCH_MP_TAC candle_fsa_jet_of_q_shape THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "proxy_shape" MP_TAC THEN
      REWRITE_TAC[candle_q_dim_jet_shape_def;
                  candle_q_dim_taylor_model_proxy_hessian] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[candle_fsa_result_of_q_proxy] THEN
    ONCE_REWRITE_TAC[GSYM candle_q_dim_taylor_model_proxy_hessian] THEN
    REWRITE_TAC[candle_q_dim_analytic_contains_def] THEN
    MATCH_MP_TAC candle_fsa_jet_of_q_contains_components THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      USE_THEN "box_contains_all"
       (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      USE_THEN "box_contains_all"
       (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
      ASM_REWRITE_TAC[]]]);;

end;;
