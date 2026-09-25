(* ========================================================================== *)
(* Nonlinear instruction preservation for the centered Taylor-model checker. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_nonlinear_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_domain;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;

let candle_q_dim_taylor_model_result_sqrt_analytic_invariant = prove
 (`!clp cln cld cup cun cud blp bln bld bup bun bud
      center_e box_e boxes result (type_witness:real^N).
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
       (candle_q_dim_taylor_model_result_sqrt
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_analytic_sqrt_interval clp cln cld cup cun cud)
         (candle_analytic_sqrt_interval blp bln bld bup bun bud)
         result)
       (Candle_analytic_sqrt clp cln cld cup cun cud center_e)
       (Candle_analytic_sqrt blp bln bld bup bun bud box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "input_invariant") THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_sqrt_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "input_domain")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_sqrt_domain")
          (LABEL_TAC "proxy_sqrt_domain"))) THEN
    USE_THEN "input_domain" ASSUME_TAC THEN
    USE_THEN "input_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "center_regular")
        (CONJUNCTS_THEN2 (LABEL_TAC "box_regular")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_shape")
            (CONJUNCTS_THEN2 (LABEL_TAC "center_contains")
              (CONJUNCTS_THEN2 (LABEL_TAC "proxy_shape")
                (LABEL_TAC "box_contains_all")))))) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_regular_at_def] THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "center_contains" (fun center_contains_th ->
          USE_THEN "center_sqrt_domain" (fun center_sqrt_domain_th ->
            let value_contains_th =
              CONJUNCT1
                (REWRITE_RULE[candle_q_dim_analytic_contains_def;
                              candle_q_dim_jet_contains_components_def]
                  center_contains_th) in
            let not_zero_th = center_sqrt_domain_th in
            ACCEPT_TAC
              (MATCH_MP
                candle_q_dim_jet_sqrt_domain_value_positive
                (CONJ not_zero_th value_contains_th))))];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      USE_THEN "box_regular" (fun box_regular_th ->
        USE_THEN "box_contains_all" (fun box_contains_all_th ->
          USE_THEN "proxy_sqrt_domain" (fun proxy_sqrt_domain_th ->
            let p_in_box =
              ASSUME
                `(p:real^N) IN interval
                  [candle_q_box_lower_vector boxes,
                   candle_q_box_upper_vector boxes]` in
            let regular_at_p =
              MATCH_MP (SPEC `p:real^N` box_regular_th) p_in_box in
            let contains_at_p =
              MATCH_MP (SPEC `p:real^N` box_contains_all_th) p_in_box in
            let value_contains_th =
              CONJUNCT1
                (REWRITE_RULE[candle_q_dim_analytic_contains_def;
                              candle_q_dim_jet_contains_components_def]
                  contains_at_p) in
            let not_zero_th = proxy_sqrt_domain_th in
            REWRITE_TAC[candle_analytic_regular_at_def] THEN
            CONJ_TAC THENL
             [ACCEPT_TAC regular_at_p;
              ACCEPT_TAC
                (MATCH_MP
                  candle_q_dim_jet_sqrt_domain_value_positive
                  (CONJ not_zero_th value_contains_th))])));
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_jet_sqrt_shape THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_sqrt_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_jet_sqrt_shape THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    USE_THEN "box_contains_all" (fun box_contains_all_th ->
      let contains_at_p =
        MATCH_MP
          (SPEC `p:real^N` box_contains_all_th)
          (ASSUME
            `(p:real^N) IN interval
              [candle_q_box_lower_vector boxes,
               candle_q_box_upper_vector boxes]`) in
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_sqrt_components_sound THEN
      CONJ_TAC THENL
       [USE_THEN "proxy_shape" ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [USE_THEN "proxy_sqrt_domain" ACCEPT_TAC;
        ACCEPT_TAC
          (REWRITE_RULE[candle_q_dim_analytic_contains_def]
            contains_at_p)])]);;

let candle_q_dim_taylor_model_result_atn_analytic_invariant = prove
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
       (candle_q_dim_taylor_model_result_atn
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         result)
       (Candle_analytic_atn center_e) (Candle_analytic_atn box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "input_invariant") THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_atn_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "input_domain")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_atn_domain")
          (LABEL_TAC "proxy_atn_domain"))) THEN
    USE_THEN "input_domain" ASSUME_TAC THEN
    USE_THEN "input_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "center_regular")
        (CONJUNCTS_THEN2 (LABEL_TAC "box_regular")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_shape")
            (CONJUNCTS_THEN2 (LABEL_TAC "center_contains")
              (CONJUNCTS_THEN2 (LABEL_TAC "proxy_shape")
                (LABEL_TAC "box_contains_all")))))) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_regular_at_def] THEN
      USE_THEN "center_regular" ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[candle_analytic_regular_at_def] THEN
      USE_THEN "box_regular" (fun box_regular_th ->
        MATCH_MP_TAC (SPEC `p:real^N` box_regular_th) THEN
        ASM_REWRITE_TAC[]);
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_jet_atn_shape THEN
      USE_THEN "center_shape" ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_atn_components_sound THEN
      CONJ_TAC THENL
       [USE_THEN "center_shape" ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [USE_THEN "center_atn_domain" ACCEPT_TAC;
        USE_THEN "center_contains" (fun center_contains_th ->
          ACCEPT_TAC
            (REWRITE_RULE[candle_q_dim_analytic_contains_def]
              center_contains_th))];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_jet_atn_shape THEN
      USE_THEN "proxy_shape" ACCEPT_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    USE_THEN "box_contains_all" (fun box_contains_all_th ->
      let contains_at_p =
        MATCH_MP
          (SPEC `p:real^N` box_contains_all_th)
          (ASSUME
            `(p:real^N) IN interval
              [candle_q_box_lower_vector boxes,
               candle_q_box_upper_vector boxes]`) in
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_atn_components_sound THEN
      CONJ_TAC THENL
       [USE_THEN "proxy_shape" ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [USE_THEN "proxy_atn_domain" ACCEPT_TAC;
        ACCEPT_TAC
          (REWRITE_RULE[candle_q_dim_analytic_contains_def]
            contains_at_p)])]);;

end;;
