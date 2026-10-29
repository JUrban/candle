(* ========================================================================== *)
(* Certificate-driven reciprocal Taylor results for packed source replay.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Unlike the older exact-rational reciprocal   *)
(* constructor, this result retains the outward-rounded center and whole-box *)
(* reciprocal intervals supplied by the fast checker.  Its soundness theorem *)
(* is therefore the ordinary-HOL semantic target for the packed object step. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_item_operations_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certificate_core.ml";;

module Candle_cv_analytic_expr_packed_source_certified_inverse_sound = struct

open Candle_cv_exact_interval_inv_core;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_domain;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_core;;
open Candle_cv_analytic_expr_packed_source_item_invariant;;
open Candle_cv_analytic_expr_packed_source_item_operations_sound;;

let candle_q_dim_taylor_model_result_inv_certified_def = new_definition
 `candle_q_dim_taylor_model_result_inv_certified
      radii center_reciprocal box_reciprocal result =
    candle_q_dim_taylor_model_result_complete radii
      (candle_q_dim_taylor_model_result_domain result)
      (candle_q_dim_jet_inv_with center_reciprocal
        (candle_q_dim_taylor_model_result_center result))
      (candle_q_dim_jet_hessian
        (candle_q_dim_jet_inv_with box_reciprocal
          (candle_q_dim_taylor_model_proxy result)))`;;

let candle_q_dim_taylor_model_result_inv_certified_analytic_invariant = prove
 (`!center_e box_e boxes result center_reciprocal box_reciprocal
      (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes result center_e box_e /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center result))
       center_reciprocal /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_f (candle_q_dim_taylor_model_proxy result))
       box_reciprocal
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_inv_certified
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         center_reciprocal box_reciprocal result)
       (Candle_analytic_inv center_e) (Candle_analytic_inv box_e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 (LABEL_TAC "input_invariant")
              (CONJUNCTS_THEN2 (LABEL_TAC "center_certificate")
                (LABEL_TAC "box_certificate"))))))) THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_inv_certified_def] THEN
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
       [USE_THEN "center_regular" MATCH_ACCEPT_TAC;
        USE_THEN "center_contains" (fun center_contains_th ->
          USE_THEN "center_certificate" (fun center_certificate_th ->
            let value_contains_th =
              CONJUNCT1
                (REWRITE_RULE[candle_q_dim_analytic_contains_def;
                              candle_q_dim_jet_contains_components_def]
                  center_contains_th) in
            let not_zero_th =
              CONJUNCT1
                (REWRITE_RULE[candle_q_interval_inv_certificate_def]
                  center_certificate_th) in
            MATCH_ACCEPT_TAC
              (MATCH_MP candle_q_interval_not_zero_contains_nonzero
                (CONJ not_zero_th value_contains_th))))];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      USE_THEN "box_regular" (fun box_regular_th ->
        USE_THEN "box_contains_all" (fun box_contains_all_th ->
          USE_THEN "box_certificate" (fun box_certificate_th ->
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
            let not_zero_th =
              CONJUNCT1
                (REWRITE_RULE[candle_q_interval_inv_certificate_def]
                  box_certificate_th) in
            REWRITE_TAC[candle_analytic_regular_at_def] THEN
            CONJ_TAC THENL
             [MATCH_ACCEPT_TAC regular_at_p;
              MATCH_ACCEPT_TAC
                (MATCH_MP candle_q_interval_not_zero_contains_nonzero
                  (CONJ not_zero_th value_contains_th))])));
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_jet_inv_with_shape THEN
      USE_THEN "center_shape" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_inv_with_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      USE_THEN "center_certificate" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_jet_inv_with_shape THEN
      USE_THEN "proxy_shape" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    USE_THEN "box_contains_all" (fun box_contains_all_th ->
      let contains_at_p =
        MATCH_MP (SPEC `p:real^N` box_contains_all_th)
          (ASSUME
            `(p:real^N) IN interval
              [candle_q_box_lower_vector boxes,
               candle_q_box_upper_vector boxes]`) in
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_inv_with_components_sound THEN
      ASM_REWRITE_TAC[GSYM candle_q_dim_analytic_contains_def] THEN
      ACCEPT_TAC contains_at_p)]);;

let candle_q_packed_source_item_inv_certified_def = new_definition
 `candle_q_packed_source_item_inv_certified
      boxes center_reciprocal box_reciprocal item =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_result_inv_certified
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        center_reciprocal box_reciprocal
        (candle_q_packed_source_item_result item))
      (Candle_analytic_inv
        (candle_q_packed_source_item_center_expr item))
      (Candle_analytic_inv
        (candle_q_packed_source_item_box_expr item))`;;

let candle_q_packed_source_item_inv_certified_analytic_invariant = prove
 (`!boxes center_reciprocal box_reciprocal item.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_item_analytic_invariant boxes item /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item)))
       center_reciprocal /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_proxy
           (candle_q_packed_source_item_result item)))
       box_reciprocal
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_item_inv_certified
         boxes center_reciprocal box_reciprocal item)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "item_invariant")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_certificate")
            (LABEL_TAC "box_certificate"))))) THEN
  USE_THEN "item_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_source_item_result_def;
                  candle_q_packed_source_item_center_expr_def;
                  candle_q_packed_source_item_box_expr_def]) THEN
  REWRITE_TAC[candle_q_packed_source_item_inv_certified_def;
              candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    MATCH_MP_TAC
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (INST_TYPE [`:6`,`:N`]
          candle_q_dim_taylor_model_result_inv_certified_analytic_invariant)) THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [USE_THEN "center_certificate" MATCH_ACCEPT_TAC;
      USE_THEN "box_certificate" MATCH_ACCEPT_TAC]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_dim_taylor_model_result_inv_certified_analytic_invariant;
     candle_q_packed_source_item_inv_certified_analytic_invariant] then
  failwith "packed source certified inverse: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFIED_INVERSE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
