(* ========================================================================== *)
(* Full semantic contract for a certificate-driven packed source entry.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the exact ordinary-HOL target for a  *)
(* future executable entry: complete center and outer certificate replays,   *)
(* authenticated geometry, source identity, Hessian identity, and final      *)
(* Taylor acceptance are all retained in one proposition.                    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_certificate_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_certificate_entry_sound = struct

open M_verifier;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_analytic_expr_packed_source_certificate_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_complete_sound;;

let candle_q_packed_source_certificate_completed_result_def = new_definition
 `candle_q_packed_source_certificate_completed_result
      radii center_item outer_item packed_hessian =
    candle_q_dim_taylor_model_result_complete
      radii
      (candle_q_dim_taylor_model_result_domain
         (candle_q_packed_source_item_result center_item) /\
       candle_q_dim_taylor_model_result_domain
         (candle_q_packed_source_item_result outer_item))
      (candle_q_packed_object_center_jet
        (candle_q_dim_taylor_model_result_value_bound
          (candle_q_packed_source_item_result center_item))
        (candle_q_dim_taylor_model_result_gradient_bounds
          (candle_q_packed_source_item_result center_item))
        packed_hessian)
      (candle_q_packed_hessian6_expand packed_hessian)`;;

let candle_q_packed_source_certificate_completed_result_domain = prove
 (`!radii center_item outer_item packed_hessian.
     candle_q_dim_taylor_model_result_domain
       (candle_q_packed_source_certificate_completed_result
         radii center_item outer_item packed_hessian) =
     (candle_q_dim_taylor_model_result_domain
        (candle_q_packed_source_item_result center_item) /\
      candle_q_dim_taylor_model_result_domain
        (candle_q_packed_source_item_result outer_item))`,
  REWRITE_TAC
    [candle_q_packed_source_certificate_completed_result_def;
     candle_q_dim_taylor_model_result_complete_def;
     candle_q_dim_taylor_model_result_complete_rounded_def;
     candle_q_dim_taylor_model_result_domain_def;
     candle_q_dim_taylor_model_result_make_def; FST; SND]);;

let candle_q_packed_source_certificate_accept_contract_def = new_definition
 `candle_q_packed_source_certificate_accept_contract
      source_boxes center_boxes outer_boxes radii sources
      center_certificates outer_certificates center_item outer_item
      packed_hessian <=>
    LENGTH source_boxes = 6 /\
    LENGTH center_boxes = 6 /\
    LENGTH outer_boxes = 6 /\
    candle_q_box_valid_list center_boxes /\
    candle_q_box_valid_list outer_boxes /\
    candle_q_packed_source_correspondence
      source_boxes center_boxes outer_boxes radii /\
    candle_q_packed_source_certificate_program_run
      center_boxes sources center_certificates [] (CONS center_item []) [] /\
    candle_q_packed_source_certificate_program_run
      outer_boxes sources outer_certificates [] (CONS outer_item []) [] /\
    candle_analytic_erase_sqrt_certificates
      (candle_q_packed_source_item_box_expr center_item) =
      candle_analytic_erase_sqrt_certificates
        (candle_q_packed_source_item_box_expr outer_item) /\
    candle_q_packed_hessian6_expand packed_hessian =
      candle_q_dim_taylor_model_result_hessian
        (candle_q_packed_source_item_result outer_item) /\
    LENGTH radii = 6 /\
    LENGTH
      (candle_q_dim_taylor_model_result_gradient_bounds
        (candle_q_packed_source_item_result center_item)) = 6 /\
    LENGTH packed_hessian = 21 /\
    candle_q_dim_taylor_model_result_domain
      (candle_q_packed_source_item_result center_item) /\
    candle_q_dim_taylor_model_result_domain
      (candle_q_packed_source_item_result outer_item) /\
    candle_q_real
      (SND
        (candle_q_dim_taylor_model_result_value_bound
          (candle_q_packed_source_certificate_completed_result
            radii center_item outer_item packed_hessian))) < &0`;;

let candle_q_packed_source_certificate_accept_contract_object_accept = prove
 (`!source_boxes center_boxes outer_boxes radii sources
       center_certificates outer_certificates center_item outer_item
       packed_hessian.
     candle_q_packed_source_certificate_accept_contract
       source_boxes center_boxes outer_boxes radii sources
       center_certificates outer_certificates center_item outer_item
       packed_hessian
     ==>
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_dim_taylor_model_result_domain
          (candle_q_packed_source_item_result center_item) /\
        candle_q_dim_taylor_model_result_domain
          (candle_q_packed_source_item_result outer_item))
       (candle_q_dim_taylor_model_result_value_bound
         (candle_q_packed_source_item_result center_item))
       (candle_q_dim_taylor_model_result_gradient_bounds
         (candle_q_packed_source_item_result center_item))
       (candle_q_dim_taylor_model_result_value_bound
         (candle_q_packed_source_item_result outer_item))
       (candle_q_dim_taylor_model_result_gradient_bounds
         (candle_q_packed_source_item_result outer_item))
       packed_hessian
       (candle_q_packed_source_item_box_expr center_item)
       (candle_q_packed_source_item_box_expr outer_item) /\
     (candle_q_dim_taylor_model_result_domain
        (candle_q_packed_source_item_result center_item) /\
      candle_q_dim_taylor_model_result_domain
        (candle_q_packed_source_item_result outer_item)) /\
     candle_q_real
       (SND
         (candle_q_dim_taylor_model_result_value_bound
           (candle_q_packed_source_certificate_completed_result
             radii center_item outer_item packed_hessian))) < &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_certificate_accept_contract_def] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC
      candle_q_packed_source_certificate_programs_object_invariant THEN
    EXISTS_TAC `sources:candle_analytic_instruction list` THEN
    EXISTS_TAC `sources:candle_analytic_instruction list` THEN
    EXISTS_TAC
      `center_certificates:
        (((num#num)#num)#((num#num)#num))list` THEN
    EXISTS_TAC
      `outer_certificates:
        (((num#num)#num)#((num#num)#num))list` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_source_certificate_accept_contract_components = prove
 (`!source_boxes center_boxes outer_boxes radii sources
       center_certificates outer_certificates center_item outer_item
       packed_hessian.
     candle_q_packed_source_certificate_accept_contract
       source_boxes center_boxes outer_boxes radii sources
       center_certificates outer_certificates center_item outer_item
       packed_hessian
     ==>
     LENGTH source_boxes = 6 /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_item_analytic_invariant
       center_boxes outer_boxes
       (candle_q_dim_taylor_model_result_domain
          (candle_q_packed_source_item_result center_item) /\
        candle_q_dim_taylor_model_result_domain
          (candle_q_packed_source_item_result outer_item))
       (candle_q_dim_taylor_model_result_value_bound
         (candle_q_packed_source_item_result center_item))
       (candle_q_dim_taylor_model_result_gradient_bounds
         (candle_q_packed_source_item_result center_item))
       (candle_q_dim_taylor_model_result_value_bound
         (candle_q_packed_source_item_result outer_item))
       (candle_q_dim_taylor_model_result_gradient_bounds
         (candle_q_packed_source_item_result outer_item))
       packed_hessian
       (candle_q_packed_source_item_box_expr center_item)
       (candle_q_packed_source_item_box_expr outer_item) /\
     (candle_q_dim_taylor_model_result_domain
        (candle_q_packed_source_item_result center_item) /\
      candle_q_dim_taylor_model_result_domain
        (candle_q_packed_source_item_result outer_item)) /\
     candle_q_real
       (SND
         (candle_q_dim_taylor_model_result_value_bound
           (candle_q_packed_source_certificate_completed_result
             radii center_item outer_item packed_hessian))) < &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_certificate_accept_contract_def] THEN
  MESON_TAC
    [REWRITE_RULE
      [candle_q_packed_source_certificate_accept_contract_def]
      candle_q_packed_source_certificate_accept_contract_object_accept]);;

let candle_q_packed_source_certificate_accept_contract_cell_pass = prove
 (`!source_boxes center_boxes outer_boxes radii sources
       center_certificates outer_certificates center_item outer_item
       packed_hessian.
     candle_q_packed_source_certificate_accept_contract
       source_boxes center_boxes outer_boxes radii sources
       center_certificates outer_certificates center_item outer_item
       packed_hessian
     ==>
     m_cell_pass
       (candle_analytic_denote_dim
         (candle_q_packed_source_item_box_expr outer_item))
       ((candle_q_box_lower_vector source_boxes:real^6),
        (candle_q_box_upper_vector source_boxes:real^6))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  let components =
    MATCH_MP
      (SPEC_ALL
        candle_q_packed_source_certificate_accept_contract_components)
      (ASSUME
        `candle_q_packed_source_certificate_accept_contract
          source_boxes center_boxes outer_boxes radii sources
          center_certificates outer_certificates center_item outer_item
          packed_hessian`) in
  let source_length,components = CONJ_PAIR components in
  let correspondence,components = CONJ_PAIR components in
  let object_invariant,components = CONJ_PAIR components in
  let domains,negative = CONJ_PAIR components in
  let complete_invariant =
    REWRITE_RULE
      [GSYM candle_q_packed_source_certificate_completed_result_def]
      (MATCH_MP
        (SPEC_ALL candle_q_packed_object_item_complete_analytic_invariant)
        (CONJ source_length (CONJ correspondence object_invariant))) in
  let enabled =
    MATCH_MP
      (REWRITE_RULE
        [candle_q_dim_taylor_model_result_analytic_invariant_def;
         candle_q_packed_source_certificate_completed_result_domain]
        complete_invariant)
      domains in
  let _,enabled = CONJ_PAIR enabled in
  let _,enabled = CONJ_PAIR enabled in
  let _,enabled = CONJ_PAIR enabled in
  let _,enabled = CONJ_PAIR enabled in
  let _,source_contains = CONJ_PAIR enabled in
  REWRITE_TAC[m_cell_pass] THEN
  X_GEN_TAC `p:real^6` THEN DISCH_TAC THEN
  let point_contains =
    MATCH_MP
      (SPEC `p:real^6` source_contains)
      (ASSUME
        `(p:real^6) IN interval
          [candle_q_box_lower_vector source_boxes,
           candle_q_box_upper_vector source_boxes]`) in
  let value_contains =
    MATCH_MP
      (SPEC_ALL candle_q_dim_analytic_contains_denote_value)
      point_contains in
  MP_TAC
    (REWRITE_RULE
      [candle_q_dim_taylor_model_proxy_def;
       candle_q_dim_jet_f_def; candle_q_dim_jet_make_def; FST; SND]
      value_contains) THEN
  REWRITE_TAC[candle_q_interval_contains_def] THEN
  MP_TAC negative THEN REAL_ARITH_TAC);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_source_certificate_completed_result_def;
     candle_q_packed_source_certificate_completed_result_domain;
     candle_q_packed_source_certificate_accept_contract_object_accept;
     candle_q_packed_source_certificate_accept_contract_components;
     candle_q_packed_source_certificate_accept_contract_cell_pass] then
  failwith "packed source certificate entry sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFICATE_ENTRY_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
