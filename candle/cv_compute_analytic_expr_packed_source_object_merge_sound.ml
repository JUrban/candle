(* ========================================================================== *)
(* Merge two ordinary source replays into the six-field packed object.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The center replay supplies a value and first  *)
(* derivative enclosure over the authenticated center box.  The outer replay *)
(* supplies the value, first derivative, and Hessian enclosure over the outer *)
(* box.  This theorem selects those fields without repeating any analytic     *)
(* calculus proof.                                                            *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_program_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_invariant.ml";;

module Candle_cv_analytic_expr_packed_source_object_merge_sound = struct

open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_packed_source_item_invariant;;
open Candle_cv_analytic_expr_packed_source_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;

let candle_q_stack_contains_length = prove
 (`!boxes environment.
     candle_q_stack_contains boxes environment
     ==> LENGTH boxes = LENGTH environment`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_stack_contains_all2] THEN
  MATCH_ACCEPT_TAC candle_all2_length);;

let candle_q_stack_contains_lambda_in_interval = prove
 (`!boxes environment.
     LENGTH boxes = dimindex (:N) /\
     candle_q_stack_contains boxes environment
     ==>
     (lambda i. EL (i - 1) environment):real^N IN
       interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INTERVAL] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_box_lower_vector_def;
              candle_q_box_upper_vector_def] THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM candle_q_interval_contains_def] THEN
  MATCH_MP_TAC candle_q_stack_contains_el_lt THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC (REWRITE_RULE[IN_NUMSEG]) THEN
    SUBGOAL_THEN `1 <= i` ASSUME_TAC THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `i <= dimindex (:N)` ASSUME_TAC THENL
       [ASM_MESON_TAC[];
        SUBGOAL_THEN `(i - 1) + 1 = i` ASSUME_TAC THENL
         [ASM_SIMP_TAC[SUB_ADD];
          REWRITE_TAC[GSYM LE_SUC_LT; ADD1] THEN
          ASM_REWRITE_TAC[]]]]]);;

let candle_q_environment_lambda_list_of_seq = prove
 (`!environment.
     LENGTH environment = dimindex (:N)
     ==>
     environment =
       list_of_seq
         (\k. ((lambda i. EL (i - 1) environment):real^N)$(k + 1))
         (dimindex (:N))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k + 1 IN 1..dimindex (:N)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_NUMSEG] THEN CONJ_TAC THENL
       [MATCH_ACCEPT_TAC LE_ADDR;
        REWRITE_TAC[GSYM ADD1; LE_SUC_LT] THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
      SUBGOAL_THEN
       `((lambda i. EL (i - 1) environment):real^N)$(k + 1) =
        EL ((k + 1) - 1) environment`
      SUBST1_TAC THENL
       [MATCH_MP_TAC LAMBDA_BETA THEN
        UNDISCH_TAC `k + 1 IN 1..dimindex (:N)` THEN
        REWRITE_TAC[IN_NUMSEG];
        REWRITE_TAC[ADD_SUB]]]]);;

let candle_q_stack_contains_vector_witness = prove
 (`!boxes environment.
     LENGTH boxes = dimindex (:N) /\
     candle_q_stack_contains boxes environment
     ==>
     ?z:real^N.
       z IN interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes] /\
       environment =
         list_of_seq (\k. z$(k + 1)) (dimindex (:N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let lengths =
    MATCH_MP
      (ISPECL
        [`boxes:(((num#num)#num)#((num#num)#num))list`;
         `environment:real list`]
        candle_q_stack_contains_length)
      (ASSUME
        `candle_q_stack_contains
          (boxes:(((num#num)#num)#((num#num)#num))list)
          (environment:real list)`) in
  let environment_length =
    TRANS (SYM lengths)
      (ASSUME
        `LENGTH
          (boxes:(((num#num)#num)#((num#num)#num))list) =
         dimindex (:N)`) in
  EXISTS_TAC `(lambda i. EL (i - 1) environment):real^N` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
      (ISPECL
        [`boxes:(((num#num)#num)#((num#num)#num))list`;
         `environment:real list`]
        candle_q_stack_contains_lambda_in_interval) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (ISPEC `environment:real list`
        candle_q_environment_lambda_list_of_seq) THEN
    MATCH_ACCEPT_TAC environment_length]);;

let candle_q_result_proxy_stack_invariant = prove
 (`!boxes result center_e box_e.
     LENGTH boxes = 6 /\
     candle_q_dim_taylor_model_result_analytic_invariant
       (ARB:real^6) boxes result center_e box_e /\
     candle_q_dim_taylor_model_result_domain result
     ==>
     !environment.
       candle_q_stack_contains boxes environment
       ==> candle_analytic_regular_at environment box_e /\
           candle_q_dim_analytic_contains 6
             (candle_q_dim_taylor_model_proxy result)
             environment box_e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "box_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "result_invariant")
        (LABEL_TAC "result_domain"))) THEN
  USE_THEN "result_invariant"
    (fun invariant_th ->
      USE_THEN "result_domain"
        (fun domain_th -> MP_TAC
          (MATCH_MP
            (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
              (REWRITE_RULE
                [candle_q_dim_taylor_model_result_analytic_invariant_def]
                invariant_th))
            domain_th))) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_regular")
      (CONJUNCTS_THEN2 (LABEL_TAC "regular_all")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_shape")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_contains")
            (CONJUNCTS_THEN2 (LABEL_TAC "proxy_shape")
              (LABEL_TAC "proxy_contains")))))) THEN
  X_GEN_TAC `environment:real list` THEN
  DISCH_THEN (LABEL_TAC "environment_contains") THEN
  MP_TAC
    (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
      (ISPECL
        [`boxes:(((num#num)#num)#((num#num)#num))list`;
         `environment:real list`]
        (INST_TYPE [`:6`,`:N`]
          candle_q_stack_contains_vector_witness))) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "box_length" ACCEPT_TAC;
      USE_THEN "environment_contains" ACCEPT_TAC];
    DISCH_THEN
      (X_CHOOSE_THEN `z:real^6`
        (CONJUNCTS_THEN2 (LABEL_TAC "z_in")
          (LABEL_TAC "environment_eq"))) THEN
    USE_THEN "regular_all"
      (fun th ->
        USE_THEN "z_in"
          (fun z_in -> MP_TAC (MATCH_MP (SPEC `z:real^6` th) z_in))) THEN
    DISCH_THEN (LABEL_TAC "regular_at_z") THEN
    USE_THEN "proxy_contains"
      (fun th ->
        USE_THEN "z_in"
          (fun z_in -> MP_TAC (MATCH_MP (SPEC `z:real^6` th) z_in))) THEN
    DISCH_THEN (LABEL_TAC "contains_at_z") THEN
    USE_THEN "environment_eq" SUBST1_TAC THEN
    CONJ_TAC THENL
     [USE_THEN "regular_at_z" ACCEPT_TAC;
      USE_THEN "contains_at_z" ACCEPT_TAC]]);;

let candle_q_result_proxy_center_first_contains = prove
 (`!result environment e.
     candle_q_dim_analytic_contains 6
       (candle_q_dim_taylor_model_proxy result) environment e
     ==>
     candle_q_packed_object_center_first_contains
       (candle_q_dim_taylor_model_result_value_bound result)
       (candle_q_dim_taylor_model_result_gradient_bounds result)
       environment e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_center_first_contains_def;
              candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_dim_taylor_model_proxy_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  MESON_TAC[]);;

let candle_q_packed_source_items_merge_object_invariant = prove
 (`!center_boxes outer_boxes center_item outer_item packed_hessian.
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_item_analytic_invariant
       center_boxes center_item /\
     candle_q_packed_source_item_analytic_invariant
       outer_boxes outer_item /\
     candle_analytic_erase_sqrt_certificates
       (candle_q_packed_source_item_box_expr center_item) =
       candle_analytic_erase_sqrt_certificates
         (candle_q_packed_source_item_box_expr outer_item) /\
     candle_q_packed_hessian6_expand packed_hessian =
       candle_q_dim_taylor_model_result_hessian
         (candle_q_packed_source_item_result outer_item)
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
       (candle_q_packed_source_item_box_expr outer_item)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "outer_length")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_item_invariant")
          (CONJUNCTS_THEN2 (LABEL_TAC "outer_item_invariant")
            (CONJUNCTS_THEN2 (LABEL_TAC "erasure")
              (LABEL_TAC "packed_hessian")))))) THEN
  USE_THEN "center_item_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "center_internal_erasure")
        (LABEL_TAC "center_result_invariant"))) THEN
  USE_THEN "outer_item_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "outer_valid")
      (CONJUNCTS_THEN2 (LABEL_TAC "outer_internal_erasure")
        (LABEL_TAC "outer_result_invariant"))) THEN
  REWRITE_TAC[candle_q_packed_object_item_analytic_invariant_def] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "outer_valid" ACCEPT_TAC;
    USE_THEN "erasure" ACCEPT_TAC;
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "center_domain")
        (LABEL_TAC "outer_domain")) THEN
    USE_THEN "center_result_invariant"
      (fun th ->
        USE_THEN "center_domain"
          (fun domain_th -> MP_TAC
            (MATCH_MP
              (REWRITE_RULE
                [candle_q_dim_taylor_model_result_analytic_invariant_def]
                th)
              domain_th))) THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "center_regular_at_midpoint")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_regular_all")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_jet_shape")
            (CONJUNCTS_THEN2 (LABEL_TAC "center_jet_contains")
              (CONJUNCTS_THEN2 (LABEL_TAC "center_proxy_shape")
                (LABEL_TAC "center_proxy_contains")))))) THEN
    USE_THEN "outer_result_invariant"
      (fun th ->
        USE_THEN "outer_domain"
          (fun domain_th -> MP_TAC
            (MATCH_MP
              (REWRITE_RULE
                [candle_q_dim_taylor_model_result_analytic_invariant_def]
                th)
              domain_th))) THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "outer_regular_at_midpoint")
        (CONJUNCTS_THEN2 (LABEL_TAC "outer_regular_all")
          (CONJUNCTS_THEN2 (LABEL_TAC "outer_jet_shape")
            (CONJUNCTS_THEN2 (LABEL_TAC "outer_jet_contains")
              (CONJUNCTS_THEN2 (LABEL_TAC "outer_proxy_shape")
                (LABEL_TAC "outer_proxy_contains")))))) THEN
    CONJ_TAC THENL
     [USE_THEN "center_proxy_shape" MP_TAC THEN
      CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
      REWRITE_TAC[candle_q_dim_jet_shape_def;
                  candle_q_dim_taylor_model_proxy_def;
                  candle_q_dim_jet_gradient_def;
                  candle_q_dim_jet_make_def; FST; SND] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      CONJ_TAC THENL
       [USE_THEN "outer_proxy_shape" MP_TAC THEN
      CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
      ASM_REWRITE_TAC[candle_q_packed_object_box_jet_def;
                      candle_q_dim_taylor_model_proxy_def;
                      candle_q_dim_jet_make_def;
                      candle_q_dim_jet_hessian_def; FST; SND];
        CONJ_TAC THENL
         [X_GEN_TAC `environment:real list` THEN
          DISCH_THEN (LABEL_TAC "center_environment_contains") THEN
          USE_THEN "center_length"
            (fun length_th ->
              USE_THEN "center_result_invariant"
                (fun invariant_th ->
                  USE_THEN "center_domain"
                    (fun domain_th ->
                      USE_THEN "center_environment_contains"
                        (fun environment_th ->
                          let center_stack =
                            MATCH_MP
                              candle_q_result_proxy_stack_invariant
                              (CONJ length_th
                                (CONJ invariant_th domain_th)) in
                          let center_at_environment =
                            MATCH_MP
                              (SPEC `environment:real list` center_stack)
                              environment_th in
                          let center_regular,center_contains =
                            CONJ_PAIR center_at_environment in
                          CONJ_TAC THENL
                           [MATCH_ACCEPT_TAC center_regular;
                            MATCH_MP_TAC
                              candle_q_result_proxy_center_first_contains THEN
                            MATCH_ACCEPT_TAC center_contains]))));
          X_GEN_TAC `environment:real list` THEN
          DISCH_THEN (LABEL_TAC "outer_environment_contains") THEN
          USE_THEN "outer_length"
            (fun length_th ->
              USE_THEN "outer_result_invariant"
                (fun invariant_th ->
                  USE_THEN "outer_domain"
                    (fun domain_th ->
                      USE_THEN "outer_environment_contains"
                        (fun environment_th ->
                          let outer_stack =
                            MATCH_MP
                              candle_q_result_proxy_stack_invariant
                              (CONJ length_th
                                (CONJ invariant_th domain_th)) in
                          let outer_at_environment =
                            MATCH_MP
                              (SPEC `environment:real list` outer_stack)
                              environment_th in
                          let outer_regular,outer_contains =
                            CONJ_PAIR outer_at_environment in
                          CONJ_TAC THENL
                           [MATCH_ACCEPT_TAC outer_regular;
                            MP_TAC outer_contains THEN
                            ASM_REWRITE_TAC
                              [candle_q_packed_object_box_jet_def;
                               candle_q_dim_taylor_model_proxy_def;
                               candle_q_dim_jet_make_def;
                               candle_q_dim_jet_hessian_def;
                               FST; SND]]))))]]]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_stack_contains_length;
     candle_q_stack_contains_lambda_in_interval;
     candle_q_environment_lambda_list_of_seq;
     candle_q_stack_contains_vector_witness;
     candle_q_result_proxy_stack_invariant;
     candle_q_result_proxy_center_first_contains;
     candle_q_packed_source_items_merge_object_invariant] then
  failwith "packed source object merge sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_MERGE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
