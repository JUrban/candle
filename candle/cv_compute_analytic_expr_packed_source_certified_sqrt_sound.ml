(* ========================================================================== *)
(* Certificate-driven square-root Taylor results for packed source replay.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fast checker supplies separate center    *)
(* and whole-box root/derivative intervals plus one whole-box second-        *)
(* derivative reciprocal.  This file retains those exact supplied intervals *)
(* in the ordinary Taylor result and proves their analytic meaning.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_item_operations_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_sqrt.ml";;

module Candle_cv_analytic_expr_packed_source_certified_sqrt_sound = struct

open Candle_cv_exact_interval_sqrt_certificate;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_domain;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_polynomial_expr_dim_check;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_core;;
open Candle_cv_analytic_expr_packed_source_sqrt;;
open Candle_cv_analytic_expr_packed_source_item_invariant;;
open Candle_cv_analytic_expr_packed_source_item_operations_sound;;

let candle_packed_analytic_sqrt_with_interval_def = new_definition
 `candle_packed_analytic_sqrt_with_interval
      (i:((num#num)#num)#((num#num)#num)) a =
    Candle_analytic_sqrt
      (FST (FST (FST i))) (SND (FST (FST i))) (SND (FST i))
      (FST (FST (SND i))) (SND (FST (SND i))) (SND (SND i)) a`;;

let candle_q_box_center_vector_in_interval = prove
 (`!boxes.
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     (candle_q_box_center_vector boxes : real^N) IN
       interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_INTERVAL] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i IN 1..dimindex (:N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `i - 1 < LENGTH
      (boxes:(((num#num)#num)#((num#num)#num))list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MP_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[candle_q_box_lower_vector_component;
               candle_q_box_upper_vector_component;
               candle_q_box_center_vector_component] THEN
  MP_TAC
    (SPEC
      `EL (i - 1)
        (boxes:(((num#num)#num)#((num#num)#num))list)`
      candle_q_box_midpoint_radius) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC candle_q_box_valid_list_el THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let candle_q_dim_jet_sqrt_first_certificates_value_positive = prove
 (`!input root_interval derivative value.
     candle_q_interval_sqrt_certificate input root_interval /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add_normalized root_interval root_interval)
       derivative /\
     candle_q_interval_contains input value
     ==> &0 < value`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= value` ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_interval_sqrt_certificate_input_nonnegative];
    ALL_TAC] THEN
  SUBGOAL_THEN
     `candle_q_interval_contains root_interval (sqrt value)` ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_interval_sqrt_certificate_sound];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_interval_add_normalized root_interval root_interval)
      (sqrt value + sqrt value)` ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_interval_add_normalized_sound];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(sqrt value + sqrt value = &0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM
      (fun certificate_th ->
        let not_zero_th =
          CONJUNCT1
            (REWRITE_RULE[candle_q_interval_inv_certificate_def]
              certificate_th) in
        MATCH_ACCEPT_TAC
          (MATCH_MP candle_q_interval_not_zero_contains_nonzero
            (CONJ not_zero_th
              (ASSUME
                `candle_q_interval_contains
                  (candle_q_interval_add_normalized
                    root_interval root_interval)
                  (sqrt value + sqrt value)`))));
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt value` ASSUME_TAC THENL
   [MP_TAC (SPEC `value:real` SQRT_POS_LE) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC (SPEC `value:real` SQRT_LT_0) THEN ASM_REWRITE_TAC[]]);;

let candle_q_dim_jet_sqrt_first_certificates_value_positive_curried = prove
 (`!input root_interval derivative value.
     candle_q_interval_sqrt_certificate input root_interval
     ==>
     candle_q_interval_inv_certificate
       (candle_q_interval_add_normalized root_interval root_interval)
       derivative
     ==>
     candle_q_interval_contains input value
     ==>
     &0 < value`,
  MESON_TAC[candle_q_dim_jet_sqrt_first_certificates_value_positive]);;

(* The center state stores only a first jet, but its ordinary representation *)
(* carries an erased Hessian field.  The whole-box second certificate safely  *)
(* supplies that proof-only field while preserving the exact center value and *)
(* gradient intervals produced by the fast checker.                           *)

let candle_q_dim_jet_sqrt_split_certified_components_sound = prove
 (`!n center_root center_derivative box_root box_derivative
      box_second_reciprocal center_jet box_jet value gradient hessian.
     candle_q_dim_jet_shape n center_jet /\
     candle_q_dim_jet_contains_components
       n center_jet value gradient hessian /\
     candle_q_dim_jet_contains_components
       n box_jet value gradient hessian /\
     candle_q_interval_sqrt_certificate
       (candle_q_dim_jet_f center_jet) center_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add_normalized center_root center_root)
       center_derivative /\
     candle_q_dim_jet_sqrt_certificates
       (candle_q_dim_jet_f box_jet) box_root box_derivative
       box_second_reciprocal
     ==>
     candle_q_dim_jet_contains_components n
       (candle_q_dim_jet_unary_with center_root center_derivative
         (candle_q_interval_neg box_second_reciprocal) center_jet)
       (sqrt value)
       (\i. inv (sqrt value + sqrt value) * gradient i)
       (\i j.
          (--inv ((sqrt value + sqrt value) * (value + value))) *
            (gradient i * gradient j) +
          inv (sqrt value + sqrt value) * hessian i j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_sqrt_certificates_def] THEN STRIP_TAC THEN
  let center_input_contains = CONJUNCT1
    (REWRITE_RULE[candle_q_dim_jet_contains_components_def]
      (ASSUME
        `candle_q_dim_jet_contains_components n center_jet
          value gradient hessian`)) in
  let box_input_contains = CONJUNCT1
    (REWRITE_RULE[candle_q_dim_jet_contains_components_def]
      (ASSUME
        `candle_q_dim_jet_contains_components n box_jet
          value gradient hessian`)) in
  let center_root_contains = MATCH_MP
    (ISPECL
      [`candle_q_dim_jet_f center_jet`;
       `center_root:((num#num)#num)#((num#num)#num)`;
       `value:real`]
      candle_q_interval_sqrt_certificate_sound)
    (CONJ
      (ASSUME
        `candle_q_interval_sqrt_certificate
          (candle_q_dim_jet_f center_jet) center_root`)
      center_input_contains) in
  let center_root_twice_contains = MATCH_MP
    (ISPECL
      [`center_root:((num#num)#num)#((num#num)#num)`;
       `center_root:((num#num)#num)#((num#num)#num)`;
       `sqrt value`; `sqrt value`]
      candle_q_interval_add_normalized_sound)
    (CONJ center_root_contains center_root_contains) in
  let center_derivative_contains = MATCH_MP
    (ISPECL
      [`candle_q_interval_add_normalized center_root center_root`;
       `center_derivative:((num#num)#num)#((num#num)#num)`;
       `sqrt value + sqrt value`]
      candle_q_interval_inv_certificate_sound)
    (CONJ
      (ASSUME
        `candle_q_interval_inv_certificate
          (candle_q_interval_add_normalized center_root center_root)
          center_derivative`)
      center_root_twice_contains) in
  let box_root_contains = MATCH_MP
    (ISPECL
      [`candle_q_dim_jet_f box_jet`;
       `box_root:((num#num)#num)#((num#num)#num)`;
       `value:real`]
      candle_q_interval_sqrt_certificate_sound)
    (CONJ
      (ASSUME
        `candle_q_interval_sqrt_certificate
          (candle_q_dim_jet_f box_jet) box_root`)
      box_input_contains) in
  let box_root_twice_contains = MATCH_MP
    (ISPECL
      [`box_root:((num#num)#num)#((num#num)#num)`;
       `box_root:((num#num)#num)#((num#num)#num)`;
       `sqrt value`; `sqrt value`]
      candle_q_interval_add_normalized_sound)
    (CONJ box_root_contains box_root_contains) in
  let box_input_twice_contains = MATCH_MP
    (ISPECL
      [`candle_q_dim_jet_f box_jet`; `candle_q_dim_jet_f box_jet`;
       `value:real`; `value:real`]
      candle_q_interval_add_normalized_sound)
    (CONJ box_input_contains box_input_contains) in
  let box_denominator_contains = MATCH_MP
    (ISPECL
      [`candle_q_interval_add_normalized box_root box_root`;
       `candle_q_interval_add_normalized
          (candle_q_dim_jet_f box_jet) (candle_q_dim_jet_f box_jet)`;
       `sqrt value + sqrt value`; `value + value`]
      candle_q_interval_mul_normalized_sound)
    (CONJ box_root_twice_contains box_input_twice_contains) in
  let box_second_contains = MATCH_MP
    (ISPECL
      [`candle_q_interval_mul_normalized
          (candle_q_interval_add_normalized box_root box_root)
          (candle_q_interval_add_normalized
            (candle_q_dim_jet_f box_jet) (candle_q_dim_jet_f box_jet))`;
       `box_second_reciprocal:((num#num)#num)#((num#num)#num)`;
       `(sqrt value + sqrt value) * (value + value)`]
      candle_q_interval_inv_certificate_sound)
    (CONJ
      (ASSUME
        `candle_q_interval_inv_certificate
          (candle_q_interval_mul_normalized
            (candle_q_interval_add_normalized box_root box_root)
            (candle_q_interval_add_normalized
              (candle_q_dim_jet_f box_jet)
              (candle_q_dim_jet_f box_jet)))
          box_second_reciprocal`)
      box_denominator_contains) in
  let box_second_neg_contains = MATCH_MP
    (ISPECL
      [`box_second_reciprocal:((num#num)#num)#((num#num)#num)`;
       `inv ((sqrt value + sqrt value) * (value + value))`]
      candle_q_interval_neg_sound)
    box_second_contains in
  let unary_th = MATCH_MP
    (ISPECL
      [`n:num`;
       `center_root:((num#num)#num)#((num#num)#num)`;
       `center_derivative:((num#num)#num)#((num#num)#num)`;
       `candle_q_interval_neg box_second_reciprocal`;
       `center_jet:((((num#num)#num)#((num#num)#num))#
             ((((num#num)#num)#((num#num)#num))list)#
             ((((num#num)#num)#((num#num)#num))list)list)`;
       `value:real`; `gradient:num->real`; `hessian:num->num->real`;
       `sqrt value`; `inv (sqrt value + sqrt value)`;
       `--inv ((sqrt value + sqrt value) * (value + value))`]
      candle_q_dim_jet_unary_with_components_sound)
    (end_itlist CONJ
      [ASSUME `candle_q_dim_jet_shape n center_jet`;
       ASSUME
        `candle_q_dim_jet_contains_components n center_jet
          value gradient hessian`;
       center_root_contains; center_derivative_contains;
       box_second_neg_contains]) in
  ACCEPT_TAC (REWRITE_RULE[GSYM REAL_MUL_ASSOC] unary_th));;

let candle_q_dim_taylor_model_result_sqrt_certified_def = new_definition
 `candle_q_dim_taylor_model_result_sqrt_certified radii
      center_root box_root center_derivative box_derivative
      box_second_reciprocal result =
    candle_q_dim_taylor_model_result_complete radii
      (candle_q_dim_taylor_model_result_domain result)
      (candle_q_dim_jet_unary_with center_root center_derivative
        (candle_q_interval_neg box_second_reciprocal)
        (candle_q_dim_taylor_model_result_center result))
      (candle_q_dim_jet_hessian
        (candle_q_dim_jet_sqrt_certified box_root box_derivative
          box_second_reciprocal
          (candle_q_dim_taylor_model_proxy result)))`;;

let candle_q_dim_taylor_model_result_sqrt_certified_analytic_invariant = prove
 (`!center_e box_e boxes result center_root box_root center_derivative
      box_derivative box_second_reciprocal (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes result center_e box_e /\
     candle_q_interval_sqrt_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center result)) center_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add_normalized center_root center_root)
       center_derivative /\
     candle_q_dim_jet_sqrt_certificates
       (candle_q_dim_jet_f (candle_q_dim_taylor_model_proxy result))
       box_root box_derivative box_second_reciprocal
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_sqrt_certified
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         center_root box_root center_derivative box_derivative
         box_second_reciprocal result)
       (candle_packed_analytic_sqrt_with_interval center_root center_e)
       (candle_packed_analytic_sqrt_with_interval box_root box_e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "erasure_equal")
        (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 (LABEL_TAC "input_invariant")
              (CONJUNCTS_THEN2 (LABEL_TAC "center_root_certificate")
                (CONJUNCTS_THEN2
                  (LABEL_TAC "center_derivative_certificate")
                  (LABEL_TAC "box_certificates")))))))) THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_sqrt_certified_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                    candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                    candle_analytic_erase_sqrt_certificates_def];
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
    let center_point =
      `candle_q_box_center_vector boxes:real^N` in
    SUBGOAL_THEN
      `(candle_q_box_center_vector boxes : real^N) IN
        interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]`
      (LABEL_TAC "center_point_in_box") THENL
     [MATCH_MP_TAC candle_q_box_center_vector_in_interval THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    let center_point_in_box =
      ASSUME
        `(candle_q_box_center_vector boxes : real^N) IN
          interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]` in
    USE_THEN "box_contains_all" (fun th ->
      LABEL_TAC "proxy_contains_center"
        (MP (SPEC center_point th) center_point_in_box)) THEN
    USE_THEN "proxy_contains_center" (fun proxy_contains_box_e ->
      let proxy_contains_erased_box =
        ONCE_REWRITE_RULE
          [GSYM candle_q_dim_analytic_contains_erase]
          proxy_contains_box_e in
      USE_THEN "erasure_equal" (fun erasure_equal ->
        let proxy_contains_erased_center =
          SUBS [SYM erasure_equal] proxy_contains_erased_box in
        let proxy_contains_center_e =
          ONCE_REWRITE_RULE
            [candle_q_dim_analytic_contains_erase]
            proxy_contains_erased_center in
        LABEL_TAC "proxy_contains_center_e" proxy_contains_center_e)) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                  candle_analytic_regular_at_def] THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "center_contains" (fun center_contains_center_e ->
          let center_input_contains = CONJUNCT1
            (REWRITE_RULE[candle_q_dim_analytic_contains_def;
                          candle_q_dim_jet_contains_components_def]
              center_contains_center_e) in
          USE_THEN "center_root_certificate" (fun root_th ->
            USE_THEN "center_derivative_certificate" (fun derivative_th ->
              let root_application,root_term = dest_comb (concl root_th) in
              let _,input_term = dest_comb root_application in
              let _,derivative_term = dest_comb (concl derivative_th) in
              let _,value_term = dest_comb (concl center_input_contains) in
              let positive_rule = SPECL
                [input_term; root_term; derivative_term; value_term]
                candle_q_dim_jet_sqrt_first_certificates_value_positive_curried in
              let positive_th =
                MP (MP (MP positive_rule root_th) derivative_th)
                  center_input_contains in
              MATCH_ACCEPT_TAC positive_th)))];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `p:real^N` THEN
      DISCH_THEN (LABEL_TAC "box_regular_p_in_box") THEN
      REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                  candle_analytic_regular_at_def] THEN
      CONJ_TAC THENL
       [USE_THEN "box_regular" (fun th ->
          USE_THEN "box_regular_p_in_box" (fun p_in_box ->
            ACCEPT_TAC (MP (SPEC `p:real^N` th) p_in_box)));
        USE_THEN "box_contains_all" (fun th ->
          USE_THEN "box_regular_p_in_box" (fun p_in_box ->
            let contains_at_p = MP (SPEC `p:real^N` th) p_in_box in
            let input_contains = CONJUNCT1
              (REWRITE_RULE[candle_q_dim_analytic_contains_def;
                            candle_q_dim_jet_contains_components_def]
                contains_at_p) in
            USE_THEN "box_certificates" (fun box_certificates_th ->
              let expanded =
                REWRITE_RULE[candle_q_dim_jet_sqrt_certificates_def]
                  box_certificates_th in
              let box_root_th,remaining = CONJ_PAIR expanded in
              let box_derivative_th,_ = CONJ_PAIR remaining in
              let root_application,root_term = dest_comb (concl box_root_th) in
              let _,input_term = dest_comb root_application in
              let _,derivative_term = dest_comb (concl box_derivative_th) in
              let _,value_term = dest_comb (concl input_contains) in
              let positive_rule = SPECL
                [input_term; root_term; derivative_term; value_term]
                candle_q_dim_jet_sqrt_first_certificates_value_positive_curried in
              let positive_th =
                MP (MP (MP positive_rule box_root_th) box_derivative_th)
                  input_contains in
              MATCH_ACCEPT_TAC positive_th)))];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_jet_unary_with_shape THEN
      USE_THEN "center_shape" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "center_contains" (fun center_contains_center_e ->
        USE_THEN "proxy_contains_center_e" (fun proxy_contains_center_e ->
          let center_components =
            REWRITE_RULE[candle_q_dim_analytic_contains_def]
              center_contains_center_e in
          let proxy_components =
            REWRITE_RULE[candle_q_dim_analytic_contains_def]
              proxy_contains_center_e in
          let proxy_application,_ = dest_comb (concl proxy_components) in
          let proxy_application,_ = dest_comb proxy_application in
          let proxy_application,_ = dest_comb proxy_application in
          let _,proxy_jet = dest_comb proxy_application in
          REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                      candle_q_dim_analytic_contains_def;
                      candle_analytic_value_def;
                      candle_analytic_d_def;
                      candle_analytic_dd_def] THEN
          MATCH_MP_TAC candle_q_dim_jet_sqrt_split_certified_components_sound THEN
          ASM_REWRITE_TAC[] THEN
          MAP_EVERY EXISTS_TAC
            [`box_root:((num#num)#num)#((num#num)#num)`;
             `box_derivative:((num#num)#num)#((num#num)#num)`] THEN
          EXISTS_TAC proxy_jet THEN
          REPEAT CONJ_TAC THENL
           [MATCH_ACCEPT_TAC center_components;
            MATCH_ACCEPT_TAC proxy_components;
            USE_THEN "box_certificates" MATCH_ACCEPT_TAC]));
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_q_dim_jet_sqrt_certified_def] THEN
      MATCH_MP_TAC candle_q_dim_jet_unary_with_shape THEN
      USE_THEN "proxy_shape" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `p:real^N` THEN
    DISCH_THEN (LABEL_TAC "final_p_in_box") THEN
    USE_THEN "box_contains_all" (fun th ->
      USE_THEN "final_p_in_box" (fun p_in_box ->
        let contains_at_p = MP (SPEC `p:real^N` th) p_in_box in
        REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                    candle_q_dim_analytic_contains_def;
                    candle_analytic_value_def;
                    candle_analytic_d_def;
                    candle_analytic_dd_def] THEN
        MATCH_MP_TAC candle_q_dim_jet_sqrt_certified_components_sound THEN
        REPEAT CONJ_TAC THENL
         [USE_THEN "proxy_shape" MATCH_ACCEPT_TAC;
          USE_THEN "box_certificates" MATCH_ACCEPT_TAC;
          MATCH_ACCEPT_TAC
            (REWRITE_RULE[candle_q_dim_analytic_contains_def]
              contains_at_p)]))]);;

let candle_q_packed_source_item_sqrt_certified_def = new_definition
 `candle_q_packed_source_item_sqrt_certified
      boxes center_root box_root center_derivative box_derivative
      box_second_reciprocal item =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_result_sqrt_certified
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        center_root box_root center_derivative box_derivative
        box_second_reciprocal
        (candle_q_packed_source_item_result item))
      (candle_packed_analytic_sqrt_with_interval center_root
        (candle_q_packed_source_item_center_expr item))
      (candle_packed_analytic_sqrt_with_interval box_root
        (candle_q_packed_source_item_box_expr item))`;;

let candle_q_packed_source_item_sqrt_certified_analytic_invariant = prove
 (`!boxes center_root box_root center_derivative box_derivative
      box_second_reciprocal item.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_item_analytic_invariant boxes item /\
     candle_q_interval_sqrt_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item))) center_root /\
     candle_q_interval_inv_certificate
       (candle_q_interval_add_normalized center_root center_root)
       center_derivative /\
     candle_q_dim_jet_sqrt_certificates
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_proxy
           (candle_q_packed_source_item_result item)))
       box_root box_derivative box_second_reciprocal
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_item_sqrt_certified
         boxes center_root box_root center_derivative box_derivative
         box_second_reciprocal item)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "item_invariant")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_root_certificate")
            (CONJUNCTS_THEN2 (LABEL_TAC "center_derivative_certificate")
              (LABEL_TAC "box_certificates")))))) THEN
  USE_THEN "item_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_source_item_result_def;
                  candle_q_packed_source_item_center_expr_def;
                  candle_q_packed_source_item_box_expr_def]) THEN
  REWRITE_TAC[candle_q_packed_source_item_sqrt_certified_def;
              candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                    candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_packed_analytic_sqrt_with_interval_def;
                    candle_analytic_erase_sqrt_certificates_def];
    MATCH_MP_TAC
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (INST_TYPE [`:6`,`:N`]
          candle_q_dim_taylor_model_result_sqrt_certified_analytic_invariant)) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "center_root_certificate" MATCH_ACCEPT_TAC;
      USE_THEN "center_derivative_certificate" MATCH_ACCEPT_TAC;
      USE_THEN "box_certificates" MATCH_ACCEPT_TAC]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_box_center_vector_in_interval;
     candle_q_dim_jet_sqrt_first_certificates_value_positive;
     candle_q_dim_jet_sqrt_split_certified_components_sound;
     candle_q_dim_taylor_model_result_sqrt_certified_analytic_invariant;
     candle_q_packed_source_item_sqrt_certified_analytic_invariant] then
  failwith "packed source certified sqrt: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFIED_SQRT_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
