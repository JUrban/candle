(* ========================================================================== *)
(* Case-10173 historical splice: checked production-to-analytic contract.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_sound.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_program_analytic_sound.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_first_order_reference_sound.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_optimized_production_jet_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_production_contract_sound = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_hessian;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_dim_check;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_first_order_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_first_order_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_correspondence_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_assembler_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_production_hessian_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_production_jet_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_certificate_compute;;
open Candle_cv_analytic_expr_case10173_historical_source_polynomials_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_jet_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_dihedral_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_contains_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_item_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_invariant;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_analytic_sound;;

let candle_contract_rewrite_with_equalities equalities theorem =
  itlist PROVE_HYP equalities
    (REWRITE_RULE (map GSYM equalities) theorem);;

let candle_contract_match_conjunctive_rule theorem : tactic =
  ASSUM_LIST
    (fun assumptions goal ->
      let premise,_ = dest_imp (concl theorem) in
      let rec build term =
        if is_conj term then
          let left,right = dest_conj term in
          CONJ (build left) (build right)
        else
          find (fun assumption -> aconv (concl assumption) term) assumptions in
      ACCEPT_TAC (MP theorem (build premise)) goal);;

let candle_fs_hist_positive_interval_components = prove
 (`!value.
     candle_fs_hist_positive_interval value
     ==>
     value = ((FST (FST value),0),(FST (SND value),0)) /\
     0 < FST (FST value) /\
     FST (FST value) <= FST (SND value)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_positive_interval_def; FST; SND] THEN
  MESON_TAC[]);;

let candle_fs_hist_positive_root_certificate_input_interval = prove
 (`!input root_value.
     candle_fs_hist_positive_root_certificate input root_value
     ==> candle_fs_hist_positive_interval input`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_positive_root_certificate_def;
              candle_fs_hist_positive_interval_def;
              candle_fs_hist_root_certificate_def; FST; SND] THEN
  MESON_TAC[]);;

let candle_fs_hist_positive_root_certificate_root_interval = prove
 (`!input root_value.
     candle_fs_hist_positive_root_certificate input root_value
     ==> candle_fs_hist_positive_interval root_value`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_positive_root_certificate_def;
              candle_fs_hist_positive_interval_def;
              candle_fs_hist_root_certificate_def; FST; SND] THEN
  MESON_TAC[]);;

let candle_fs_hist_positive_interval_contains_positive_components = prove
 (`!lower lower_neg upper upper_neg x.
     candle_fs_hist_positive_interval
       ((lower,lower_neg),(upper,upper_neg)) /\
     candle_fs_interval_contains
       ((lower,lower_neg),(upper,upper_neg)) x
     ==> &0 < x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_positive_interval_def;
              candle_fs_interval_contains_def;
              candle_fs_real_def; candle_lc_zreal_def;
              FST; SND; REAL_SUB_RZERO] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(candle_fs_scale)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT; candle_fs_scale_pos];
    SUBGOAL_THEN `&0 < &lower / &(candle_fs_scale)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT];
      SUBGOAL_THEN
       `(&lower - &lower_neg) / &(candle_fs_scale) =
        &lower / &(candle_fs_scale)`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_SUB_RZERO];
        ASM_REAL_ARITH_TAC]]]);;

let candle_fs_hist_positive_interval_contains_positive = prove
 (`!value x.
     candle_fs_hist_positive_interval value /\
     candle_fs_interval_contains value x
     ==> &0 < x`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC
    candle_fs_hist_positive_interval_contains_positive_components);;

let candle_fs_hist_positive_components_tac value premise =
  let components =
    MATCH_MP
      (SPEC value candle_fs_hist_positive_interval_components)
      (ASSUME premise) in
  ASSUME_TAC (CONJUNCT1 components) THEN
  ASSUME_TAC (CONJUNCT1 (CONJUNCT2 components)) THEN
  ASSUME_TAC (CONJUNCT2 (CONJUNCT2 components));;

let candle_fs_hist_environment_nonnegative_tac environment premise =
  MAP_EVERY ASSUME_TAC
    (CONJUNCTS
      (EQ_MP
        (SPEC environment candle_fs_hist_environment_nonnegative_def)
        (ASSUME premise)));;

let candle_fs_hist_scale_four_root_input_positive = prove
 (`!value root_value.
     candle_fs_hist_positive_root_certificate
       (candle_fs_angle_interval_scale 4 value) root_value
     ==> candle_fs_hist_positive_interval value`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_positive_root_certificate_def;
              candle_fs_hist_root_certificate_def;
              candle_fs_hist_positive_interval_def;
              candle_fs_angle_interval_scale_def;
              candle_lc_zscale_def; FST; SND] THEN
  STRIP_TAC THEN ASM_ARITH_TAC);;

(* Normalize only the enclosing checker call.  Rewriting the root variable
   itself is cyclic because the normalized endpoint expression still refers
   to its projections. *)

let candle_fs_hist_first_order_direct_positive_normalize = prove
 (`!environment root_delta root_four_x0.
     candle_fs_hist_positive_interval root_delta /\
     candle_fs_hist_positive_interval root_four_x0
     ==>
     candle_fs_hist_first_order_direct environment root_delta root_four_x0 =
     candle_fs_hist_first_order_direct environment
       ((FST (FST root_delta),0),(FST (SND root_delta),0))
       ((FST (FST root_four_x0),0),(FST (SND root_four_x0),0))`,
  MESON_TAC[candle_fs_hist_positive_interval_components]);;

let candle_fs_hist_second_order_positive_normalize = prove
 (`!environment root_delta root_four_x0.
     candle_fs_hist_positive_interval root_delta /\
     candle_fs_hist_positive_interval root_four_x0
     ==>
     candle_fs_hist_second_order environment root_delta root_four_x0 =
     candle_fs_hist_second_order environment
       ((FST (FST root_delta),0),(FST (SND root_delta),0))
       ((FST (FST root_four_x0),0),(FST (SND root_four_x0),0))`,
  MESON_TAC[candle_fs_hist_positive_interval_components]);;

let candle_fs_hist_first_order_reference_gradient_positive_normalize = prove
 (`!environment values root_delta root_four_x0.
     candle_fs_hist_positive_interval root_delta
     ==>
     candle_fs_hist_positive_interval root_four_x0
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient
         (candle_fs_hist_first_order_direct environment
           ((FST (FST (root_delta:((num#num)#(num#num)))),0),
            (FST (SND root_delta),0))
           ((FST (FST (root_four_x0:((num#num)#(num#num)))),0),
            (FST (SND root_four_x0),0))))
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_reference_dihedral_real_jet values)) 6)
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient
         (candle_fs_hist_first_order_direct
           environment root_delta root_four_x0))
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_reference_dihedral_real_jet values)) 6)`,
  MESON_TAC[candle_fs_hist_first_order_direct_positive_normalize]);;

let candle_fs_hist_second_order_reference_hessian_positive_normalize = prove
 (`!environment values root_delta root_four_x0.
     candle_fs_hist_positive_interval root_delta
     ==>
     candle_fs_hist_positive_interval root_four_x0
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_second_order environment
           ((FST (FST root_delta),0),(FST (SND root_delta),0))
           ((FST (FST root_four_x0),0),(FST (SND root_four_x0),0))))
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_reference_dihedral_real_jet values) i) 6) 6)
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_second_order
           environment root_delta root_four_x0))
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_reference_dihedral_real_jet values) i) 6) 6)`,
  MESON_TAC[candle_fs_hist_second_order_positive_normalize]);;

(* Positivity certified by the checked roots is also exactly what makes the
   source sqrt and the following reciprocal regular.  This lemma is uniform
   in the six certificate integers: they affect checking, not denotation. *)

let candle_case10173_hist_source_dihedral_regular = prove
 (`!values lp ln ld up un ud.
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values
     ==>
     candle_analytic_regular_at (list_of_seq values 6)
       (candle_case10173_hist_source_dihedral_expr
         lp ln ld up un ud)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_case10173_hist_source_dihedral_expr_def;
              candle_case10173_hist_source_numerator_expr_def;
              candle_case10173_hist_source_radical_expr_def;
              candle_analytic_regular_at_def;
              candle_analytic_value_def] THEN
  SUBGOAL_THEN
   `&0 < candle_analytic_value (list_of_seq (values:num->real) 6)
      candle_case10173_hist_source_radical_expr`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[candle_case10173_hist_source_radical_value] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC
      (REWRITE_RULE[candle_case10173_hist_source_radical_expr_def;
                    candle_analytic_value_def]) THEN
    ASM_REWRITE_TAC[candle_case10173_hist_source_radical_expr_def;
                    candle_analytic_value_def] THEN
    ASM_SIMP_TAC[SQRT_EQ_0] THEN ASM_REAL_ARITH_TAC]);;

let candle_case10173_hist_first_order_direct_gradient_length = prove
 (`!environment root_delta root_four_x0.
     LENGTH
       (candle_fs_first_gradient
         (candle_fs_hist_first_order_direct
           environment root_delta root_four_x0)) = 6`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_hist_first_order_direct_def;
              candle_fs_first_gradient_def;
              candle_fs_first_make_def;
              LET_DEF; LET_END_DEF; FST; SND] THEN
  MATCH_ACCEPT_TAC candle_fs_hist_result_gradient_length);;

let candle_case10173_q_box_stack_contains_centers = prove
 (`!boxes.
     candle_q_box_valid_list boxes
     ==>
     candle_q_stack_contains boxes
       (MAP (\box. candle_q_real (candle_q_midpoint box)) boxes)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_box_valid_list_def;
                  candle_q_stack_contains_def; MAP] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC (SPEC
      `h:(((num#num)#num)#((num#num)#num))`
      candle_q_box_midpoint_radius) THEN
    ASM_REWRITE_TAC[candle_q_interval_contains_def] THEN MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let candle_case10173_fs_box_contains_center_six = prove
 (`!boxes.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes
     ==>
     ALL2 candle_fs_interval_contains
       (candle_fs_interval_list_of_q boxes)
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^6)$(k + 1)) 6)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_fs_interval_list_of_q_contains THEN
  MP_TAC (SPEC
    `boxes:(((num#num)#num)#((num#num)#num))list`
    candle_case10173_q_box_stack_contains_centers) THEN
  ASM_SIMP_TAC[GSYM candle_case10173_q_box_center_vector_list_six]);;

let candle_case10173_q_box_center_in_interval_six = prove
 (`!boxes.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes
     ==>
     (candle_q_box_center_vector boxes : real^6) IN
       interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_INTERVAL] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i IN 1..dimindex (:6)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `i - 1 < LENGTH
      (boxes:(((num#num)#num)#((num#num)#num))list)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MP_TAC THEN
    CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
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

(* Package the center-value and center-gradient obligations at the natural
   interval level used by the checked guard.  Endpoint normalization is
   derived here once rather than repeated by every genuine leaf. *)

let candle_case10173_hist_first_order_reference_contains = prove
 (`!environment values root_delta root_four_x0.
     LENGTH environment = 6 /\
     ALL2 candle_fs_interval_contains environment
       (list_of_seq values 6) /\
     candle_fs_hist_positive_interval root_delta /\
     candle_fs_hist_positive_interval root_four_x0 /\
     candle_fs_hist_positive_product root_delta root_four_x0 /\
     candle_fs_interval_contains root_delta
       (sqrt (candle_fs_hist_delta_real values)) /\
     candle_fs_interval_contains root_four_x0
       (sqrt (candle_fs_hist_four_x0_real values)) /\
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     candle_fs_hist_positive_interval
       (FST (candle_fs_hist_u126 environment)) /\
     candle_fs_hist_positive_interval
       (FST (candle_fs_hist_u135 environment)) /\
     candle_fs_hist_positive_product
       (FST (candle_fs_hist_u126 environment))
       (FST (candle_fs_hist_u135 environment)) /\
     candle_fs_hist_unit_interval
       (candle_fs_hist_quotient
         (candle_fs_hist_delta_x4_value_direct environment)
         root_delta root_four_x0) /\
     candle_fs_hist_environment_nonnegative environment
     ==>
     candle_fs_interval_contains
       (candle_fs_first_value
         (candle_fs_hist_first_order_direct
           environment root_delta root_four_x0))
       (candle_hist_real_jet_value
         (candle_fs_hist_reference_dihedral_real_jet values)) /\
     ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient
         (candle_fs_hist_first_order_direct
           environment root_delta root_four_x0))
       (list_of_seq
         (candle_hist_real_jet_gradient
           (candle_fs_hist_reference_dihedral_real_jet values)) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  candle_fs_hist_environment_nonnegative_tac
    `environment:((num#num)#(num#num))list`
    `candle_fs_hist_environment_nonnegative environment` THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains (FST (candle_fs_hist_u126 environment))
      (candle_fs_hist_u126_real (values:num->real))`
  (LABEL_TAC "u126_contains") THENL
   [MATCH_MP_TAC candle_fs_hist_u126_value_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains (FST (candle_fs_hist_u135 environment))
      (candle_fs_hist_u135_real (values:num->real))`
  (LABEL_TAC "u135_contains") THENL
   [MATCH_MP_TAC candle_fs_hist_u135_value_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  candle_fs_hist_positive_components_tac
    `root_delta:((num#num)#(num#num))`
    `candle_fs_hist_positive_interval root_delta` THEN
  candle_fs_hist_positive_components_tac
    `root_four_x0:((num#num)#(num#num))`
    `candle_fs_hist_positive_interval root_four_x0` THEN
  candle_fs_hist_positive_components_tac
    `FST (candle_fs_hist_u126 environment)`
    `candle_fs_hist_positive_interval
      (FST (candle_fs_hist_u126 environment))` THEN
  candle_fs_hist_positive_components_tac
    `FST (candle_fs_hist_u135 environment)`
    `candle_fs_hist_positive_interval
      (FST (candle_fs_hist_u135 environment))` THEN
  SUBGOAL_THEN
   `0 <
      (FST (FST (FST (candle_fs_hist_u126 environment))) *
       FST (FST (FST (candle_fs_hist_u135 environment)))) DIV
      candle_fs_scale`
  ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC
      (REWRITE_RULE[candle_fs_hist_positive_product_def]
        (ASSUME
          `candle_fs_hist_positive_product
            (FST (candle_fs_hist_u126 environment))
            (FST (candle_fs_hist_u135 environment))`));
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
      (candle_contract_rewrite_with_equalities
        [(ASSUME
          `(root_delta:((num#num)#(num#num))) =
           ((FST (FST root_delta),0),(FST (SND root_delta),0))`);
         (ASSUME
          `(root_four_x0:((num#num)#(num#num))) =
           ((FST (FST root_four_x0),0),(FST (SND root_four_x0),0))`)]
        (SPECL
          [`environment:((num#num)#(num#num))list`; `values:num->real`;
           `FST (FST (root_delta:((num#num)#(num#num)))):num`;
           `FST (SND (root_delta:((num#num)#(num#num)))):num`;
           `FST (FST (root_four_x0:((num#num)#(num#num)))):num`;
           `FST (SND (root_four_x0:((num#num)#(num#num)))):num`]
          candle_fs_hist_first_order_direct_reference_value_contains)) THEN
    ASM_MESON_TAC[candle_fs_hist_positive_product_def;
                  candle_fs_hist_unit_interval_def];
    candle_contract_match_conjunctive_rule
      (candle_contract_rewrite_with_equalities
        [(ASSUME
          `(root_delta:((num#num)#(num#num))) =
           ((FST (FST root_delta),0),(FST (SND root_delta),0))`);
         (ASSUME
          `(root_four_x0:((num#num)#(num#num))) =
           ((FST (FST root_four_x0),0),(FST (SND root_four_x0),0))`)]
        (SPECL
          [`environment:((num#num)#(num#num))list`; `values:num->real`;
           `FST (FST (root_delta:((num#num)#(num#num)))):num`;
           `FST (SND (root_delta:((num#num)#(num#num)))):num`;
           `FST (FST (root_four_x0:((num#num)#(num#num)))):num`;
           `FST (SND (root_four_x0:((num#num)#(num#num)))):num`;
           `FST (FST (FST (candle_fs_hist_u126 environment))):num`;
           `FST (SND (FST (candle_fs_hist_u126 environment))):num`;
           `FST (FST (FST (candle_fs_hist_u135 environment))):num`;
          `FST (SND (FST (candle_fs_hist_u135 environment))):num`]
          candle_fs_hist_first_order_direct_reference_gradient_contains))]);;

let candle_case10173_hist_second_order_reference_hessian_contains = prove
 (`!boxes values root_delta root_four_x0.
     LENGTH boxes = 6 /\
     ALL2 candle_fs_interval_contains boxes
       (list_of_seq values 6) /\
     candle_fs_hist_positive_interval
       (candle_fs_hist_second_value
         (candle_fs_hist_delta_second boxes)) /\
     candle_fs_hist_positive_interval root_delta /\
     candle_fs_hist_positive_interval root_four_x0 /\
     candle_fs_hist_positive_product root_delta root_four_x0 /\
     candle_fs_interval_contains root_delta
       (sqrt (candle_fs_hist_delta_real values)) /\
     candle_fs_interval_contains root_four_x0
       (sqrt (candle_fs_hist_four_x0_real values)) /\
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values /\
     candle_fs_hist_positive_interval
       (candle_fs_interval_lookup 0 boxes) /\
     candle_fs_hist_positive_interval
       (FST (candle_fs_hist_u126 boxes)) /\
     candle_fs_hist_positive_interval
       (FST (candle_fs_hist_u135 boxes)) /\
     candle_fs_hist_positive_product
       (FST (candle_fs_hist_u126 boxes))
       (FST (candle_fs_hist_u135 boxes)) /\
     candle_fs_hist_unit_interval
       (candle_fs_hist_quotient
         (candle_fs_hist_second_value
           (candle_fs_hist_delta_x4_second boxes))
         root_delta root_four_x0) /\
     candle_fs_hist_environment_nonnegative boxes
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fs_hist_second_hessian
         (candle_fs_hist_second_order boxes root_delta root_four_x0))
       (list_of_seq
         (\i. list_of_seq
           (candle_hist_real_jet_hessian
             (candle_fs_hist_reference_dihedral_real_jet values) i) 6) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  candle_fs_hist_environment_nonnegative_tac
    `boxes:((num#num)#(num#num))list`
    `candle_fs_hist_environment_nonnegative boxes` THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains (FST (candle_fs_hist_u126 boxes))
      (candle_fs_hist_u126_real (values:num->real))`
  (LABEL_TAC "u126_contains") THENL
   [MATCH_MP_TAC candle_fs_hist_u126_value_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains (FST (candle_fs_hist_u135 boxes))
      (candle_fs_hist_u135_real (values:num->real))`
  (LABEL_TAC "u135_contains") THENL
   [MATCH_MP_TAC candle_fs_hist_u135_value_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC
    (MATCH_MP (REAL_ARITH `&0 < x ==> ~(x = &0)`)
      (MATCH_MP
        (SPECL
          [`FST (candle_fs_hist_u126
              (boxes:((num#num)#(num#num))list))`;
           `candle_fs_hist_u126_real (values:num->real)`]
          candle_fs_hist_positive_interval_contains_positive)
        (CONJ
          (ASSUME
            `candle_fs_hist_positive_interval
              (FST (candle_fs_hist_u126 boxes))`)
          (ASSUME
            `candle_fs_interval_contains
              (FST (candle_fs_hist_u126 boxes))
              (candle_fs_hist_u126_real values)`)))) THEN
  ASSUME_TAC
    (MATCH_MP (REAL_ARITH `&0 < x ==> ~(x = &0)`)
      (MATCH_MP
        (SPECL
          [`FST (candle_fs_hist_u135
              (boxes:((num#num)#(num#num))list))`;
           `candle_fs_hist_u135_real (values:num->real)`]
          candle_fs_hist_positive_interval_contains_positive)
        (CONJ
          (ASSUME
            `candle_fs_hist_positive_interval
              (FST (candle_fs_hist_u135 boxes))`)
          (ASSUME
            `candle_fs_interval_contains
              (FST (candle_fs_hist_u135 boxes))
              (candle_fs_hist_u135_real values)`)))) THEN
  candle_fs_hist_positive_components_tac
    `candle_fs_hist_second_value (candle_fs_hist_delta_second boxes)`
    `candle_fs_hist_positive_interval
      (candle_fs_hist_second_value
        (candle_fs_hist_delta_second boxes))` THEN
  candle_fs_hist_positive_components_tac
    `root_delta:((num#num)#(num#num))`
    `candle_fs_hist_positive_interval root_delta` THEN
  candle_fs_hist_positive_components_tac
    `root_four_x0:((num#num)#(num#num))`
    `candle_fs_hist_positive_interval root_four_x0` THEN
  candle_fs_hist_positive_components_tac
    `candle_fs_interval_lookup 0 boxes`
    `candle_fs_hist_positive_interval
      (candle_fs_interval_lookup 0 boxes)` THEN
  candle_fs_hist_positive_components_tac
    `FST (candle_fs_hist_u126 boxes)`
    `candle_fs_hist_positive_interval
      (FST (candle_fs_hist_u126 boxes))` THEN
  candle_fs_hist_positive_components_tac
    `FST (candle_fs_hist_u135 boxes)`
    `candle_fs_hist_positive_interval
      (FST (candle_fs_hist_u135 boxes))` THEN
  SUBGOAL_THEN
   `0 <
      (FST (FST (FST (candle_fs_hist_u126 boxes))) *
       FST (FST (FST (candle_fs_hist_u135 boxes)))) DIV
      candle_fs_scale`
  ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC
      (REWRITE_RULE[candle_fs_hist_positive_product_def]
        (ASSUME
          `candle_fs_hist_positive_product
            (FST (candle_fs_hist_u126 boxes))
            (FST (candle_fs_hist_u135 boxes))`));
    ALL_TAC] THEN
  candle_contract_match_conjunctive_rule
    (candle_contract_rewrite_with_equalities
      [(ASSUME
        `candle_fs_hist_second_value (candle_fs_hist_delta_second boxes) =
         ((FST (FST (candle_fs_hist_second_value
             (candle_fs_hist_delta_second boxes))),0),
          (FST (SND (candle_fs_hist_second_value
             (candle_fs_hist_delta_second boxes))),0))`);
       (ASSUME
        `(root_delta:((num#num)#(num#num))) =
         ((FST (FST root_delta),0),(FST (SND root_delta),0))`);
       (ASSUME
        `(root_four_x0:((num#num)#(num#num))) =
         ((FST (FST root_four_x0),0),(FST (SND root_four_x0),0))`);
       (ASSUME
        `candle_fs_interval_lookup 0 boxes =
         ((FST (FST (candle_fs_interval_lookup 0 boxes)),0),
          (FST (SND (candle_fs_interval_lookup 0 boxes)),0))`);
       (ASSUME
        `FST (candle_fs_hist_u126 boxes) =
         ((FST (FST (FST (candle_fs_hist_u126 boxes))),0),
          (FST (SND (FST (candle_fs_hist_u126 boxes))),0))`);
       (ASSUME
        `FST (candle_fs_hist_u135 boxes) =
         ((FST (FST (FST (candle_fs_hist_u135 boxes))),0),
          (FST (SND (FST (candle_fs_hist_u135 boxes))),0))`)]
      (SPECL
        [`boxes:((num#num)#(num#num))list`; `values:num->real`;
         `FST (FST (candle_fs_hist_second_value
            (candle_fs_hist_delta_second boxes))):num`;
         `FST (SND (candle_fs_hist_second_value
            (candle_fs_hist_delta_second boxes))):num`;
         `FST (FST (root_delta:((num#num)#(num#num)))):num`;
         `FST (SND (root_delta:((num#num)#(num#num)))):num`;
         `FST (FST (root_four_x0:((num#num)#(num#num)))):num`;
         `FST (SND (root_four_x0:((num#num)#(num#num)))):num`;
         `FST (FST (candle_fs_interval_lookup 0 boxes)):num`;
         `FST (SND (candle_fs_interval_lookup 0 boxes)):num`;
         `FST (FST (FST (candle_fs_hist_u126 boxes))):num`;
         `FST (SND (FST (candle_fs_hist_u126 boxes))):num`;
         `FST (FST (FST (candle_fs_hist_u135 boxes))):num`;
         `FST (SND (FST (candle_fs_hist_u135 boxes))):num`]
        candle_fs_hist_second_order_reference_hessian_contains)));;

let candle_case10173_hist_result_jet_shape = prove
 (`!boxes center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     candle_q_dim_jet_shape 6
       (candle_fs_first_to_q
         (candle_fs_hist_first_order_direct
           (candle_fs_interval_list_of_q
             (candle_q_center_environment_list boxes))
           center_root_delta center_root_four_x0)
         (candle_fs_hist_second_hessian
           (candle_fs_hist_second_order
             (candle_fs_interval_list_of_q boxes)
             box_root_delta box_root_four_x0)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fs_first_to_q_shape;
              candle_case10173_hist_first_order_direct_gradient_length] THEN
  MP_TAC
    (SPECL
      [`candle_fs_interval_list_of_q
         (boxes:(((num#num)#num)#((num#num)#num))list)`;
       `box_root_delta:(num#num)#(num#num)`;
       `box_root_four_x0:(num#num)#(num#num)`]
      candle_fs_hist_second_order_shape) THEN
  MESON_TAC[]);;

let candle_case10173_hist_reference_hessian_is_source = prove
 (`!values (p:real^6) lp ln ld up un ud.
     values = (\k. p$(k + 1)) /\
     &0 < candle_fs_hist_delta_real values /\
     &0 < candle_fs_hist_four_x0_real values
     ==>
     list_of_seq
       (\di. list_of_seq
         (candle_hist_real_jet_hessian
           (candle_fs_hist_reference_dihedral_real_jet values) di) 6) 6 =
     list_of_seq
       (\di. list_of_seq
         (\dj. partial2 (dj + 1) (di + 1)
           (candle_analytic_denote_dim
             (candle_case10173_hist_source_dihedral_expr
               lp ln ld up un ud)) p) 6) 6`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_analytic_regular_at (list_of_seq (values:num->real) 6)
      (candle_case10173_hist_source_dihedral_expr lp ln ld up un ud)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_case10173_hist_source_dihedral_regular THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `list_of_seq
      (\di. list_of_seq
        (\dj. candle_analytic_dd di dj
          (list_of_seq (\k. (p:real^6)$(k + 1)) 6)
          (candle_case10173_hist_source_dihedral_expr
            lp ln ld up un ud)) 6) 6` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `di:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `dj:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
    MATCH_MP_TAC candle_case10173_hist_reference_source_dd THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC
      (REWRITE_RULE[candle_case10173_hist_dim_six]
        (ISPECL
          [`candle_case10173_hist_source_dihedral_expr
              lp ln ld up un ud`;
           `p:real^6`]
          candle_analytic_dd_matrix_flyspeck)) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_case10173_hist_source_dihedral_valid];
      ASM_MESON_TAC[]]]);;

end;;
