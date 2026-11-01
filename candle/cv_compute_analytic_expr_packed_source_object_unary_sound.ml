(* ========================================================================== *)
(* Exact object-q unary chain-rule arithmetic.                               *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The verified word evaluator refines sqrt,     *)
(* reciprocal and atan to one object-rational unary constructor.  This file  *)
(* mirrors that constructor's raw rational list scaling, triangular          *)
(* self-outer product and packed Hessian association order.                  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_mul_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_unary_sound = struct

open Candle_cv_exact_interval_mul_core;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_mul_sound;;

let candle_q_packed_object_interval_list_scale_def = new_definition
 `candle_q_packed_object_interval_list_scale scalar values =
    MAP (candle_q_interval_mul scalar) values`;;

let candle_real_packed_object_interval_list_scale_def = new_definition
 `candle_real_packed_object_interval_list_scale scalar values =
    MAP (\value:real. scalar * value) values`;;

let candle_q_packed_object_interval_list_scale_length = prove
 (`!scalar values.
     LENGTH (candle_q_packed_object_interval_list_scale scalar values) =
     LENGTH values`,
  REWRITE_TAC[candle_q_packed_object_interval_list_scale_def; LENGTH_MAP]);;

let candle_q_packed_object_interval_list_scale_lookup = prove
 (`!scalar values i.
     i < LENGTH values
     ==>
     candle_q_interval_lookup i
       (candle_q_packed_object_interval_list_scale scalar values) =
     candle_q_interval_mul scalar (candle_q_interval_lookup i values)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_interval_lookup_in_range;
               candle_q_packed_object_interval_list_scale_def;
               LENGTH_MAP; EL_MAP]);;

let candle_q_packed_object_interval_list_scale_sound = prove
 (`!values real_values scalar scalar_real.
     candle_q_stack_contains values real_values /\
     candle_q_interval_contains scalar scalar_real
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_interval_list_scale scalar values)
       (candle_real_packed_object_interval_list_scale
         scalar_real real_values)`,
  LIST_INDUCT_TAC THENL
   [X_GEN_TAC `real_values:real list` THEN
    MP_TAC (ISPEC `real_values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `real_head:real`
          (X_CHOOSE_THEN `real_tail:real list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_q_packed_object_interval_list_scale_def;
                candle_real_packed_object_interval_list_scale_def;
                candle_q_stack_contains_def; MAP];
    POP_ASSUM (LABEL_TAC "scale_ih") THEN
    X_GEN_TAC `real_values:real list` THEN
    MP_TAC (ISPEC `real_values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `real_head:real`
          (X_CHOOSE_THEN `real_tail:real list` SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_q_packed_object_interval_list_scale_def;
                candle_real_packed_object_interval_list_scale_def;
                candle_q_stack_contains_def; MAP] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_interval_mul_sound THEN ASM_REWRITE_TAC[];
      USE_THEN "scale_ih"
        (fun theorem ->
          MATCH_MP_TAC
            (REWRITE_RULE
              [candle_q_packed_object_interval_list_scale_def;
               candle_real_packed_object_interval_list_scale_def]
              theorem)) THEN
      ASM_REWRITE_TAC[]]]);;

let candle_q_packed_object_stack_contains_append = prove
 (`!left left_values right right_values.
     candle_q_stack_contains left left_values /\
     candle_q_stack_contains right right_values
     ==>
     candle_q_stack_contains
       (APPEND left right) (APPEND left_values right_values)`,
  LIST_INDUCT_TAC THENL
   [X_GEN_TAC `left_values:real list` THEN
    MP_TAC (ISPEC `left_values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `left_value:real`
          (X_CHOOSE_THEN `left_values_tail:real list` SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[APPEND; candle_q_stack_contains_def];
    POP_ASSUM (LABEL_TAC "append_ih") THEN
    X_GEN_TAC `left_values:real list` THEN
    MP_TAC (ISPEC `left_values:real list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `left_value:real`
          (X_CHOOSE_THEN `left_values_tail:real list` SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[APPEND; candle_q_stack_contains_def] THEN
    REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "append_ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let candle_q_packed_object_interval_self_outer_def = define
 `(candle_q_packed_object_interval_self_outer
     ([]:(((num#num)#num)#((num#num)#num))list) = []) /\
  (candle_q_packed_object_interval_self_outer (CONS entry rest) =
     APPEND
       (candle_q_packed_object_interval_list_scale entry (CONS entry rest))
       (candle_q_packed_object_interval_self_outer rest))`;;

let candle_real_packed_object_interval_self_outer_def = define
 `(candle_real_packed_object_interval_self_outer ([]:real list) = []) /\
  (candle_real_packed_object_interval_self_outer (CONS entry rest) =
     APPEND
       (candle_real_packed_object_interval_list_scale entry (CONS entry rest))
       (candle_real_packed_object_interval_self_outer rest))`;;

let candle_q_packed_object_interval_self_outer_sound = prove
 (`!values real_values.
     candle_q_stack_contains values real_values
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_interval_self_outer values)
       (candle_real_packed_object_interval_self_outer real_values)`,
  LIST_INDUCT_TAC THEN
  X_GEN_TAC `real_values:real list` THEN
  MP_TAC (ISPEC `real_values:real list` list_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `real_head:real`
        (X_CHOOSE_THEN `real_tail:real list` SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[candle_q_packed_object_interval_self_outer_def;
                  candle_real_packed_object_interval_self_outer_def;
                  candle_q_stack_contains_def] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_q_packed_object_stack_contains_append THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_interval_list_scale_sound THEN
    ASM_REWRITE_TAC[candle_q_stack_contains_def];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_interval_self_outer_twice_length = prove
 (`!values.
     2 * LENGTH (candle_q_packed_object_interval_self_outer values) =
     LENGTH values * (LENGTH values + 1)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_q_packed_object_interval_self_outer_def; LENGTH] THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[candle_q_packed_object_interval_self_outer_def;
                    candle_q_packed_object_interval_list_scale_length;
                    LENGTH_APPEND; LENGTH] THEN
    let left_expand = prove
     (`!n m. 2 * (SUC n + m) = 2 * SUC n + 2 * m`,
      CONV_TAC NUM_RING) in
    let right_expand = prove
     (`!n. SUC n * (SUC n + 1) = 2 * SUC n + n * (n + 1)`,
      CONV_TAC NUM_RING) in
    ASM_REWRITE_TAC[left_expand; right_expand]]);;

let candle_q_packed_object_interval_self_outer6_length = prove
 (`!values.
     LENGTH values = 6
     ==> LENGTH (candle_q_packed_object_interval_self_outer values) = 21`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPEC
      `values:(((num#num)#num)#((num#num)#num))list`
      candle_q_packed_object_interval_self_outer_twice_length) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let candle_real_packed_object_interval_self_outer6 = prove
 (`!gradient:num->real.
     candle_real_packed_object_interval_self_outer
       (list_of_seq gradient 6) =
     candle_q_packed_hessian6_values
       (\i j. gradient i * gradient j)`,
  GEN_TAC THEN
  let numeral_conversions =
    map (fun n -> num_CONV (mk_small_numeral n)) (1--6) in
  REWRITE_TAC
    ([list_of_seq;
      candle_real_packed_object_interval_self_outer_def;
      candle_real_packed_object_interval_list_scale_def;
      candle_q_packed_hessian6_values_def; MAP; APPEND] @
     numeral_conversions));;

let candle_q_packed_object_interval_self_outer6_sound = prove
 (`!values gradient.
     candle_q_stack_contains values (list_of_seq gradient 6)
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_interval_self_outer values)
       (candle_q_packed_hessian6_values
         (\i j. gradient i * gradient j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (MATCH_MP
      candle_q_packed_object_interval_self_outer_sound
      (ASSUME
        `candle_q_stack_contains values (list_of_seq gradient 6)`)) THEN
  REWRITE_TAC[candle_real_packed_object_interval_self_outer6]);;

let candle_q_packed_object_unary_hessian6_def = new_definition
 `candle_q_packed_object_unary_hessian6 derivative_interval second_interval
      gradient packed_hessian =
    MAP2 candle_q_interval_add
      (candle_q_packed_object_interval_list_scale second_interval
        (candle_q_packed_object_interval_self_outer gradient))
      (candle_q_packed_object_interval_list_scale derivative_interval
        packed_hessian)`;;

let candle_q_packed_object_unary_hessian6_length = prove
  (`!derivative_interval second_interval gradient packed_hessian.
     LENGTH gradient = 6 /\ LENGTH packed_hessian = 21
     ==>
     LENGTH
       (candle_q_packed_object_unary_hessian6
         derivative_interval second_interval gradient packed_hessian) = 21`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH (candle_q_packed_object_interval_self_outer gradient) = 21`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_interval_self_outer6_length THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[candle_q_packed_object_unary_hessian6_def;
                 candle_q_packed_object_interval_list_scale_length;
                 LENGTH_MAP2]]);;

let candle_q_packed_object_unary_hessian6_lookup = prove
 (`!derivative_interval second_interval gradient packed_hessian i.
     LENGTH gradient = 6 /\ LENGTH packed_hessian = 21 /\ i < 21
     ==>
     candle_q_interval_lookup i
       (candle_q_packed_object_unary_hessian6
         derivative_interval second_interval gradient packed_hessian) =
     candle_q_interval_add
       (candle_q_interval_mul second_interval
         (candle_q_interval_lookup i
           (candle_q_packed_object_interval_self_outer gradient)))
       (candle_q_interval_mul derivative_interval
         (candle_q_interval_lookup i packed_hessian))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH (candle_q_packed_object_interval_self_outer gradient) = 21`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_interval_self_outer6_length THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH (candle_q_packed_object_unary_hessian6
      derivative_interval second_interval gradient packed_hessian) = 21`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_unary_hessian6_length THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[candle_q_interval_lookup_in_range;
               candle_q_packed_object_unary_hessian6_def;
               candle_q_packed_object_interval_list_scale_def;
               LENGTH_MAP; EL_MAP; EL_MAP2]);;

let candle_q_packed_object_unary_hessian6_sound = prove
 (`!derivative_interval second_interval gradient packed_hessian
       derivative_real second_real gradient_real hessian_real.
     LENGTH gradient = 6 /\ LENGTH packed_hessian = 21 /\
     candle_q_interval_contains derivative_interval derivative_real /\
     candle_q_interval_contains second_interval second_real /\
     candle_q_stack_contains gradient (list_of_seq gradient_real 6) /\
     candle_q_stack_contains packed_hessian
       (candle_q_packed_hessian6_values hessian_real)
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_unary_hessian6
         derivative_interval second_interval gradient packed_hessian)
       (candle_q_packed_hessian6_values
         (\i j.
            second_real * (gradient_real i * gradient_real j) +
            derivative_real * hessian_real i j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let outer_contains =
    MATCH_MP
      candle_q_packed_object_interval_self_outer6_sound
      (ASSUME
        `candle_q_stack_contains gradient
          (list_of_seq gradient_real 6)`) in
  ASSUME_TAC outer_contains THEN
  SUBGOAL_THEN
   `LENGTH (candle_q_packed_object_interval_self_outer gradient) = 21`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_interval_self_outer6_length THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_packed_object_unary_hessian6
      derivative_interval second_interval gradient packed_hessian =
    list_of_seq
      (\i. candle_q_interval_lookup i
        (candle_q_packed_object_unary_hessian6
          derivative_interval second_interval gradient packed_hessian)) 21`
  SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_interval_list_eq_list_of_seq_lookup THEN
    MATCH_MP_TAC candle_q_packed_object_unary_hessian6_length THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_stack_contains_all2;
              candle_q_packed_hessian6_values_coordinates;
              candle_all2_list_of_seq] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[candle_q_packed_object_unary_hessian6_lookup;
               EL_LIST_OF_SEQ] THEN
  MATCH_MP_TAC candle_q_interval_add_sound THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `candle_q_interval_contains
       (candle_q_interval_lookup i
         (candle_q_packed_object_interval_self_outer gradient))
       (gradient_real (candle_q_packed_object_hessian6_row i) *
        gradient_real (candle_q_packed_object_hessian6_col i))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `i < LENGTH
         (candle_q_packed_object_interval_self_outer gradient)`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[];
        let outer_entry_contains =
          MATCH_MP candle_q_stack_contains_el_lt
            (CONJ
              (ASSUME
                `candle_q_stack_contains
                  (candle_q_packed_object_interval_self_outer gradient)
                  (candle_q_packed_hessian6_values
                    (\i j. gradient_real i * gradient_real j))`)
              (ASSUME
                `i < LENGTH
                  (candle_q_packed_object_interval_self_outer
                    gradient)`)) in
        MP_TAC outer_entry_contains THEN
        ASM_SIMP_TAC[candle_q_interval_lookup_in_range;
                     candle_q_packed_hessian6_values_coordinates;
                     LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]];
      let product_contains =
        MATCH_MP candle_q_interval_mul_sound
          (CONJ
            (ASSUME
              `candle_q_interval_contains second_interval second_real`)
            (ASSUME
              `candle_q_interval_contains
                (candle_q_interval_lookup i
                  (candle_q_packed_object_interval_self_outer gradient))
                (gradient_real
                   (candle_q_packed_object_hessian6_row i) *
                 gradient_real
                   (candle_q_packed_object_hessian6_col i))`)) in
      SUBGOAL_THEN
       `second_real *
          gradient_real (candle_q_packed_object_hessian6_row i) *
          gradient_real (candle_q_packed_object_hessian6_col i) =
        second_real *
          (gradient_real (candle_q_packed_object_hessian6_row i) *
           gradient_real (candle_q_packed_object_hessian6_col i))`
      SUBST1_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC];
        ACCEPT_TAC product_contains]];
    SUBGOAL_THEN
     `candle_q_interval_contains
       (candle_q_interval_lookup i packed_hessian)
       (hessian_real (candle_q_packed_object_hessian6_row i)
         (candle_q_packed_object_hessian6_col i))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `i < LENGTH
         (packed_hessian:
           (((num#num)#num)#((num#num)#num))list)`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[];
        SUBGOAL_THEN
         `candle_q_interval_contains
           (EL i packed_hessian)
           (EL i (candle_q_packed_hessian6_values hessian_real))`
        ASSUME_TAC THENL
         [MATCH_MP_TAC candle_q_stack_contains_el_lt THEN
          ASM_REWRITE_TAC[];
          MP_TAC
            (ASSUME
              `candle_q_interval_contains
                (EL i packed_hessian)
                (EL i
                  (candle_q_packed_hessian6_values hessian_real))`) THEN
          ONCE_REWRITE_TAC[
            candle_q_packed_hessian6_values_coordinates] THEN
          ASM_SIMP_TAC[candle_q_interval_lookup_in_range;
                       LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]]];
      MATCH_MP_TAC candle_q_interval_mul_sound THEN
      ASM_REWRITE_TAC[]]]);;

(* Recover the two packed stack-containment facts needed by every unary      *)
(* constructor from the ordinary analytic box-jet invariant.  Keeping this  *)
(* extraction here avoids repeating coordinate reconstruction for sqrt and  *)
(* atan after reciprocal established the first instance.                     *)

let candle_q_packed_object_box_source_stacks = prove
 (`!source_value source_gradient source_hessian environment source_e.
     LENGTH source_gradient = 6 /\ LENGTH source_hessian = 21 /\
     candle_q_dim_analytic_contains 6
       (candle_q_packed_object_box_jet
         source_value source_gradient source_hessian)
       environment source_e
     ==>
     candle_q_stack_contains source_gradient
       (list_of_seq (\i. candle_analytic_d i environment source_e) 6) /\
     candle_q_stack_contains source_hessian
       (candle_q_packed_hessian6_values
         (\i j. candle_analytic_dd i j environment source_e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let source_components =
    REWRITE_RULE
      [candle_q_dim_analytic_contains_def;
       candle_q_dim_jet_contains_components_def;
       candle_q_packed_object_box_jet_def;
       candle_q_dim_jet_f_def;
       candle_q_dim_jet_gradient_at_def;
       candle_q_dim_jet_hessian_at_def;
       candle_q_dim_jet_gradient_def;
       candle_q_dim_jet_hessian_def;
       candle_q_dim_jet_make_def; FST; SND]
      (ASSUME
        `candle_q_dim_analytic_contains 6
          (candle_q_packed_object_box_jet
            source_value source_gradient source_hessian)
          environment source_e`) in
  let _,source_derivatives = CONJ_PAIR source_components in
  let gradient_contains,_ = CONJ_PAIR source_derivatives in
  ASSUME_TAC gradient_contains THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `source_gradient =
      list_of_seq (\i. candle_q_interval_lookup i source_gradient) 6`
    SUBST1_TAC THENL
     [MATCH_MP_TAC candle_q_interval_list_eq_list_of_seq_lookup THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_stack_contains_all2;
                  candle_all2_list_of_seq] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[EL_LIST_OF_SEQ]];
    SUBGOAL_THEN
     `source_hessian =
      list_of_seq (\i. candle_q_interval_lookup i source_hessian) 21`
    SUBST1_TAC THENL
     [MATCH_MP_TAC candle_q_interval_list_eq_list_of_seq_lookup THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_stack_contains_all2] THEN
      ONCE_REWRITE_TAC[candle_q_packed_hessian6_values_coordinates] THEN
      REWRITE_TAC[candle_all2_list_of_seq] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
      MATCH_MP_TAC
        (SPECL
          [`source_value:((num#num)#num)#((num#num)#num)`;
           `source_gradient:
              (((num#num)#num)#((num#num)#num))list`;
           `source_hessian:
              (((num#num)#num)#((num#num)#num))list`;
           `environment:real list`; `source_e:candle_analytic_expr`; `i:num`]
          candle_q_packed_object_analytic_hessian_lookup_contains) THEN
      ASM_REWRITE_TAC[]]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_interval_list_scale_length;
     candle_q_packed_object_interval_list_scale_lookup;
     candle_q_packed_object_interval_list_scale_sound;
     candle_q_packed_object_stack_contains_append;
     candle_q_packed_object_interval_self_outer_sound;
     candle_q_packed_object_interval_self_outer_twice_length;
     candle_q_packed_object_interval_self_outer6_length;
     candle_real_packed_object_interval_self_outer6;
     candle_q_packed_object_interval_self_outer6_sound;
     candle_q_packed_object_unary_hessian6_length;
     candle_q_packed_object_unary_hessian6_lookup;
     candle_q_packed_object_unary_hessian6_sound;
     candle_q_packed_object_box_source_stacks] then
  failwith "packed source object unary sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_UNARY_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
