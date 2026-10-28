(* ========================================================================== *)
(* Center-state soundness for the optimized [4 * x_i * delta] instructions. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The definitions below are the exact-rational *)
(* object operations used after the shared delta value and gradient have     *)
(* been computed.  This layer proves their analytic meaning independently of *)
(* any one Flyspeck inequality or certificate.                               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_product_analytic.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_packed_hessian_sound.ml";;

module Candle_cv_analytic_expr_packed_source_delta_product_state_sound = struct

open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_packed_source_delta_product_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_product_analytic;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;

let candle_q_packed_delta_product_center_value_def = new_definition
 `candle_q_packed_delta_product_center_value coordinate_value delta_value =
    candle_q_packed_delta_scale4
      (candle_q_interval_mul coordinate_value delta_value)`;;

let candle_q_packed_delta_product_center_gradient_entry_def = new_definition
 `candle_q_packed_delta_product_center_gradient_entry coordinate
      coordinate_value delta_value delta_gradient derivative_coordinate =
    let base = candle_q_interval_mul coordinate_value
      (candle_q_interval_lookup derivative_coordinate delta_gradient) in
    let complete =
      if derivative_coordinate = coordinate then
        candle_q_interval_add base delta_value
      else base in
    candle_q_packed_delta_scale4 complete`;;

let candle_q_packed_delta_product_center_gradient_six_def = new_definition
 `candle_q_packed_delta_product_center_gradient_six coordinate
      coordinate_value delta_value delta_gradient =
    [candle_q_packed_delta_product_center_gradient_entry coordinate
       coordinate_value delta_value delta_gradient 0;
     candle_q_packed_delta_product_center_gradient_entry coordinate
       coordinate_value delta_value delta_gradient 1;
     candle_q_packed_delta_product_center_gradient_entry coordinate
       coordinate_value delta_value delta_gradient 2;
     candle_q_packed_delta_product_center_gradient_entry coordinate
       coordinate_value delta_value delta_gradient 3;
     candle_q_packed_delta_product_center_gradient_entry coordinate
       coordinate_value delta_value delta_gradient 4;
     candle_q_packed_delta_product_center_gradient_entry coordinate
       coordinate_value delta_value delta_gradient 5]`;;

let candle_q_packed_delta_product_center_value_sound = prove
 (`!coordinate_value delta_value real_coordinate real_delta.
     candle_q_interval_contains coordinate_value real_coordinate /\
     candle_q_interval_contains delta_value real_delta
     ==>
     candle_q_interval_contains
       (candle_q_packed_delta_product_center_value
         coordinate_value delta_value)
       (candle_real_packed_delta_product_value real_coordinate real_delta)`,
  MESON_TAC
    [candle_q_packed_delta_product_center_value_def;
     candle_real_packed_delta_product_value_def;
     Candle_cv_analytic_expr_packed_source_delta_product_hessian.candle_q_packed_delta_scale4_sound;
     Candle_cv_exact_interval_mul_core.candle_q_interval_mul_sound]);;

let candle_q_packed_delta_product_center_gradient_entry_sound = prove
 (`!coordinate coordinate_value delta_value delta_gradient
       derivative_coordinate real_coordinate real_delta real_gradient.
     candle_q_interval_contains coordinate_value real_coordinate /\
     candle_q_interval_contains delta_value real_delta /\
     candle_q_stack_contains delta_gradient real_gradient /\
     derivative_coordinate < LENGTH delta_gradient
     ==>
     candle_q_interval_contains
       (candle_q_packed_delta_product_center_gradient_entry coordinate
         coordinate_value delta_value delta_gradient derivative_coordinate)
       (candle_real_packed_delta_product_gradient_entry coordinate
         real_coordinate real_delta real_gradient derivative_coordinate)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_product_center_gradient_entry_def;
              candle_real_packed_delta_product_gradient_entry_def;
              LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 candle_q_interval_contains delta_gradient real_gradient`
   ASSUME_TAC THENL
   [ASM_MESON_TAC
      [Candle_cv_polynomial_expr_diff.candle_q_stack_contains_all2];
    ALL_TAC] THEN
  let length_equal =
    MATCH_MP
      (ISPECL
        [`candle_q_interval_contains:
            (((num#num)#num)#((num#num)#num))->real->bool`;
         `delta_gradient:(((num#num)#num)#((num#num)#num))list`;
         `real_gradient:real list`]
        Candle_cv_analytic_expr_taylor_model_packed_hessian_sound.candle_all2_length)
      (ASSUME
        `ALL2 candle_q_interval_contains delta_gradient real_gradient`) in
  ASSUME_TAC length_equal THEN
  SUBGOAL_THEN
   `candle_q_real_lookup derivative_coordinate real_gradient =
    EL derivative_coordinate real_gradient`
   ASSUME_TAC THENL
   [(MATCH_MP_TAC
      (Candle_cv_polynomial_expr_dim_calculus.candle_q_real_lookup_in_range)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_interval_lookup derivative_coordinate delta_gradient)
      (EL derivative_coordinate real_gradient)`
   ASSUME_TAC THENL
   [MP_TAC
     (SPECL
       [`derivative_coordinate:num`;
        `delta_gradient:(((num#num)#num)#((num#num)#num))list`;
        `real_gradient:real list`]
       Candle_cv_analytic_expr_packed_source_delta_product_hessian.candle_q_packed_delta_lookup_contains) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (ASM_CASES_TAC `(derivative_coordinate:num) = coordinate` THENL
   [ASM_REWRITE_TAC[] THEN
    (MATCH_MP_TAC
      (Candle_cv_analytic_expr_packed_source_delta_product_hessian.candle_q_packed_delta_scale4_sound)) THEN
    MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THENL
     [(MATCH_MP_TAC
        (Candle_cv_exact_interval_mul_core.candle_q_interval_mul_sound)) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN
    (MATCH_MP_TAC
      (Candle_cv_analytic_expr_packed_source_delta_product_hessian.candle_q_packed_delta_scale4_sound)) THEN
    (MATCH_MP_TAC
      (Candle_cv_exact_interval_mul_core.candle_q_interval_mul_sound)) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]) THEN
  ASM_MESON_TAC[]);;

let candle_q_packed_delta_product_center_gradient_six_sound = prove
 (`!v0 v1 v2 v3 v4 v5 coordinate coordinate_value delta_value
       delta_gradient real_coordinate real_delta real_gradient.
     coordinate < 6 /\
     candle_q_interval_contains coordinate_value real_coordinate /\
     candle_q_interval_contains delta_value real_delta /\
     candle_q_stack_contains delta_gradient real_gradient /\
     real_coordinate =
       candle_q_real_lookup coordinate [v0;v1;v2;v3;v4;v5] /\
     real_delta = candle_packed_delta_real v0 v1 v2 v3 v4 v5 /\
     real_gradient =
       candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5
     ==>
     candle_q_stack_contains
       (candle_q_packed_delta_product_center_gradient_six coordinate
         coordinate_value delta_value delta_gradient)
       (list_of_seq
         (\derivative_coordinate.
           candle_analytic_d derivative_coordinate
             [v0;v1;v2;v3;v4;v5]
             (candle_packed_delta_product_expr coordinate)) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  let gradient_all2 =
    REWRITE_RULE
      [Candle_cv_polynomial_expr_diff.candle_q_stack_contains_all2]
      (ASSUME
        `candle_q_stack_contains delta_gradient
          (candle_real_packed_delta_gradient_six
            v0 v1 v2 v3 v4 v5)`) in
  let length_equal =
    MATCH_MP
      (ISPECL
        [`candle_q_interval_contains:
            (((num#num)#num)#((num#num)#num))->real->bool`;
         `delta_gradient:(((num#num)#num)#((num#num)#num))list`;
         `candle_real_packed_delta_gradient_six
            v0 v1 v2 v3 v4 v5:real list`]
        Candle_cv_analytic_expr_taylor_model_packed_hessian_sound.candle_all2_length)
      gradient_all2 in
  let length_six =
    REWRITE_RULE[candle_real_packed_delta_gradient_six_length]
      length_equal in
  let coordinate_lt = ASSUME `coordinate < 6` in
  let coordinate_contains =
    ASSUME
      `candle_q_interval_contains coordinate_value
        (candle_q_real_lookup coordinate [v0;v1;v2;v3;v4;v5])` in
  let delta_contains =
    ASSUME
      `candle_q_interval_contains delta_value
        (candle_packed_delta_real v0 v1 v2 v3 v4 v5)` in
  let gradient_contains =
    ASSUME
      `candle_q_stack_contains delta_gradient
        (candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5)` in
  let component derivative_coordinate =
    let derivative_lt =
      prove
       (vsubst
         [derivative_coordinate,`derivative_coordinate:num`]
         `derivative_coordinate < 6`,
        CONV_TAC NUM_REDUCE_CONV) in
    let derivative_lt_length =
      REWRITE_RULE[GSYM length_six] derivative_lt in
    let entry_contains =
      MATCH_MP
        (SPECL
          [`coordinate:num`;
           `coordinate_value:((num#num)#num)#((num#num)#num)`;
           `delta_value:((num#num)#num)#((num#num)#num)`;
           `delta_gradient:(((num#num)#num)#((num#num)#num))list`;
           derivative_coordinate;
           `candle_q_real_lookup coordinate [v0;v1;v2;v3;v4;v5]`;
           `candle_packed_delta_real v0 v1 v2 v3 v4 v5`;
           `candle_real_packed_delta_gradient_six
              v0 v1 v2 v3 v4 v5`]
          candle_q_packed_delta_product_center_gradient_entry_sound)
        (end_itlist CONJ
          [coordinate_contains; delta_contains; gradient_contains;
           derivative_lt_length]) in
    let analytic_entry =
      MATCH_MP
        (SPECL
          [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
           `coordinate:num`; derivative_coordinate]
          candle_packed_delta_product_analytic_d)
        (CONJ coordinate_lt derivative_lt) in
    REWRITE_RULE[GSYM analytic_entry] entry_contains in
  let component0 = component `0` in
  let component1 = component `1` in
  let component2 = component `2` in
  let component3 = component `3` in
  let component4 = component `4` in
  let component5 = component `5` in
  let all_components =
    CONJ component0
      (CONJ component1
        (CONJ component2
          (CONJ component3 (CONJ component4 component5)))) in
  REWRITE_TAC
             [Candle_cv_polynomial_expr_diff.candle_q_stack_contains_all2;
              candle_q_packed_delta_product_center_gradient_six_def;
              num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND; ALL2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCEPT_TAC all_components);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_delta_product_center_value_sound;
     candle_q_packed_delta_product_center_gradient_entry_sound;
     candle_q_packed_delta_product_center_gradient_six_sound] then
  failwith "packed source delta product center state: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_PRODUCT_CENTER_STATE_OK DEVELOPMENT_NON_RELEASE";;

end;;
