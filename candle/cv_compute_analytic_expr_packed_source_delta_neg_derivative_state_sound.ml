(* ========================================================================== *)
(* Center-state soundness for the optimized negative delta derivatives.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the ordinary-HOL semantic half of the *)
(* complete optimized Taylor state.  It proves that the exact-rational       *)
(* center value and gradient fields enclose the value and all first           *)
(* derivatives of [--(partial delta / partial x_i)] for i = 3,4,5.            *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_neg_derivative_analytic.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_product_analytic.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_packed_hessian_sound.ml";;

module Candle_cv_analytic_expr_packed_source_delta_neg_derivative_state_sound = struct

open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_gradient;;
open Candle_cv_analytic_expr_packed_source_delta_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_product_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_product_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_analytic;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;

let candle_q_packed_delta_neg_derivative_center_value_def = new_definition
 `candle_q_packed_delta_neg_derivative_center_value coordinate
      x0 x1 x2 x3 x4 x5 =
    candle_q_interval_neg
      (candle_q_interval_lookup coordinate
        (candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5))`;;

let candle_q_packed_delta_neg_derivative_center_gradient_def =
  new_definition
 `candle_q_packed_delta_neg_derivative_center_gradient coordinate
      x0 x1 x2 x3 x4 x5 =
    candle_q_dim_interval_list_neg
      (EL coordinate
        (candle_q_packed_hessian6_expand
          (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)))`;;

let candle_q_dim_interval_list_neg_contains = prove
 (`!intervals values.
     candle_q_stack_contains intervals values
     ==> candle_q_stack_contains
           (candle_q_dim_interval_list_neg intervals)
           (MAP (\value. --value) values)`,
  REWRITE_TAC[candle_q_stack_contains_all2;
              candle_q_dim_interval_list_neg_map] THEN
  LIST_INDUCT_TAC THEN
  X_GEN_TAC `values:real list` THEN
  MP_TAC (ISPEC `values:real list` list_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `value:real`
        (X_CHOOSE_THEN `rest:real list` SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[ALL2; MAP] THEN
  ASM_MESON_TAC[candle_q_interval_neg_sound]);;

let candle_q_packed_delta_neg_derivative_center_value_sound = prove
 (`!x0 x1 x2 x3 x4 x5 v0 v1 v2 v3 v4 v5 coordinate.
     candle_q_interval_contains x0 v0 /\
     candle_q_interval_contains x1 v1 /\
     candle_q_interval_contains x2 v2 /\
     candle_q_interval_contains x3 v3 /\
     candle_q_interval_contains x4 v4 /\
     candle_q_interval_contains x5 v5 /\
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_q_interval_contains
       (candle_q_packed_delta_neg_derivative_center_value coordinate
         x0 x1 x2 x3 x4 x5)
       (candle_analytic_value [v0;v1;v2;v3;v4;v5]
         (candle_packed_delta_neg_derivative_expr coordinate))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let coordinate_lt =
    MATCH_MP
     (ARITH_RULE
       `(coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
        ==> coordinate < 6`)
     (ASSUME `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`) in
  REWRITE_TAC[candle_q_packed_delta_neg_derivative_center_value_def;
              candle_packed_delta_neg_derivative_analytic_value] THEN
  MATCH_MP_TAC candle_q_interval_neg_sound THEN
  let analytic_component =
    MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`]
        candle_packed_delta_analytic_d)
      coordinate_lt in
  let lookup_component =
    MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`]
        candle_q_real_lookup_packed_delta_gradient_six)
      coordinate_lt in
  ONCE_REWRITE_TAC[analytic_component] THEN
  ONCE_REWRITE_TAC[GSYM lookup_component] THEN
  MATCH_MP_TAC candle_q_packed_delta_lookup_contains THEN
  MATCH_MP_TAC candle_q_packed_delta_gradient_six_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_q_packed_delta_hessian_six_analytic_contains = prove
 (`!x0 x1 x2 x3 x4 x5 v0 v1 v2 v3 v4 v5.
     candle_q_interval_contains x0 v0 /\
     candle_q_interval_contains x1 v1 /\
     candle_q_interval_contains x2 v2 /\
     candle_q_interval_contains x3 v3 /\
     candle_q_interval_contains x4 v4 /\
     candle_q_interval_contains x5 v5
     ==>
     candle_q_stack_contains
       (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)
       (candle_q_packed_hessian6_values
         (\i j. candle_analytic_dd i j [v0;v1;v2;v3;v4;v5]
           candle_packed_delta_expr))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_stack_contains_all2] THEN
  MP_TAC
   (MATCH_MP
     (SPECL
       [`x0:((num#num)#num)#((num#num)#num)`;
        `x1:((num#num)#num)#((num#num)#num)`;
        `x2:((num#num)#num)#((num#num)#num)`;
        `x3:((num#num)#num)#((num#num)#num)`;
        `x4:((num#num)#num)#((num#num)#num)`;
        `x5:((num#num)#num)#((num#num)#num)`;
        `v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`]
       candle_q_packed_delta_hessian_six_sound)
     (end_itlist CONJ
       (map ASSUME
         [`candle_q_interval_contains x0 v0`;
          `candle_q_interval_contains x1 v1`;
          `candle_q_interval_contains x2 v2`;
          `candle_q_interval_contains x3 v3`;
          `candle_q_interval_contains x4 v4`;
          `candle_q_interval_contains x5 v5`]))) THEN
  REWRITE_TAC[candle_real_packed_delta_hessian_six_analytic;
              candle_real_packed_delta_analytic_hessian_six_def;
              candle_q_packed_hessian6_values_def]);;

let candle_q_packed_delta_neg_derivative_center_gradient_sound = prove
 (`!x0 x1 x2 x3 x4 x5 v0 v1 v2 v3 v4 v5 coordinate.
     candle_q_interval_contains x0 v0 /\
     candle_q_interval_contains x1 v1 /\
     candle_q_interval_contains x2 v2 /\
     candle_q_interval_contains x3 v3 /\
     candle_q_interval_contains x4 v4 /\
     candle_q_interval_contains x5 v5 /\
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_q_stack_contains
       (candle_q_packed_delta_neg_derivative_center_gradient coordinate
         x0 x1 x2 x3 x4 x5)
       (list_of_seq
         (\derivative_coordinate.
           candle_analytic_d derivative_coordinate
             [v0;v1;v2;v3;v4;v5]
             (candle_packed_delta_neg_derivative_expr coordinate)) 6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC
   (MATCH_MP
     (ARITH_RULE
       `(coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
        ==> coordinate < 6`)
     (ASSUME `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`)) THEN
  let packed_contains =
    MATCH_MP
      (SPECL
        [`x0:((num#num)#num)#((num#num)#num)`;
         `x1:((num#num)#num)#((num#num)#num)`;
         `x2:((num#num)#num)#((num#num)#num)`;
         `x3:((num#num)#num)#((num#num)#num)`;
         `x4:((num#num)#num)#((num#num)#num)`;
         `x5:((num#num)#num)#((num#num)#num)`;
         `v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`]
        candle_q_packed_delta_hessian_six_analytic_contains)
      (end_itlist CONJ
        (map ASSUME
          [`candle_q_interval_contains x0 v0`;
           `candle_q_interval_contains x1 v1`;
           `candle_q_interval_contains x2 v2`;
           `candle_q_interval_contains x3 v3`;
           `candle_q_interval_contains x4 v4`;
           `candle_q_interval_contains x5 v5`])) in
  let expanded_contains =
    MATCH_MP
      (ISPECL
        [`candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5`;
         `(\i j. candle_analytic_dd i j [v0;v1;v2;v3;v4;v5]
            candle_packed_delta_expr):num->num->real`]
        candle_q_packed_hessian6_expand_contains_symmetric_values)
      packed_contains in
  MP_TAC expanded_contains THEN
  REWRITE_TAC[candle_q_symmetric_hessian6_analytic_values] THEN
  DISCH_THEN (LABEL_TAC "expanded_hessian") THEN
  SUBGOAL_THEN
   `candle_q_stack_contains
      (EL coordinate
        (candle_q_packed_hessian6_expand
          (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)))
      (list_of_seq
        (\j. candle_analytic_dd coordinate j [v0;v1;v2;v3;v4;v5]
          candle_packed_delta_expr) 6)`
  ASSUME_TAC THENL
   [USE_THEN "expanded_hessian"
     (fun expanded_hessian ->
       let expanded_length =
         CONJUNCT1
          (ISPEC
            `candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5`
            candle_q_packed_hessian6_expand_shape) in
       let coordinate_lt_length =
         REWRITE_RULE[GSYM expanded_length]
           (ASSUME `coordinate < 6`) in
       MP_TAC
        (MATCH_MP
          (ISPECL
            [`coordinate:num`; `candle_q_stack_contains`;
             `candle_q_packed_hessian6_expand
               (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)`;
             `list_of_seq
               (\i. list_of_seq
                 (\j. candle_analytic_dd i j [v0;v1;v2;v3;v4;v5]
                   candle_packed_delta_expr) 6) 6`]
            candle_all2_el_lt)
          (CONJ expanded_hessian coordinate_lt_length))) THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_packed_delta_neg_derivative_center_gradient_def] THEN
  REWRITE_TAC[candle_packed_delta_neg_derivative_analytic_d] THEN
  let row_contains =
    ASSUME
      `candle_q_stack_contains
         (EL coordinate
           (candle_q_packed_hessian6_expand
             (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)))
         (list_of_seq
           (\j. candle_analytic_dd coordinate j [v0;v1;v2;v3;v4;v5]
             candle_packed_delta_expr) 6)` in
  let neg_contains =
    MATCH_MP candle_q_dim_interval_list_neg_contains row_contains in
  let rewritten_neg_contains =
    REWRITE_RULE [MAP_LIST_OF_SEQ; o_DEF] neg_contains in
  ACCEPT_TAC rewritten_neg_contains);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_dim_interval_list_neg_contains;
     candle_q_packed_delta_neg_derivative_center_value_sound;
     candle_q_packed_delta_hessian_six_analytic_contains;
     candle_q_packed_delta_neg_derivative_center_gradient_sound] then
  failwith "packed source negative delta derivative center state: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_NEG_DERIVATIVE_CENTER_STATE_OK DEVELOPMENT_NON_RELEASE";;

end;;
