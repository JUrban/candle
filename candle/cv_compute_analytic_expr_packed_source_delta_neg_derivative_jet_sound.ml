(* ========================================================================== *)
(* Complete six-dimensional analytic jet for negative delta derivatives.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The optimized object state stores a center   *)
(* value and gradient together with a packed whole-box Hessian.  This file  *)
(* packages the three proved fields as the ordinary HOL analytic-jet         *)
(* invariant consumed by source-program induction.                           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_neg_derivative_state_complete_sound.ml";;

module Candle_cv_analytic_expr_packed_source_delta_neg_derivative_jet_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_state_sound;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_state_complete_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;

let candle_q_packed_delta_neg_derivative_jet_six_def = new_definition
 `candle_q_packed_delta_neg_derivative_jet_six coordinate
      x0 x1 x2 x3 x4 x5 =
    candle_q_dim_jet_make
      (candle_q_packed_delta_neg_derivative_center_value coordinate
        x0 x1 x2 x3 x4 x5)
      (candle_q_packed_delta_neg_derivative_center_gradient coordinate
        x0 x1 x2 x3 x4 x5)
      (candle_q_packed_hessian6_expand
        (candle_q_packed_delta_neg_derivative_hessian_six coordinate))`;;

let candle_q_packed_delta_neg_derivative_jet_six_shape = prove
 (`!coordinate x0 x1 x2 x3 x4 x5.
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_q_dim_jet_shape 6
       (candle_q_packed_delta_neg_derivative_jet_six coordinate
         x0 x1 x2 x3 x4 x5)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  let coordinate_lt =
    MATCH_MP
      (ARITH_RULE
        `(coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
         ==> coordinate < 6`)
      (ASSUME `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`) in
  let center_matrix_shape =
    ISPEC
      `candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5:
        ((((num#num)#num)#((num#num)#num))list)`
      candle_q_packed_hessian6_expand_shape in
  let center_matrix_length,center_rows_length =
    CONJ_PAIR center_matrix_shape in
  let center_row_length =
    MATCH_MP
      (SPEC `coordinate:num`
        (REWRITE_RULE[GSYM ALL_EL] center_rows_length))
      (REWRITE_RULE[GSYM center_matrix_length] coordinate_lt) in
  let box_matrix_shape =
    ISPEC
      `candle_q_packed_delta_neg_derivative_hessian_six coordinate:
        ((((num#num)#num)#((num#num)#num))list)`
      candle_q_packed_hessian6_expand_shape in
  REWRITE_TAC[candle_q_packed_delta_neg_derivative_jet_six_def;
              candle_q_dim_jet_shape_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_q_packed_delta_neg_derivative_center_gradient_def;
              candle_q_dim_interval_list_neg_length;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_rows_width_all] THEN
  ACCEPT_TAC (CONJ center_row_length box_matrix_shape));;

let candle_q_packed_matrix_list_of_seq_lookup_contains = prove
 (`!n
     (interval_rows:((((num#num)#num)#((num#num)#num))list)list)
     (hessian:num->num->real) i j.
     ALL2 candle_q_stack_contains interval_rows
       (list_of_seq (\rowindex. list_of_seq (hessian rowindex) n) n) /\
     i < LENGTH interval_rows /\ i < n /\ j < n
     ==>
     candle_q_interval_contains
       (candle_q_interval_lookup j
         (candle_q_dim_interval_row_lookup i interval_rows))
       (hessian i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let row_lookup_rule =
      ISPECL
        [`i:num`;
         `candle_q_stack_contains:
            ((((num#num)#num)#((num#num)#num))list)->real list->bool`;
         `interval_rows:((((num#num)#num)#((num#num)#num))list)list`;
         `list_of_seq
            (\rowindex. list_of_seq
              ((hessian:num->num->real) rowindex) n) n`]
        candle_all2_el_lt in
  let row_lookup_premise =
      CONJ
        (ASSUME
          `ALL2 candle_q_stack_contains interval_rows
            (list_of_seq
              (\rowindex. list_of_seq
                ((hessian:num->num->real) rowindex) n) n)`)
        (ASSUME
          `i < LENGTH
            (interval_rows:
              ((((num#num)#num)#((num#num)#num))list)list)`) in
  let row_contains = MATCH_MP row_lookup_rule row_lookup_premise in
  let row_sequence_lookup =
    let sequence_rule =
      ISPECL
        [`(\rowindex. list_of_seq
             ((hessian:num->num->real) rowindex) n)`;
         `i:num`; `n:num`]
        EL_LIST_OF_SEQ in
    MATCH_MP sequence_rule (ASSUME `(i:num) < n`) in
  let row_contains =
    REWRITE_RULE[row_sequence_lookup] row_contains in
  let entry_lookup_rule =
      SPECL
        [`j:num`;
         `EL i interval_rows:
            ((((num#num)#num)#((num#num)#num))list)`;
         `list_of_seq ((hessian:num->num->real) i) n`]
        candle_q_stack_lookup_contains in
  let entry_contains = MATCH_MP entry_lookup_rule row_contains in
  MP_TAC entry_contains THEN
  ASM_SIMP_TAC[candle_q_dim_interval_row_lookup_in_range;
               candle_q_real_lookup_list_of_seq]);;

let candle_q_packed_delta_neg_derivative_jet_six_analytic_contains = prove
 (`!x0 x1 x2 x3 x4 x5 v0 v1 v2 v3 v4 v5 coordinate.
     candle_q_interval_contains x0 v0 /\
     candle_q_interval_contains x1 v1 /\
     candle_q_interval_contains x2 v2 /\
     candle_q_interval_contains x3 v3 /\
     candle_q_interval_contains x4 v4 /\
     candle_q_interval_contains x5 v5 /\
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_q_dim_analytic_contains 6
       (candle_q_packed_delta_neg_derivative_jet_six coordinate
         x0 x1 x2 x3 x4 x5)
       [v0;v1;v2;v3;v4;v5]
       (candle_packed_delta_neg_derivative_expr coordinate)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let coordinate_cases =
    ASSUME `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` in
  let state_premises =
    end_itlist CONJ
      (map ASSUME
        [`candle_q_interval_contains x0 v0`;
         `candle_q_interval_contains x1 v1`;
         `candle_q_interval_contains x2 v2`;
         `candle_q_interval_contains x3 v3`;
         `candle_q_interval_contains x4 v4`;
         `candle_q_interval_contains x5 v5`;
         `coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`]) in
  let value_contains =
    MATCH_MP
      (SPECL
        [`x0:((num#num)#num)#((num#num)#num)`;
         `x1:((num#num)#num)#((num#num)#num)`;
         `x2:((num#num)#num)#((num#num)#num)`;
         `x3:((num#num)#num)#((num#num)#num)`;
         `x4:((num#num)#num)#((num#num)#num)`;
         `x5:((num#num)#num)#((num#num)#num)`;
         `v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`]
        candle_q_packed_delta_neg_derivative_center_value_sound)
      state_premises in
  let gradient_contains =
    MATCH_MP
      (SPECL
        [`x0:((num#num)#num)#((num#num)#num)`;
         `x1:((num#num)#num)#((num#num)#num)`;
         `x2:((num#num)#num)#((num#num)#num)`;
         `x3:((num#num)#num)#((num#num)#num)`;
         `x4:((num#num)#num)#((num#num)#num)`;
         `x5:((num#num)#num)#((num#num)#num)`;
         `v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`]
        candle_q_packed_delta_neg_derivative_center_gradient_sound)
      state_premises in
  let packed_hessian_contains =
    MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`]
        candle_q_packed_delta_neg_derivative_hessian_six_sound)
      coordinate_cases in
  let matrix_contains =
    MATCH_MP
      (ISPECL
        [`candle_q_packed_delta_neg_derivative_hessian_six coordinate`;
         `(\rowindex colindex.
            candle_analytic_dd rowindex colindex
              [v0;v1;v2;v3;v4;v5]
              (candle_packed_delta_neg_derivative_expr coordinate))`]
        candle_q_packed_hessian6_expand_contains_symmetric_values)
      packed_hessian_contains in
  let matrix_contains =
    REWRITE_RULE[candle_q_symmetric_hessian6_analytic_values]
      matrix_contains in
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_packed_delta_neg_derivative_jet_six_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ACCEPT_TAC value_contains;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC
      (MATCH_MP
        (SPECL
          [`i:num`;
           `candle_q_packed_delta_neg_derivative_center_gradient coordinate
              x0 x1 x2 x3 x4 x5`;
           `list_of_seq
              (\derivative_coordinate.
                candle_analytic_d derivative_coordinate
                  [v0;v1;v2;v3;v4;v5]
                  (candle_packed_delta_neg_derivative_expr coordinate)) 6`]
          candle_q_stack_lookup_contains)
        gradient_contains) THEN
    ASM_SIMP_TAC[candle_q_real_lookup_list_of_seq];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC candle_q_packed_matrix_list_of_seq_lookup_contains THEN
    EXISTS_TAC `6` THEN
    ASM_REWRITE_TAC[candle_q_packed_hessian6_expand_shape] THEN
    MP_TAC matrix_contains THEN ASM_REWRITE_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_delta_neg_derivative_jet_six_shape;
     candle_q_packed_matrix_list_of_seq_lookup_contains;
     candle_q_packed_delta_neg_derivative_jet_six_analytic_contains] then
  failwith "packed negative delta derivative jet: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_NEG_DERIVATIVE_JET_OK DEVELOPMENT_NON_RELEASE";;

end;;
