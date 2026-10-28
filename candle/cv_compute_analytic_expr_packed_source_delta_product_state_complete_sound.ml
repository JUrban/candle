(* ========================================================================== *)
(* Whole-box Hessian soundness for the optimized [4 * x_i * delta] family.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This joins the proved compact product-Hessian *)
(* operation to the analytic second derivatives of the coordinate-parametric *)
(* source expression.                                                        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_product_state_sound.ml";;

module Candle_cv_analytic_expr_packed_source_delta_product_state_complete_sound = struct

open Candle_cv_polynomial_expr_diff;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_product_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_product_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_product_state_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;

let candle_q_packed_delta_product_hessian_six_def = new_definition
 `candle_q_packed_delta_product_hessian_six coordinate box_coordinate
      delta_gradient delta_hessian =
    candle_q_packed_delta_product_hessian coordinate box_coordinate
      delta_gradient candle_q_packed_delta_hessian_indices delta_hessian`;;

let candle_real_packed_delta_hessian_six_length = prove
 (`!v0 v1 v2 v3 v4 v5.
     LENGTH (candle_real_packed_delta_hessian_six v0 v1 v2 v3 v4 v5) =
     21`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_real_packed_delta_hessian_six_def;
              candle_real_packed_delta_hessian_rows_six_def;
              candle_real_packed_delta_sums_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_product_list_eq_list_of_seq_el_21 = prove
 (`!items:A list.
     LENGTH items = 21
     ==> items = list_of_seq (\lookup_index. EL lookup_index items) 21`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `lookup_index:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

let candle_packed_delta_product_analytic_hessian_six = prove
 (`!v0 v1 v2 v3 v4 v5 coordinate.
     coordinate < 6
     ==>
     candle_q_packed_hessian6_values
       (\rowindex colindex.
         candle_analytic_dd rowindex colindex
           [v0;v1;v2;v3;v4;v5]
           (candle_packed_delta_product_expr coordinate)) =
     candle_real_packed_delta_product_hessian coordinate
       (candle_q_real_lookup coordinate [v0;v1;v2;v3;v4;v5])
       (candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5)
       candle_q_packed_delta_hessian_indices
       (candle_real_packed_delta_hessian_six v0 v1 v2 v3 v4 v5)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  let reconstruction =
    MATCH_MP
      (ISPEC
        `candle_real_packed_delta_hessian_six v0 v1 v2 v3 v4 v5`
        candle_product_list_eq_list_of_seq_el_21)
      (SPECL [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;
              `v5:real`]
        candle_real_packed_delta_hessian_six_length) in
  let coordinate_lt = ASSUME `coordinate < 6` in
  let component rowindex colindex =
    let bounds =
      prove
       (vsubst
         [rowindex,`rowindex:num`; colindex,`colindex:num`]
         `rowindex < 6 /\ rowindex <= colindex /\ colindex < 6`,
        CONV_TAC NUM_REDUCE_CONV) in
    MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`; rowindex; colindex]
        candle_packed_delta_product_analytic_dd_upper)
      (CONJ coordinate_lt bounds) in
  let components =
    map
      (fun (rowindex,colindex) ->
        component (mk_small_numeral rowindex) (mk_small_numeral colindex))
      [(0,0);(0,1);(0,2);(0,3);(0,4);(0,5);
       (1,1);(1,2);(1,3);(1,4);(1,5);
       (2,2);(2,3);(2,4);(2,5);
       (3,3);(3,4);(3,5);(4,4);(4,5);(5,5)] in
  ONCE_REWRITE_TAC[reconstruction] THEN
  REWRITE_TAC[candle_q_packed_hessian6_values_def] THEN
  EVERY (map (fun theorem -> ONCE_REWRITE_TAC[theorem]) components) THEN
  REWRITE_TAC[candle_q_packed_delta_hessian_indices_def;
              candle_real_packed_delta_product_hessian_def;
              candle_packed_delta_hessian_upper_index_def;
              FST; SND; num_CONV `21`;
              num_CONV `20`; num_CONV `19`; num_CONV `18`;
              num_CONV `17`; num_CONV `16`; num_CONV `15`;
              num_CONV `14`; num_CONV `13`; num_CONV `12`;
              num_CONV `11`; num_CONV `10`; num_CONV `9`;
              num_CONV `8`; num_CONV `7`; num_CONV `6`;
              num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_delta_product_hessian_six_sound = prove
 (`!v0 v1 v2 v3 v4 v5 coordinate box_coordinate delta_gradient
       delta_hessian.
     coordinate < 6 /\
     candle_q_interval_contains box_coordinate
       (candle_q_real_lookup coordinate [v0;v1;v2;v3;v4;v5]) /\
     candle_q_stack_contains delta_gradient
       (candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5) /\
     candle_q_stack_contains delta_hessian
       (candle_real_packed_delta_hessian_six v0 v1 v2 v3 v4 v5)
     ==>
     candle_q_stack_contains
       (candle_q_packed_delta_product_hessian_six coordinate
         box_coordinate delta_gradient delta_hessian)
       (candle_q_packed_hessian6_values
         (\rowindex colindex.
           candle_analytic_dd rowindex colindex
             [v0;v1;v2;v3;v4;v5]
             (candle_packed_delta_product_expr coordinate)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let analytic_table =
    MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `coordinate:num`]
        candle_packed_delta_product_analytic_hessian_six)
      (ASSUME `coordinate < 6`) in
  REWRITE_TAC[candle_q_packed_delta_product_hessian_six_def;
              candle_q_stack_contains_all2] THEN
  ONCE_REWRITE_TAC[analytic_table] THEN
  MATCH_MP_TAC candle_q_packed_delta_product_hessian_sound THEN
  ASM_REWRITE_TAC[GSYM candle_q_stack_contains_all2]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_real_packed_delta_hessian_six_length;
     candle_product_list_eq_list_of_seq_el_21;
     candle_packed_delta_product_analytic_hessian_six;
     candle_q_packed_delta_product_hessian_six_sound] then
  failwith "packed source delta product complete state: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_PRODUCT_STATE_COMPLETE_OK DEVELOPMENT_NON_RELEASE";;

end;;
