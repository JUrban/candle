(* ========================================================================== *)
(* Executable exact object-q fused products and gradient multiplication.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The association order is the exact HOL4      *)
(* object-q order: start at the zero interval and accumulate two or four     *)
(* interval products from left to right.  No rational normalization is added. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_linear_compute.ml";;

module Candle_cv_analytic_expr_packed_source_object_mul_compute = struct

open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_packed_source_delta_value;;
open Candle_cv_analytic_expr_packed_source_object_mul_sound;;
open Candle_cv_analytic_expr_packed_source_object_linear_compute;;

let candle_cv_q_packed_object_products_sum2_def = new_definition
 `candle_cv_q_packed_object_products_sum2
      first_left first_right second_left second_right =
    candle_cv_q_interval_add
      (candle_cv_q_interval_add candle_cv_q_zero_interval
        (candle_cv_q_interval_mul first_left first_right))
      (candle_cv_q_interval_mul second_left second_right)`;;

let candle_cv_q_packed_object_products_sum2_correct = prove
 (`!first_left first_right second_left second_right.
     candle_cv_q_packed_object_products_sum2
       (candle_cv_q_interval first_left)
       (candle_cv_q_interval first_right)
       (candle_cv_q_interval second_left)
       (candle_cv_q_interval second_right) =
     candle_cv_q_interval
       (candle_q_packed_object_products_sum2
         first_left first_right second_left second_right)`,
  REWRITE_TAC[candle_cv_q_packed_object_products_sum2_def;
              candle_q_packed_object_products_sum2_def;
              candle_cv_q_zero_interval_correct;
              candle_cv_q_interval_mul_correct;
              candle_cv_q_interval_add_correct]);;

let _ = print_endline "CANDLE_OBJECT_MUL_STAGE products-sum2";;

let candle_cv_q_packed_object_products_sum4_def = new_definition
 `candle_cv_q_packed_object_products_sum4
      first_left first_right second_left second_right
      third_left third_right fourth_left fourth_right =
    candle_cv_q_interval_add
      (candle_cv_q_interval_add
        (candle_cv_q_interval_add
          (candle_cv_q_interval_add candle_cv_q_zero_interval
            (candle_cv_q_interval_mul first_left first_right))
          (candle_cv_q_interval_mul second_left second_right))
        (candle_cv_q_interval_mul third_left third_right))
      (candle_cv_q_interval_mul fourth_left fourth_right)`;;

let candle_cv_q_packed_object_products_sum4_correct = prove
 (`!first_left first_right second_left second_right
       third_left third_right fourth_left fourth_right.
     candle_cv_q_packed_object_products_sum4
       (candle_cv_q_interval first_left)
       (candle_cv_q_interval first_right)
       (candle_cv_q_interval second_left)
       (candle_cv_q_interval second_right)
       (candle_cv_q_interval third_left)
       (candle_cv_q_interval third_right)
       (candle_cv_q_interval fourth_left)
       (candle_cv_q_interval fourth_right) =
     candle_cv_q_interval
       (candle_q_packed_object_products_sum4
         first_left first_right second_left second_right
         third_left third_right fourth_left fourth_right)`,
  REWRITE_TAC[candle_cv_q_packed_object_products_sum4_def;
              candle_q_packed_object_products_sum4_def;
              candle_cv_q_zero_interval_correct;
              candle_cv_q_interval_mul_correct;
              candle_cv_q_interval_add_correct]);;

let _ = print_endline "CANDLE_OBJECT_MUL_STAGE products-sum4";;

let candle_cv_q_packed_object_fused_scale_add_def = define
 `(candle_cv_q_packed_object_fused_scale_add
     left_scale (Cexp_num n) right_scale right = Cexp_num 0) /\
  (candle_cv_q_packed_object_fused_scale_add
     left_scale (Cexp_pair left_entry left_rest)
     right_scale (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_packed_object_fused_scale_add
     left_scale (Cexp_pair left_entry left_rest)
     right_scale (Cexp_pair right_entry right_rest) =
     Cexp_pair
       (candle_cv_q_packed_object_products_sum2
         left_scale left_entry right_scale right_entry)
       (candle_cv_q_packed_object_fused_scale_add
         left_scale left_rest right_scale right_rest))`;;

let candle_cv_q_packed_object_fused_scale_add_map2_correct = prove
 (`!left_scale right_scale left right.
     LENGTH left = LENGTH right
     ==>
     candle_cv_q_packed_object_fused_scale_add
       (candle_cv_q_interval left_scale)
       (candle_cv_q_interval_list left)
       (candle_cv_q_interval right_scale)
       (candle_cv_q_interval_list right) =
     candle_cv_q_interval_list
       (MAP2
         (\left_entry right_entry.
           candle_q_packed_object_products_sum2
             left_scale left_entry right_scale right_entry)
         left right)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
              candle_cv_q_interval_list_def;
              candle_cv_q_packed_object_fused_scale_add_def;
              MAP2_DEF; HD; TL;
              candle_cv_q_packed_object_products_sum2_correct] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[]);;

let candle_cv_q_packed_object_fused_scale_add_correct = prove
 (`!left_scale right_scale left right.
     LENGTH left = LENGTH right
     ==>
     candle_cv_q_packed_object_fused_scale_add
       (candle_cv_q_interval left_scale)
       (candle_cv_q_interval_list left)
       (candle_cv_q_interval right_scale)
       (candle_cv_q_interval_list right) =
     candle_cv_q_interval_list
       (candle_q_packed_object_fused_scale_add
         left_scale left right_scale right)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_packed_object_fused_scale_add_def] THEN
  MATCH_MP_TAC candle_cv_q_packed_object_fused_scale_add_map2_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_MUL_STAGE fused-scale-add";;

(* A numeric packed-Hessian index is decoded to its upper-triangular row and *)
(* column.  The total defaults at indices above 20 are inherited unchanged   *)
(* from the logical object function; the public builder uses exactly 0..20.  *)

let candle_cv_q_packed_object_hessian6_row_def = new_definition
 `candle_cv_q_packed_object_hessian6_row selector =
    Cexp_if (Cexp_less selector (Cexp_num 6)) (Cexp_num 0)
      (Cexp_if (Cexp_less selector (Cexp_num 11)) (Cexp_num 1)
        (Cexp_if (Cexp_less selector (Cexp_num 15)) (Cexp_num 2)
          (Cexp_if (Cexp_less selector (Cexp_num 18)) (Cexp_num 3)
            (Cexp_if (Cexp_less selector (Cexp_num 20))
              (Cexp_num 4) (Cexp_num 5)))))`;;

let candle_cv_q_packed_object_hessian6_col_def = new_definition
 `candle_cv_q_packed_object_hessian6_col selector =
    Cexp_if (Cexp_less selector (Cexp_num 6)) selector
      (Cexp_if (Cexp_less selector (Cexp_num 11))
        (Cexp_sub selector (Cexp_num 5))
        (Cexp_if (Cexp_less selector (Cexp_num 15))
          (Cexp_sub selector (Cexp_num 9))
          (Cexp_if (Cexp_less selector (Cexp_num 18))
            (Cexp_sub selector (Cexp_num 12))
            (Cexp_if (Cexp_less selector (Cexp_num 20))
              (Cexp_sub selector (Cexp_num 14)) (Cexp_num 5)))))`;;

let candle_cv_if_num_less_correct = prove
 (`!left right consequent alternative.
     Cexp_if (Cexp_less (Cexp_num left) (Cexp_num right))
       consequent alternative =
     if left < right then consequent else alternative`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cexp_less_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]);;

let _ = print_endline "CANDLE_OBJECT_MUL_STAGE less-helper";;

let candle_cv_q_packed_object_hessian6_row_correct = prove
 (`!selector.
     candle_cv_q_packed_object_hessian6_row (Cexp_num selector) =
     Cexp_num (candle_q_packed_object_hessian6_row selector)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_object_hessian6_row_def;
              candle_q_packed_object_hessian6_row_def;
              candle_cv_if_num_less_correct] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]));;

let _ = print_endline "CANDLE_OBJECT_MUL_STAGE hessian-row";;

let candle_cv_q_packed_object_hessian6_col_correct = prove
 (`!selector.
     candle_cv_q_packed_object_hessian6_col (Cexp_num selector) =
     Cexp_num (candle_q_packed_object_hessian6_col selector)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_object_hessian6_col_def;
              candle_q_packed_object_hessian6_col_def;
              candle_cv_if_num_less_correct; cexp_sub_def] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]));;

let _ = print_endline "CANDLE_OBJECT_MUL_STAGE hessian-coordinates";;

let candle_q_packed_object_mul_hessian6_entry_index_def = new_definition
 `candle_q_packed_object_mul_hessian6_entry_index
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian selector =
    candle_q_packed_object_fused_hessian_entry
      left_value right_value
      (candle_q_interval_lookup selector left_hessian)
      (candle_q_interval_lookup selector right_hessian)
      (candle_q_packed_object_symmetric_product_pair
        left_gradient right_gradient
        (candle_q_packed_object_hessian6_row selector)
        (candle_q_packed_object_hessian6_col selector))`;;

let candle_cv_q_packed_object_mul_hessian6_entry_index_def = new_definition
 `candle_cv_q_packed_object_mul_hessian6_entry_index
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian selector =
    candle_cv_q_packed_object_products_sum4
      right_value (candle_cv_q_interval_lookup selector left_hessian)
      (candle_cv_q_interval_lookup
        (candle_cv_q_packed_object_hessian6_row selector) left_gradient)
      (candle_cv_q_interval_lookup
        (candle_cv_q_packed_object_hessian6_col selector) right_gradient)
      (candle_cv_q_interval_lookup
        (candle_cv_q_packed_object_hessian6_row selector) right_gradient)
      (candle_cv_q_interval_lookup
        (candle_cv_q_packed_object_hessian6_col selector) left_gradient)
      left_value (candle_cv_q_interval_lookup selector right_hessian)`;;

let candle_cv_q_packed_object_mul_hessian6_entry_index_correct = prove
 (`!left_value right_value left_gradient right_gradient
       left_hessian right_hessian selector.
     candle_cv_q_packed_object_mul_hessian6_entry_index
       (candle_cv_q_interval left_value)
       (candle_cv_q_interval right_value)
       (candle_cv_q_interval_list left_gradient)
       (candle_cv_q_interval_list right_gradient)
       (candle_cv_q_interval_list left_hessian)
       (candle_cv_q_interval_list right_hessian)
       (Cexp_num selector) =
     candle_cv_q_interval
       (candle_q_packed_object_mul_hessian6_entry_index
         left_value right_value left_gradient right_gradient
         left_hessian right_hessian selector)`,
  REWRITE_TAC
    [candle_cv_q_packed_object_mul_hessian6_entry_index_def;
     candle_q_packed_object_mul_hessian6_entry_index_def;
     candle_q_packed_object_fused_hessian_entry_def;
     candle_q_packed_object_symmetric_product_pair_def; FST; SND;
     candle_cv_q_packed_object_hessian6_row_correct;
     candle_cv_q_packed_object_hessian6_col_correct;
     candle_cv_q_interval_lookup_correct;
     candle_cv_q_packed_object_products_sum4_correct]);;

let _ = print_endline "CANDLE_OBJECT_MUL_STAGE hessian-entry";;

(* Fixed 6+6+6+3 blocks keep construction of the 21-entry executable
   Hessian cheap while preserving the logical list order exactly. *)

let candle_cv_q_packed_object_interval_list_append_def = define
 `(candle_cv_q_packed_object_interval_list_append (Cexp_num n) right =
     right) /\
  (candle_cv_q_packed_object_interval_list_append
     (Cexp_pair head tail) right =
     Cexp_pair head
       (candle_cv_q_packed_object_interval_list_append tail right))`;;

let candle_cv_q_packed_object_interval_list_append_correct = prove
 (`!left right.
     candle_cv_q_packed_object_interval_list_append
       (candle_cv_q_interval_list left)
       (candle_cv_q_interval_list right) =
     candle_cv_q_interval_list (APPEND left right)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_packed_object_interval_list_append_def;
     candle_cv_q_interval_list_def; APPEND]);;

let candle_q_packed_object_mul_hessian6_block6_def = new_definition
 `candle_q_packed_object_mul_hessian6_block6
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian selector =
    [candle_q_packed_object_mul_hessian6_entry_index
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian selector;
     candle_q_packed_object_mul_hessian6_entry_index
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 1);
     candle_q_packed_object_mul_hessian6_entry_index
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 2);
     candle_q_packed_object_mul_hessian6_entry_index
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 3);
     candle_q_packed_object_mul_hessian6_entry_index
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 4);
     candle_q_packed_object_mul_hessian6_entry_index
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 5)]`;;

let candle_q_packed_object_mul_hessian6_block3_def = new_definition
 `candle_q_packed_object_mul_hessian6_block3
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian selector =
    [candle_q_packed_object_mul_hessian6_entry_index
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian selector;
     candle_q_packed_object_mul_hessian6_entry_index
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 1);
     candle_q_packed_object_mul_hessian6_entry_index
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian (selector + 2)]`;;

let candle_cv_q_packed_object_mul_hessian6_block6_def = new_definition
 `candle_cv_q_packed_object_mul_hessian6_block6
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian selector =
    candle_cv_q_packed_delta_six
      (candle_cv_q_packed_object_mul_hessian6_entry_index
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian selector)
      (candle_cv_q_packed_object_mul_hessian6_entry_index
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian (Cexp_add selector (Cexp_num 1)))
      (candle_cv_q_packed_object_mul_hessian6_entry_index
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian (Cexp_add selector (Cexp_num 2)))
      (candle_cv_q_packed_object_mul_hessian6_entry_index
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian (Cexp_add selector (Cexp_num 3)))
      (candle_cv_q_packed_object_mul_hessian6_entry_index
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian (Cexp_add selector (Cexp_num 4)))
      (candle_cv_q_packed_object_mul_hessian6_entry_index
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian (Cexp_add selector (Cexp_num 5)))`;;

let candle_cv_q_packed_object_mul_hessian6_block3_def = new_definition
 `candle_cv_q_packed_object_mul_hessian6_block3
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian selector =
    Cexp_pair
      (candle_cv_q_packed_object_mul_hessian6_entry_index
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian selector)
      (Cexp_pair
        (candle_cv_q_packed_object_mul_hessian6_entry_index
          left_value right_value left_gradient right_gradient
          left_hessian right_hessian (Cexp_add selector (Cexp_num 1)))
        (Cexp_pair
          (candle_cv_q_packed_object_mul_hessian6_entry_index
            left_value right_value left_gradient right_gradient
            left_hessian right_hessian (Cexp_add selector (Cexp_num 2)))
          (Cexp_num 0)))`;;

let candle_cv_q_packed_object_mul_hessian6_block6_correct = prove
 (`!left_value right_value left_gradient right_gradient
       left_hessian right_hessian selector.
     candle_cv_q_packed_object_mul_hessian6_block6
       (candle_cv_q_interval left_value)
       (candle_cv_q_interval right_value)
       (candle_cv_q_interval_list left_gradient)
       (candle_cv_q_interval_list right_gradient)
       (candle_cv_q_interval_list left_hessian)
       (candle_cv_q_interval_list right_hessian)
       (Cexp_num selector) =
     candle_cv_q_interval_list
       (candle_q_packed_object_mul_hessian6_block6
         left_value right_value left_gradient right_gradient
         left_hessian right_hessian selector)`,
  REWRITE_TAC
    [candle_cv_q_packed_object_mul_hessian6_block6_def;
     candle_q_packed_object_mul_hessian6_block6_def;
     cexp_add_def;
     candle_cv_q_packed_delta_six_correct;
     candle_cv_q_packed_object_mul_hessian6_entry_index_correct]);;

let candle_cv_q_packed_object_mul_hessian6_block3_correct = prove
 (`!left_value right_value left_gradient right_gradient
       left_hessian right_hessian selector.
     candle_cv_q_packed_object_mul_hessian6_block3
       (candle_cv_q_interval left_value)
       (candle_cv_q_interval right_value)
       (candle_cv_q_interval_list left_gradient)
       (candle_cv_q_interval_list right_gradient)
       (candle_cv_q_interval_list left_hessian)
       (candle_cv_q_interval_list right_hessian)
       (Cexp_num selector) =
     candle_cv_q_interval_list
       (candle_q_packed_object_mul_hessian6_block3
         left_value right_value left_gradient right_gradient
         left_hessian right_hessian selector)`,
  REWRITE_TAC
    [candle_cv_q_packed_object_mul_hessian6_block3_def;
     candle_q_packed_object_mul_hessian6_block3_def;
     cexp_add_def; candle_cv_q_interval_list_def;
     candle_cv_q_packed_object_mul_hessian6_entry_index_correct]);;

let candle_q_packed_object_mul_hessian6_entries_def = new_definition
 `candle_q_packed_object_mul_hessian6_entries
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian =
    APPEND
      (candle_q_packed_object_mul_hessian6_block6
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian 0)
      (APPEND
        (candle_q_packed_object_mul_hessian6_block6
          left_value right_value left_gradient right_gradient
          left_hessian right_hessian 6)
        (APPEND
          (candle_q_packed_object_mul_hessian6_block6
            left_value right_value left_gradient right_gradient
            left_hessian right_hessian 12)
          (candle_q_packed_object_mul_hessian6_block3
            left_value right_value left_gradient right_gradient
            left_hessian right_hessian 18)))`;;

let candle_cv_q_packed_object_mul_hessian6_entries_def = new_definition
 `candle_cv_q_packed_object_mul_hessian6_entries
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian =
    candle_cv_q_packed_object_interval_list_append
      (candle_cv_q_packed_object_mul_hessian6_block6
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian (Cexp_num 0))
      (candle_cv_q_packed_object_interval_list_append
        (candle_cv_q_packed_object_mul_hessian6_block6
          left_value right_value left_gradient right_gradient
          left_hessian right_hessian (Cexp_num 6))
        (candle_cv_q_packed_object_interval_list_append
          (candle_cv_q_packed_object_mul_hessian6_block6
            left_value right_value left_gradient right_gradient
            left_hessian right_hessian (Cexp_num 12))
          (candle_cv_q_packed_object_mul_hessian6_block3
            left_value right_value left_gradient right_gradient
            left_hessian right_hessian (Cexp_num 18))))`;;

let candle_cv_q_packed_object_mul_hessian6_entries_correct = prove
 (`!left_value right_value left_gradient right_gradient
       left_hessian right_hessian.
     candle_cv_q_packed_object_mul_hessian6_entries
       (candle_cv_q_interval left_value)
       (candle_cv_q_interval right_value)
       (candle_cv_q_interval_list left_gradient)
       (candle_cv_q_interval_list right_gradient)
       (candle_cv_q_interval_list left_hessian)
       (candle_cv_q_interval_list right_hessian) =
     candle_cv_q_interval_list
       (candle_q_packed_object_mul_hessian6_entries
         left_value right_value left_gradient right_gradient
         left_hessian right_hessian)`,
  REWRITE_TAC
    [candle_cv_q_packed_object_mul_hessian6_entries_def;
     candle_q_packed_object_mul_hessian6_entries_def;
     candle_cv_q_packed_object_mul_hessian6_block6_correct;
     candle_cv_q_packed_object_mul_hessian6_block3_correct;
     candle_cv_q_packed_object_interval_list_append_correct]);;

let _ = print_endline "CANDLE_OBJECT_MUL_STAGE hessian-fixed-entries";;

let candle_q_packed_object_mul_hessian6_entries_sequence = prove
 (`!left_value right_value left_gradient right_gradient
       left_hessian right_hessian.
     candle_q_packed_object_mul_hessian6_entries
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian =
     list_of_seq
       (\selector.
         candle_q_packed_object_mul_hessian6_entry_index
           left_value right_value left_gradient right_gradient
           left_hessian right_hessian selector) 21`,
  REPEAT GEN_TAC THEN
  let numeral_conversions =
    map (fun numeral -> num_CONV (mk_small_numeral numeral)) (1--21) in
  REWRITE_TAC
    ([candle_q_packed_object_mul_hessian6_entries_def;
      candle_q_packed_object_mul_hessian6_block6_def;
      candle_q_packed_object_mul_hessian6_block3_def;
      list_of_seq; APPEND] @ numeral_conversions) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_object_mul_hessian6_entries_eq = prove
 (`!left_value right_value left_gradient right_gradient
       left_hessian right_hessian.
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21
     ==>
     candle_q_packed_object_mul_hessian6_entries
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian =
     candle_q_packed_object_mul_hessian6
       left_value right_value left_gradient right_gradient
       left_hessian right_hessian`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `LENGTH
      (candle_q_packed_object_mul_hessian6
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian) = 21`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_q_packed_object_mul_hessian6_length THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[candle_q_packed_object_mul_hessian6_entries_sequence] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `selector:num` THEN DISCH_TAC THEN
  REWRITE_TAC[EL_LIST_OF_SEQ] THEN
  SUBGOAL_THEN
   `EL selector
      (candle_q_packed_object_mul_hessian6
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian) =
    candle_q_interval_lookup selector
      (candle_q_packed_object_mul_hessian6
        left_value right_value left_gradient right_gradient
        left_hessian right_hessian)`
   SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC candle_q_interval_lookup_in_range THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC
    [candle_q_packed_object_mul_hessian6_lookup;
     candle_q_packed_object_symmetric_product_pairs6_def;
     EL_LIST_OF_SEQ;
     candle_q_packed_object_mul_hessian6_entry_index_def]);;

let _ = print_endline "CANDLE_OBJECT_MUL_STAGE hessian-fixed-equality";;

let candle_cv_q_packed_object_mul_hessian6_def = new_definition
 `candle_cv_q_packed_object_mul_hessian6
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian =
    candle_cv_q_packed_object_mul_hessian6_entries
      left_value right_value left_gradient right_gradient
      left_hessian right_hessian`;;

let candle_cv_q_packed_object_mul_hessian6_correct = prove
 (`!left_value right_value left_gradient right_gradient
       left_hessian right_hessian.
     LENGTH left_hessian = 21 /\ LENGTH right_hessian = 21
     ==>
     candle_cv_q_packed_object_mul_hessian6
       (candle_cv_q_interval left_value)
       (candle_cv_q_interval right_value)
       (candle_cv_q_interval_list left_gradient)
       (candle_cv_q_interval_list right_gradient)
       (candle_cv_q_interval_list left_hessian)
       (candle_cv_q_interval_list right_hessian) =
     candle_cv_q_interval_list
       (candle_q_packed_object_mul_hessian6
         left_value right_value left_gradient right_gradient
         left_hessian right_hessian)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_object_mul_hessian6_def;
              candle_cv_q_packed_object_mul_hessian6_entries_correct] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC candle_q_packed_object_mul_hessian6_entries_eq THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_MUL_STAGE hessian-complete";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_products_sum2_correct;
     candle_cv_q_packed_object_products_sum4_correct;
     candle_cv_q_packed_object_fused_scale_add_map2_correct;
     candle_cv_q_packed_object_fused_scale_add_correct;
     candle_cv_if_num_less_correct;
     candle_cv_q_packed_object_hessian6_row_correct;
     candle_cv_q_packed_object_hessian6_col_correct;
     candle_cv_q_packed_object_mul_hessian6_entry_index_correct;
     candle_cv_q_packed_object_interval_list_append_correct;
     candle_cv_q_packed_object_mul_hessian6_block6_correct;
     candle_cv_q_packed_object_mul_hessian6_block3_correct;
     candle_cv_q_packed_object_mul_hessian6_entries_correct;
     candle_q_packed_object_mul_hessian6_entries_sequence;
     candle_q_packed_object_mul_hessian6_entries_eq;
     candle_cv_q_packed_object_mul_hessian6_correct] then
  failwith "packed object multiplication compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_MUL_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
