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

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_products_sum2_correct;
     candle_cv_q_packed_object_products_sum4_correct;
     candle_cv_q_packed_object_fused_scale_add_map2_correct;
     candle_cv_q_packed_object_fused_scale_add_correct] then
  failwith "packed object multiplication compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_MUL_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
