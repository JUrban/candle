(* ========================================================================== *)
(* Representation correctness for tagged fixed/rational Taylor items.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_sound;;

(* Both logical payloads are carried, but only the one selected by [tag] is *)
(* encoded.  This avoids introducing an untrusted decoder for tagged cvals. *)

let candle_fsa_item_q_view_def = new_definition
 `candle_fsa_item_q_view tag fixed q_result =
    if tag then candle_fs_result_to_q fixed else q_result`;;

let candle_fsa_item_fixed_view_def = new_definition
 `candle_fsa_item_fixed_view tag fixed q_result =
    if tag then fixed else candle_fsa_result_of_q q_result`;;

let candle_cv_fsa_item_encode_def = new_definition
 `candle_cv_fsa_item_encode tag fixed q_result =
    if tag
    then candle_cv_fsa_item_fixed (candle_cv_fs_result fixed)
    else candle_cv_fsa_item_q
           (candle_cv_q_dim_taylor_model_result_encode q_result)`;;

let candle_cv_fsa_item_is_fixed_correct = prove
 (`!tag fixed q_result.
     candle_cv_fsa_item_is_fixed
       (candle_cv_fsa_item_encode tag fixed q_result) =
     candle_cv_bool tag`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `tag:bool` THEN
  REWRITE_TAC[candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_fixed_def; candle_cv_fsa_item_q_def;
              candle_cv_fsa_item_is_fixed_def; candle_cv_bool_def;
              cexp_fst_def; cexp_eq_def; injectivity "cval";
              NOT_SUC] THEN CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_fsa_item_to_q_correct = prove
 (`!tag fixed q_result.
     candle_cv_fsa_item_to_q
       (candle_cv_fsa_item_encode tag fixed q_result) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_fsa_item_q_view tag fixed q_result)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `tag:bool` THEN
  REWRITE_TAC[candle_cv_fsa_item_encode_def;
              candle_fsa_item_q_view_def;
              candle_cv_fsa_item_fixed_def; candle_cv_fsa_item_q_def;
              candle_cv_fsa_item_to_q_def;
              candle_cv_fsa_item_is_fixed_def;
              candle_cv_fsa_item_payload_def;
              candle_cv_fs_result_to_q_correct;
              cexp_fst_def; cexp_snd_def; cexp_eq_def; cexp_if_def;
              injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[cexp_if_def]);;

let candle_cv_fsa_item_to_fixed_correct = prove
 (`!tag fixed q_result.
     candle_cv_fsa_item_to_fixed
       (candle_cv_fsa_item_encode tag fixed q_result) =
     candle_cv_fs_result
       (candle_fsa_item_fixed_view tag fixed q_result)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `tag:bool` THEN
  REWRITE_TAC[candle_cv_fsa_item_encode_def;
              candle_fsa_item_fixed_view_def;
              candle_cv_fsa_item_fixed_def; candle_cv_fsa_item_q_def;
              candle_cv_fsa_item_to_fixed_def;
              candle_cv_fsa_item_is_fixed_def;
              candle_cv_fsa_item_payload_def;
              candle_cv_fsa_result_of_q_correct;
              cexp_fst_def; cexp_snd_def; cexp_eq_def; cexp_if_def;
              injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[cexp_if_def]);;

let candle_cv_fsa_item_neg_correct = prove
 (`!use_fixed radii tag fixed q_result.
     candle_cv_fsa_item_neg (candle_cv_bool use_fixed)
       (candle_cv_q_list radii)
       (candle_cv_fsa_item_encode tag fixed q_result) =
     candle_cv_fsa_item_encode use_fixed
       (candle_fs_result_neg (candle_fs_list_of_q radii)
         (candle_fsa_item_fixed_view tag fixed q_result))
       (candle_q_dim_taylor_model_result_neg radii
         (candle_fsa_item_q_view tag fixed q_result))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `use_fixed:bool` THEN
  REWRITE_TAC[candle_cv_fsa_item_neg_def;
              candle_cv_fsa_item_encode_def; candle_cv_bool_def;
              candle_cv_fsa_item_to_fixed_correct;
              candle_cv_fsa_item_to_q_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fs_result_neg_correct;
              candle_cv_q_dim_taylor_model_result_neg_correct;
              cexp_if_def]);;

let candle_cv_fsa_item_add_correct = prove
 (`!use_fixed radii left_tag left_fixed left_q
       right_tag right_fixed right_q.
     candle_cv_fsa_item_add (candle_cv_bool use_fixed)
       (candle_cv_q_list radii)
       (candle_cv_fsa_item_encode left_tag left_fixed left_q)
       (candle_cv_fsa_item_encode right_tag right_fixed right_q) =
     candle_cv_fsa_item_encode use_fixed
       (candle_fs_result_add (candle_fs_list_of_q radii)
         (candle_fsa_item_fixed_view left_tag left_fixed left_q)
         (candle_fsa_item_fixed_view right_tag right_fixed right_q))
       (candle_q_dim_taylor_model_result_add radii
         (candle_fsa_item_q_view left_tag left_fixed left_q)
         (candle_fsa_item_q_view right_tag right_fixed right_q))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `use_fixed:bool` THEN
  REWRITE_TAC[candle_cv_fsa_item_add_def;
              candle_cv_fsa_item_encode_def; candle_cv_bool_def;
              candle_cv_fsa_item_to_fixed_correct;
              candle_cv_fsa_item_to_q_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fs_result_add_correct;
              candle_cv_q_dim_taylor_model_result_add_correct;
              cexp_if_def]);;

let candle_cv_fsa_item_mul_correct = prove
 (`!radii left_tag left_fixed left_q right_tag right_fixed right_q.
     candle_cv_fsa_item_mul (candle_cv_q_list radii)
       (candle_cv_fsa_item_encode left_tag left_fixed left_q)
       (candle_cv_fsa_item_encode right_tag right_fixed right_q) =
     let result =
       candle_q_dim_taylor_model_result_mul radii
         (candle_fsa_item_q_view left_tag left_fixed left_q)
         (candle_fsa_item_q_view right_tag right_fixed right_q) in
     candle_cv_fsa_item_encode F (candle_fsa_result_of_q result) result`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; candle_cv_fsa_item_mul_def;
              candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_to_q_correct;
              candle_cv_q_dim_taylor_model_result_mul_correct]);;

let candle_cv_fsa_item_square_correct = prove
 (`!radii tag fixed q_result.
     candle_cv_fsa_item_square (candle_cv_q_list radii)
       (candle_cv_fsa_item_encode tag fixed q_result) =
     let result =
       candle_q_dim_taylor_model_result_square radii
         (candle_fsa_item_q_view tag fixed q_result) in
     candle_cv_fsa_item_encode F (candle_fsa_result_of_q result) result`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; candle_cv_fsa_item_square_def;
              candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_to_q_correct;
              candle_cv_q_dim_taylor_model_result_square_correct]);;

let candle_cv_fsa_item_sqrt_correct = prove
 (`!radii center_s box_s tag fixed q_result.
     candle_cv_fsa_item_sqrt (candle_cv_q_list radii)
       (candle_cv_q_interval center_s) (candle_cv_q_interval box_s)
       (candle_cv_fsa_item_encode tag fixed q_result) =
     let result =
       candle_q_dim_taylor_model_result_sqrt radii center_s box_s
         (candle_fsa_item_q_view tag fixed q_result) in
     candle_cv_fsa_item_encode F (candle_fsa_result_of_q result) result`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; candle_cv_fsa_item_sqrt_def;
              candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_to_q_correct;
              candle_cv_q_dim_taylor_model_result_sqrt_correct]);;

let candle_cv_fsa_item_inv_correct = prove
 (`!radii tag fixed q_result.
     candle_cv_fsa_item_inv (candle_cv_q_list radii)
       (candle_cv_fsa_item_encode tag fixed q_result) =
     let result =
       candle_q_dim_taylor_model_result_inv radii
         (candle_fsa_item_q_view tag fixed q_result) in
     candle_cv_fsa_item_encode F (candle_fsa_result_of_q result) result`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; candle_cv_fsa_item_inv_def;
              candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_to_q_correct;
              candle_cv_q_dim_taylor_model_result_inv_correct]);;

let candle_cv_fsa_item_atn_correct = prove
 (`!radii tag fixed q_result.
     candle_cv_fsa_item_atn (candle_cv_q_list radii)
       (candle_cv_fsa_item_encode tag fixed q_result) =
     let result =
       candle_q_dim_taylor_model_result_atn radii
         (candle_fsa_item_q_view tag fixed q_result) in
     candle_cv_fsa_item_encode F (candle_fsa_result_of_q result) result`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; candle_cv_fsa_item_atn_def;
              candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_to_q_correct;
              candle_cv_q_dim_taylor_model_result_atn_correct]);;

let candle_cv_fsa_item_pi_half_correct = prove
 (`!radii center_boxes boxes.
     candle_cv_fsa_item_pi_half (candle_cv_q_list radii)
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes) =
     let result =
       candle_q_dim_taylor_model_result_pi_half radii center_boxes boxes in
     candle_cv_fsa_item_encode F (candle_fsa_result_of_q result) result`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; candle_cv_fsa_item_pi_half_def;
              candle_cv_fsa_item_encode_def;
              candle_cv_q_dim_taylor_model_result_pi_half_correct]);;

end;;
