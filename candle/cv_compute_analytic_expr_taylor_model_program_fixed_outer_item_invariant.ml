(* ========================================================================== *)
(* Representation and analytic invariant for fixed-outer tagged items.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_invariant.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_item_invariant = struct

open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_invariant;;

(* The executable retains a fixed payload after multiplication and square.
   The rational payload below is deliberately redundant: a true tag means
   that encoding and all logical views select the authenticated fixed result. *)

let candle_cv_fso_item_mul_correct = prove
 (`!radii left_tag left_fixed left_q right_tag right_fixed right_q.
     candle_cv_fso_item_mul (candle_cv_q_list radii)
       (candle_cv_fsa_item_encode left_tag left_fixed left_q)
       (candle_cv_fsa_item_encode right_tag right_fixed right_q) =
     let result =
       candle_fs_result_mul (candle_fs_list_of_q radii)
         (candle_fsa_item_fixed_view left_tag left_fixed left_q)
         (candle_fsa_item_fixed_view right_tag right_fixed right_q) in
     candle_cv_fsa_item_encode T result (candle_fs_result_to_q result)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF;
              candle_cv_fso_item_mul_def;
              candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_to_fixed_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fs_result_mul_correct]);;

let candle_cv_fso_item_square_correct = prove
 (`!radii tag fixed q_result.
     candle_cv_fso_item_square (candle_cv_q_list radii)
       (candle_cv_fsa_item_encode tag fixed q_result) =
     let result =
       candle_fs_result_square (candle_fs_list_of_q radii)
         (candle_fsa_item_fixed_view tag fixed q_result) in
     candle_cv_fsa_item_encode T result (candle_fs_result_to_q result)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF;
              candle_cv_fso_item_square_def;
              candle_cv_fsa_item_encode_def;
              candle_cv_fsa_item_to_fixed_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fs_result_square_correct]);;

let candle_fso_item_mul_analytic_invariant = prove
 (`!center_a center_b box_a box_b boxes
      left_tag left_fixed left_q right_tag right_fixed right_q
      (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_a /\
     candle_analytic_valid_dim (dimindex (:N)) box_b /\
     candle_analytic_erase_sqrt_certificates center_a =
       candle_analytic_erase_sqrt_certificates box_a /\
     candle_analytic_erase_sqrt_certificates center_b =
       candle_analytic_erase_sqrt_certificates box_b /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_item_analytic_invariant type_witness boxes
       left_tag left_fixed left_q center_a box_a /\
     candle_fsa_item_analytic_invariant type_witness boxes
       right_tag right_fixed right_q center_b box_b
     ==>
     let result =
       candle_fs_result_mul
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)))
         (candle_fsa_item_fixed_view left_tag left_fixed left_q)
         (candle_fsa_item_fixed_view right_tag right_fixed right_q) in
     candle_fsa_item_analytic_invariant type_witness boxes T result
       (candle_fs_result_to_q result)
       (Candle_analytic_mul center_a center_b)
       (Candle_analytic_mul box_a box_b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM
   (fun right_th ->
      POP_ASSUM
       (fun left_th ->
          LABEL_TAC "left_item_invariant" left_th THEN
          LABEL_TAC "right_item_invariant" right_th)) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF;
              candle_fsa_item_analytic_invariant_def;
              candle_fsa_item_q_view_def] THEN
  MATCH_MP_TAC candle_fs_result_mul_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fsa_item_fixed_view_analytic_invariant THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "left_item_invariant" ACCEPT_TAC;
    MATCH_MP_TAC candle_fsa_item_fixed_view_analytic_invariant THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "right_item_invariant" ACCEPT_TAC]);;

let candle_fso_item_square_analytic_invariant = prove
 (`!center_e box_e boxes tag fixed q_result (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_item_analytic_invariant type_witness boxes
       tag fixed q_result center_e box_e
     ==>
     let result =
       candle_fs_result_square
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)))
         (candle_fsa_item_fixed_view tag fixed q_result) in
     candle_fsa_item_analytic_invariant type_witness boxes T result
       (candle_fs_result_to_q result)
       (Candle_analytic_square center_e) (Candle_analytic_square box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "item_invariant") THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF;
              candle_fsa_item_analytic_invariant_def;
              candle_fsa_item_q_view_def] THEN
  MATCH_MP_TAC candle_fs_result_square_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fsa_item_fixed_view_analytic_invariant THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "item_invariant" ACCEPT_TAC]);;

end;;
