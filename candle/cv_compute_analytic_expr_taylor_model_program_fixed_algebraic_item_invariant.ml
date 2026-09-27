(* ========================================================================== *)
(* Universal analytic invariant for tagged fixed/rational Taylor items.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_item_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_invariant.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_invariant = struct

open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_nonlinear_sound;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_item_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_invariant;;

let candle_fsa_item_analytic_invariant_def = new_definition
 `candle_fsa_item_analytic_invariant
      (type_witness:real^N) boxes tag fixed q_result center_e box_e <=>
    candle_q_dim_taylor_model_result_analytic_invariant
      type_witness boxes
      (candle_fsa_item_q_view tag fixed q_result) center_e box_e`;;

let candle_fsa_item_fixed_view_analytic_invariant = prove
 (`!center_e box_e boxes tag fixed q_result (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_item_analytic_invariant
       type_witness boxes tag fixed q_result center_e box_e
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_fs_result_to_q
         (candle_fsa_item_fixed_view tag fixed q_result))
       center_e box_e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  BOOL_CASES_TAC `tag:bool` THEN
  REWRITE_TAC[candle_fsa_item_analytic_invariant_def;
              candle_fsa_item_q_view_def;
              candle_fsa_item_fixed_view_def] THEN
  DISCH_TAC THEN
  TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC candle_fsa_result_of_q_analytic_invariant THEN
  ASM_REWRITE_TAC[]);;

let candle_fsa_item_neg_analytic_invariant = prove
 (`!center_e box_e boxes use_fixed tag fixed q_result
      (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_item_analytic_invariant
       type_witness boxes tag fixed q_result center_e box_e
     ==>
     candle_fsa_item_analytic_invariant type_witness boxes use_fixed
       (candle_fs_result_neg
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes)))
         (candle_fsa_item_fixed_view tag fixed q_result))
       (candle_q_dim_taylor_model_result_neg
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_fsa_item_q_view tag fixed q_result))
       (Candle_analytic_neg center_e) (Candle_analytic_neg box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "item_invariant") THEN
  REWRITE_TAC[candle_fsa_item_analytic_invariant_def] THEN
  BOOL_CASES_TAC `use_fixed:bool` THEN
  REWRITE_TAC[candle_fsa_item_q_view_def] THENL
   [MATCH_MP_TAC candle_fs_result_neg_analytic_invariant THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_fsa_item_fixed_view_analytic_invariant THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "item_invariant" ACCEPT_TAC];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_neg_analytic_invariant THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "item_invariant" MP_TAC THEN
    REWRITE_TAC[candle_fsa_item_analytic_invariant_def;
                candle_fsa_item_q_view_def]]);;

let candle_fsa_item_add_analytic_invariant = prove
 (`!center_a center_b box_a box_b boxes use_fixed
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
     candle_fsa_item_analytic_invariant type_witness boxes use_fixed
       (candle_fs_result_add
         (candle_fs_list_of_q
           (candle_q_fixed_list_round_upper
             (candle_q_radius_list boxes)))
         (candle_fsa_item_fixed_view left_tag left_fixed left_q)
         (candle_fsa_item_fixed_view right_tag right_fixed right_q))
       (candle_q_dim_taylor_model_result_add
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_fsa_item_q_view left_tag left_fixed left_q)
         (candle_fsa_item_q_view right_tag right_fixed right_q))
       (Candle_analytic_add center_a center_b)
       (Candle_analytic_add box_a box_b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM
   (fun right_th ->
      POP_ASSUM
       (fun left_th ->
          LABEL_TAC "left_item_invariant" left_th THEN
          LABEL_TAC "right_item_invariant" right_th)) THEN
  REWRITE_TAC[candle_fsa_item_analytic_invariant_def] THEN
  BOOL_CASES_TAC `use_fixed:bool` THEN
  REWRITE_TAC[candle_fsa_item_q_view_def] THENL
   [MATCH_MP_TAC candle_fs_result_add_analytic_invariant THEN
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
      USE_THEN "right_item_invariant" ACCEPT_TAC];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_add_analytic_invariant THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      USE_THEN "left_item_invariant" MP_TAC THEN
      REWRITE_TAC[candle_fsa_item_analytic_invariant_def;
                  candle_fsa_item_q_view_def];
      USE_THEN "right_item_invariant" MP_TAC THEN
      REWRITE_TAC[candle_fsa_item_analytic_invariant_def;
                  candle_fsa_item_q_view_def]]]);;

let candle_fsa_item_mul_analytic_invariant = prove
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
       candle_q_dim_taylor_model_result_mul
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_fsa_item_q_view left_tag left_fixed left_q)
         (candle_fsa_item_q_view right_tag right_fixed right_q) in
     candle_fsa_item_analytic_invariant type_witness boxes F
       (candle_fsa_result_of_q result) result
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
  MATCH_MP_TAC candle_q_dim_taylor_model_result_mul_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "left_item_invariant" MP_TAC THEN
    REWRITE_TAC[candle_fsa_item_analytic_invariant_def;
                candle_fsa_item_q_view_def];
    USE_THEN "right_item_invariant" MP_TAC THEN
    REWRITE_TAC[candle_fsa_item_analytic_invariant_def;
                candle_fsa_item_q_view_def]]);;

let candle_fsa_item_square_analytic_invariant = prove
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
       candle_q_dim_taylor_model_result_square
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_fsa_item_q_view tag fixed q_result) in
     candle_fsa_item_analytic_invariant type_witness boxes F
       (candle_fsa_result_of_q result) result
       (Candle_analytic_square center_e) (Candle_analytic_square box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "item_invariant") THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF;
              candle_fsa_item_analytic_invariant_def;
              candle_fsa_item_q_view_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_result_square_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "item_invariant" MP_TAC THEN
    REWRITE_TAC[candle_fsa_item_analytic_invariant_def;
                candle_fsa_item_q_view_def]]);;

let candle_fsa_item_inv_analytic_invariant = prove
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
       candle_q_dim_taylor_model_result_inv
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_fsa_item_q_view tag fixed q_result) in
     candle_fsa_item_analytic_invariant type_witness boxes F
       (candle_fsa_result_of_q result) result
       (Candle_analytic_inv center_e) (Candle_analytic_inv box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "item_invariant") THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF;
              candle_fsa_item_analytic_invariant_def;
              candle_fsa_item_q_view_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_result_inv_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "item_invariant" MP_TAC THEN
    REWRITE_TAC[candle_fsa_item_analytic_invariant_def;
                candle_fsa_item_q_view_def]]);;

let candle_fsa_item_sqrt_analytic_invariant = prove
 (`!clp cln cld cup cun cud blp bln bld bup bun bud
      center_e box_e boxes tag fixed q_result (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_fsa_item_analytic_invariant type_witness boxes
       tag fixed q_result center_e box_e
     ==>
     let result =
       candle_q_dim_taylor_model_result_sqrt
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_analytic_sqrt_interval clp cln cld cup cun cud)
         (candle_analytic_sqrt_interval blp bln bld bup bun bud)
         (candle_fsa_item_q_view tag fixed q_result) in
     candle_fsa_item_analytic_invariant type_witness boxes F
       (candle_fsa_result_of_q result) result
       (Candle_analytic_sqrt clp cln cld cup cun cud center_e)
       (Candle_analytic_sqrt blp bln bld bup bun bud box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "item_invariant") THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF;
              candle_fsa_item_analytic_invariant_def;
              candle_fsa_item_q_view_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_result_sqrt_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "item_invariant" MP_TAC THEN
    REWRITE_TAC[candle_fsa_item_analytic_invariant_def;
                candle_fsa_item_q_view_def]]);;

let candle_fsa_item_atn_analytic_invariant = prove
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
       candle_q_dim_taylor_model_result_atn
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_fsa_item_q_view tag fixed q_result) in
     candle_fsa_item_analytic_invariant type_witness boxes F
       (candle_fsa_result_of_q result) result
       (Candle_analytic_atn center_e) (Candle_analytic_atn box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "item_invariant") THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF;
              candle_fsa_item_analytic_invariant_def;
              candle_fsa_item_q_view_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_result_atn_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "item_invariant" MP_TAC THEN
    REWRITE_TAC[candle_fsa_item_analytic_invariant_def;
                candle_fsa_item_q_view_def]]);;

let candle_fsa_item_pi_half_analytic_invariant = prove
 (`!boxes (type_witness:real^N).
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     let result =
       candle_q_dim_taylor_model_result_pi_half
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_q_center_environment_list boxes) boxes in
     candle_fsa_item_analytic_invariant type_witness boxes F
       (candle_fsa_result_of_q result) result
       Candle_analytic_pi_half Candle_analytic_pi_half`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF;
              candle_fsa_item_analytic_invariant_def;
              candle_fsa_item_q_view_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_result_pi_half_analytic_invariant THEN
  ASM_REWRITE_TAC[]);;

let candle_fsa_poly_item_analytic_invariant = prove
 (`!e boxes (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_fsa_item_analytic_invariant type_witness boxes T
       (candle_fs_poly_program
         (candle_q_center_environment_list boxes)
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_poly_compile e))
       (candle_fs_poly_program_to_q
         (candle_q_center_environment_list boxes)
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_poly_compile e))
       (Candle_analytic_poly e) (Candle_analytic_poly e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsa_item_analytic_invariant_def;
              candle_fsa_item_q_view_def;
              GSYM candle_fs_poly_program_to_q_def] THEN
  MATCH_MP_TAC candle_fs_poly_program_to_q_analytic_invariant THEN
  ASM_REWRITE_TAC[]);;

end;;
