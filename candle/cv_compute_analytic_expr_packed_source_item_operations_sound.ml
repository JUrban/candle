(* ========================================================================== *)
(* Ordinary analytic operations preserve packed-source semantic items.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  These are the local cases used by the source *)
(* replay induction.  Each output keeps the exact rational Taylor result and *)
(* records the center/box expression constructed by that postfix operation.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_item_invariant.ml";;

module Candle_cv_analytic_expr_packed_source_item_operations_sound = struct

open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_nonlinear_sound;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_analytic_expr_packed_source_item_invariant;;

let candle_q_packed_source_poly_item_def = new_definition
 `candle_q_packed_source_poly_item boxes polynomial =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_poly_program
        (candle_q_center_environment_list boxes) boxes
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        (candle_poly_compile polynomial))
      (Candle_analytic_poly polynomial)
      (Candle_analytic_poly polynomial)`;;

let candle_q_packed_source_item_neg_def = new_definition
 `candle_q_packed_source_item_neg boxes item =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_result_neg
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        (candle_q_packed_source_item_result item))
      (Candle_analytic_neg
        (candle_q_packed_source_item_center_expr item))
      (Candle_analytic_neg
        (candle_q_packed_source_item_box_expr item))`;;

let candle_q_packed_source_item_add_def = new_definition
 `candle_q_packed_source_item_add boxes left right =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_result_add
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        (candle_q_packed_source_item_result left)
        (candle_q_packed_source_item_result right))
      (Candle_analytic_add
        (candle_q_packed_source_item_center_expr left)
        (candle_q_packed_source_item_center_expr right))
      (Candle_analytic_add
        (candle_q_packed_source_item_box_expr left)
        (candle_q_packed_source_item_box_expr right))`;;

let candle_q_packed_source_item_mul_def = new_definition
 `candle_q_packed_source_item_mul boxes left right =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_result_mul
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        (candle_q_packed_source_item_result left)
        (candle_q_packed_source_item_result right))
      (Candle_analytic_mul
        (candle_q_packed_source_item_center_expr left)
        (candle_q_packed_source_item_center_expr right))
      (Candle_analytic_mul
        (candle_q_packed_source_item_box_expr left)
        (candle_q_packed_source_item_box_expr right))`;;

let candle_q_packed_source_item_square_def = new_definition
 `candle_q_packed_source_item_square boxes item =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_result_square
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        (candle_q_packed_source_item_result item))
      (Candle_analytic_square
        (candle_q_packed_source_item_center_expr item))
      (Candle_analytic_square
        (candle_q_packed_source_item_box_expr item))`;;

let candle_q_packed_source_item_inv_def = new_definition
 `candle_q_packed_source_item_inv boxes item =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_result_inv
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        (candle_q_packed_source_item_result item))
      (Candle_analytic_inv
        (candle_q_packed_source_item_center_expr item))
      (Candle_analytic_inv
        (candle_q_packed_source_item_box_expr item))`;;

let candle_q_packed_source_item_sqrt_def = new_definition
 `candle_q_packed_source_item_sqrt boxes
      clp cln cld cup cun cud blp bln bld bup bun bud item =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_result_sqrt
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        (candle_analytic_sqrt_interval clp cln cld cup cun cud)
        (candle_analytic_sqrt_interval blp bln bld bup bun bud)
        (candle_q_packed_source_item_result item))
      (Candle_analytic_sqrt clp cln cld cup cun cud
        (candle_q_packed_source_item_center_expr item))
      (Candle_analytic_sqrt blp bln bld bup bun bud
        (candle_q_packed_source_item_box_expr item))`;;

let candle_q_packed_source_item_atn_def = new_definition
 `candle_q_packed_source_item_atn boxes item =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_result_atn
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        (candle_q_packed_source_item_result item))
      (Candle_analytic_atn
        (candle_q_packed_source_item_center_expr item))
      (Candle_analytic_atn
        (candle_q_packed_source_item_box_expr item))`;;

let candle_q_packed_source_pi_half_item_def = new_definition
 `candle_q_packed_source_pi_half_item boxes =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_result_pi_half
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        (candle_q_center_environment_list boxes) boxes)
      Candle_analytic_pi_half Candle_analytic_pi_half`;;

let candle_q_packed_source_poly_item_analytic_invariant = prove
  (`!boxes polynomial.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_poly_valid_dim 6 polynomial
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_poly_item boxes polynomial)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_poly_item_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND;
              candle_analytic_valid_dim_def;
              candle_analytic_erase_sqrt_certificates_def] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (ISPECL
          [`polynomial:candle_poly_expr`;
           `boxes:(((num#num)#num)#((num#num)#num))list`;
           `ARB:real^6`]
          candle_q_dim_taylor_model_poly_compile_analytic_invariant)) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_source_item_neg_analytic_invariant = prove
 (`!boxes item.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_item_analytic_invariant boxes item
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_item_neg boxes item)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "item_invariant"))) THEN
  USE_THEN "item_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_source_item_result_def;
                  candle_q_packed_source_item_center_expr_def;
                  candle_q_packed_source_item_box_expr_def]) THEN
  REWRITE_TAC[candle_q_packed_source_item_neg_def;
              candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    MATCH_MP_TAC
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (INST_TYPE [`:6`,`:N`]
          candle_q_dim_taylor_model_result_neg_analytic_invariant)) THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_source_item_add_analytic_invariant = prove
 (`!boxes left right.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_item_analytic_invariant boxes left /\
     candle_q_packed_source_item_analytic_invariant boxes right
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_item_add boxes left right)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2
          (LABEL_TAC "left_invariant") (LABEL_TAC "right_invariant")))) THEN
  USE_THEN "left_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  USE_THEN "right_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_source_item_result_def;
                  candle_q_packed_source_item_center_expr_def;
                  candle_q_packed_source_item_box_expr_def]) THEN
  REWRITE_TAC[candle_q_packed_source_item_add_def;
              candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_add_analytic_invariant THEN
    ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex (:6)`]]);;

let candle_q_packed_source_item_mul_analytic_invariant = prove
 (`!boxes left right.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_item_analytic_invariant boxes left /\
     candle_q_packed_source_item_analytic_invariant boxes right
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_item_mul boxes left right)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2
          (LABEL_TAC "left_invariant") (LABEL_TAC "right_invariant")))) THEN
  USE_THEN "left_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  USE_THEN "right_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_source_item_result_def;
                  candle_q_packed_source_item_center_expr_def;
                  candle_q_packed_source_item_box_expr_def]) THEN
  REWRITE_TAC[candle_q_packed_source_item_mul_def;
              candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_mul_analytic_invariant THEN
    ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex (:6)`]]);;

let candle_q_packed_source_item_square_analytic_invariant = prove
 (`!boxes item.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_item_analytic_invariant boxes item
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_item_square boxes item)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "item_invariant"))) THEN
  USE_THEN "item_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_source_item_result_def;
                  candle_q_packed_source_item_center_expr_def;
                  candle_q_packed_source_item_box_expr_def]) THEN
  REWRITE_TAC[candle_q_packed_source_item_square_def;
              candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_square_analytic_invariant THEN
    ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex (:6)`]]);;

let candle_q_packed_source_item_inv_analytic_invariant = prove
 (`!boxes item.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_item_analytic_invariant boxes item
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_item_inv boxes item)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "item_invariant"))) THEN
  USE_THEN "item_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_source_item_result_def;
                  candle_q_packed_source_item_center_expr_def;
                  candle_q_packed_source_item_box_expr_def]) THEN
  REWRITE_TAC[candle_q_packed_source_item_inv_def;
              candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_inv_analytic_invariant THEN
    ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex (:6)`]]);;

let candle_q_packed_source_item_sqrt_analytic_invariant = prove
 (`!boxes clp cln cld cup cun cud blp bln bld bup bun bud item.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_item_analytic_invariant boxes item
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_item_sqrt boxes
         clp cln cld cup cun cud blp bln bld bup bun bud item)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "item_invariant"))) THEN
  USE_THEN "item_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_source_item_result_def;
                  candle_q_packed_source_item_center_expr_def;
                  candle_q_packed_source_item_box_expr_def]) THEN
  REWRITE_TAC[candle_q_packed_source_item_sqrt_def;
              candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_sqrt_analytic_invariant THEN
    ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex (:6)`]]);;

let candle_q_packed_source_item_atn_analytic_invariant = prove
 (`!boxes item.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_item_analytic_invariant boxes item
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_item_atn boxes item)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "item_invariant"))) THEN
  USE_THEN "item_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_source_item_result_def;
                  candle_q_packed_source_item_center_expr_def;
                  candle_q_packed_source_item_box_expr_def]) THEN
  REWRITE_TAC[candle_q_packed_source_item_atn_def;
              candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    MATCH_MP_TAC candle_q_dim_taylor_model_result_atn_analytic_invariant THEN
    ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex (:6)`]]);;

let candle_q_packed_source_pi_half_item_analytic_invariant = prove
 (`!boxes.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_pi_half_item boxes)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
      (ISPECL
        [`boxes:(((num#num)#num)#((num#num)#num))list`;
         `ARB:real^6`]
        candle_q_dim_taylor_model_result_pi_half_analytic_invariant)) THEN
  ASM_REWRITE_TAC[candle_q_packed_source_pi_half_item_def;
                  candle_q_packed_source_item_analytic_invariant_def;
                  candle_q_packed_source_item_make_def;
                  candle_q_packed_source_item_result_def;
                  candle_q_packed_source_item_center_expr_def;
                  candle_q_packed_source_item_box_expr_def; FST; SND;
                  candle_analytic_valid_dim_def;
                  candle_analytic_erase_sqrt_certificates_def]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_source_poly_item_analytic_invariant;
     candle_q_packed_source_item_neg_analytic_invariant;
     candle_q_packed_source_item_add_analytic_invariant;
     candle_q_packed_source_item_mul_analytic_invariant;
     candle_q_packed_source_item_square_analytic_invariant;
     candle_q_packed_source_item_inv_analytic_invariant;
     candle_q_packed_source_item_sqrt_analytic_invariant;
     candle_q_packed_source_item_atn_analytic_invariant;
     candle_q_packed_source_pi_half_item_analytic_invariant] then
  failwith "packed source item operations sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_ITEM_OPERATIONS_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
