(* ========================================================================== *)
(* Certificate-independent expression identity for packed object replay.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Numerical states, radii, boxes, and interval  *)
(* certificates may differ between cells.  A shared authenticated source and *)
(* plan must nevertheless construct the same denoted expression.  Square-root*)
(* payloads are erased because they authenticate numerical evaluation but do *)
(* not change the denoted function.                                           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_complete_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_identity_sound = struct

open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_poly_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_complete_program_sound;;

let candle_q_packed_object_item_box_expr_def = define
 `candle_q_packed_object_item_box_expr
    (Candle_q_packed_object_item state center_e box_e) = box_e`;;

let candle_q_packed_object_erased_stack_def = new_definition
 `candle_q_packed_object_erased_stack stack =
    MAP
      (\item. candle_analytic_erase_sqrt_certificates
        (candle_q_packed_object_item_box_expr item)) stack`;;

let candle_q_packed_object_item_neg_erasure = prove
 (`!radii item.
     candle_analytic_erase_sqrt_certificates
       (candle_q_packed_object_item_box_expr
         (candle_q_packed_object_source_item_neg radii item)) =
     Candle_analytic_neg
       (candle_analytic_erase_sqrt_certificates
         (candle_q_packed_object_item_box_expr item))`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `item:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_neg_def;
     candle_q_packed_object_item_box_expr_def;
     candle_analytic_erase_sqrt_certificates_def]);;

let candle_q_packed_object_item_add_erasure = prove
 (`!radii left right.
     candle_analytic_erase_sqrt_certificates
       (candle_q_packed_object_item_box_expr
         (candle_q_packed_object_source_item_add radii left right)) =
     Candle_analytic_add
       (candle_analytic_erase_sqrt_certificates
         (candle_q_packed_object_item_box_expr left))
       (candle_analytic_erase_sqrt_certificates
         (candle_q_packed_object_item_box_expr right))`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `left:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
  MP_TAC
    (SPEC `right:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_add_def;
     candle_q_packed_object_item_box_expr_def;
     candle_analytic_erase_sqrt_certificates_def]);;

let candle_q_packed_object_item_mul_erasure = prove
 (`!radii left right.
     candle_analytic_erase_sqrt_certificates
       (candle_q_packed_object_item_box_expr
         (candle_q_packed_object_source_item_mul radii left right)) =
     Candle_analytic_mul
       (candle_analytic_erase_sqrt_certificates
         (candle_q_packed_object_item_box_expr left))
       (candle_analytic_erase_sqrt_certificates
         (candle_q_packed_object_item_box_expr right))`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `left:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
  MP_TAC
    (SPEC `right:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_mul_def;
     candle_q_packed_object_item_box_expr_def;
     candle_analytic_erase_sqrt_certificates_def]);;

let _ = print_endline "CANDLE_OBJECT_IDENTITY_PHASE poly-step begin";;
let candle_q_packed_object_poly_step_erased_equal = prove
 (`!left_radii right_radii left_center_boxes right_center_boxes
      left_outer_boxes right_outer_boxes instruction left_stack right_stack
      left_next right_next.
     candle_q_packed_object_poly_step left_radii left_center_boxes
       left_outer_boxes instruction left_stack left_next /\
     candle_q_packed_object_poly_step right_radii right_center_boxes
       right_outer_boxes instruction right_stack right_next /\
     candle_q_packed_object_erased_stack left_stack =
       candle_q_packed_object_erased_stack right_stack
     ==>
     candle_q_packed_object_erased_stack left_next =
       candle_q_packed_object_erased_stack right_next`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "left_step")
      (CONJUNCTS_THEN2 (LABEL_TAC "right_step")
        (LABEL_TAC "input_identity"))) THEN
  REMOVE_THEN "left_step" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_poly_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  REMOVE_THEN "right_step" MP_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_object_poly_step_def;
     distinctness "candle_q_instruction";
     injectivity "candle_q_instruction"] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  REMOVE_THEN "input_identity" MP_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_object_erased_stack_def;
     candle_q_packed_object_item_box_expr_def;
     candle_q_packed_object_item_neg_erasure;
     candle_q_packed_object_item_add_erasure;
     candle_q_packed_object_item_mul_erasure;
     candle_analytic_erase_sqrt_certificates_def;
     MAP; CONS_11; FST; SND] THEN
  ASM_MESON_TAC[]);;

let _ = print_endline "CANDLE_OBJECT_IDENTITY_PHASE poly-step end";;

let _ = print_endline "CANDLE_OBJECT_IDENTITY_PHASE poly-run begin";;
let candle_q_packed_object_poly_run_erased_equal_goal =
 `!program left_radii right_radii left_center_boxes right_center_boxes
      left_outer_boxes right_outer_boxes left_stack right_stack
      left_result right_result.
     candle_q_packed_object_poly_run left_radii left_center_boxes
       left_outer_boxes program left_stack left_result /\
     candle_q_packed_object_poly_run right_radii right_center_boxes
       right_outer_boxes program right_stack right_result /\
     candle_q_packed_object_erased_stack left_stack =
       candle_q_packed_object_erased_stack right_stack
     ==>
     candle_q_packed_object_erased_stack left_result =
       candle_q_packed_object_erased_stack right_result`;;
let _ = print_endline "CANDLE_OBJECT_IDENTITY_PHASE poly-run parsed";;
let candle_q_packed_object_poly_run_erased_equal = prove
 (candle_q_packed_object_poly_run_erased_equal_goal,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_object_poly_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_object_poly_run_def] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2
        (REPEAT_TCL CHOOSE_THEN
          (CONJUNCTS_THEN2 (LABEL_TAC "left_head")
            (LABEL_TAC "left_tail")))
        (CONJUNCTS_THEN2
          (REPEAT_TCL CHOOSE_THEN
            (CONJUNCTS_THEN2 (LABEL_TAC "right_head")
              (LABEL_TAC "right_tail")))
          (LABEL_TAC "input_identity"))) THEN
    SUBGOAL_THEN
     `candle_q_packed_object_erased_stack next =
      candle_q_packed_object_erased_stack next'`
    (LABEL_TAC "next_identity") THENL
     [MATCH_MP_TAC candle_q_packed_object_poly_step_erased_equal THEN
      MAP_EVERY EXISTS_TAC
        [`left_radii:((num#num)#num)list`;
         `right_radii:((num#num)#num)list`;
         `left_center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `right_center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `left_outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `right_outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `h:candle_q_instruction`;
         `left_stack:candle_q_packed_object_item list`;
         `right_stack:candle_q_packed_object_item list`] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "induction_hypothesis" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC
        [`left_radii:((num#num)#num)list`;
         `right_radii:((num#num)#num)list`;
         `left_center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `right_center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `left_outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `right_outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `next:candle_q_packed_object_item list`;
         `next':candle_q_packed_object_item list`] THEN
      ASM_REWRITE_TAC[]]]);;

let _ = print_endline "CANDLE_OBJECT_IDENTITY_PHASE poly-run end";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_item_neg_erasure;
     candle_q_packed_object_item_add_erasure;
     candle_q_packed_object_item_mul_erasure;
     candle_q_packed_object_poly_step_erased_equal;
     candle_q_packed_object_poly_run_erased_equal] then
  failwith "packed object identity: polynomial assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_IDENTITY_POLY_OK DEVELOPMENT_NON_RELEASE";;

end;;
