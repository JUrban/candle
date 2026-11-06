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
open Candle_cv_analytic_expr_packed_source_certified_sqrt_sound;;
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

let candle_analytic_push_poly_injective = prove
 (`!left right.
     Candle_analytic_push_poly left = Candle_analytic_push_poly right
     ==> left = right`,
  REWRITE_TAC[injectivity "candle_analytic_instruction"]);;

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

let candle_q_packed_object_item_inverse_erasure = prove
 (`!radii center_reciprocal box_reciprocal item.
     candle_analytic_erase_sqrt_certificates
       (candle_q_packed_object_item_box_expr
         (candle_q_packed_object_source_item_inverse radii
           center_reciprocal box_reciprocal item)) =
     Candle_analytic_inv
       (candle_analytic_erase_sqrt_certificates
         (candle_q_packed_object_item_box_expr item))`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `item:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_inverse_def;
     candle_q_packed_object_item_box_expr_def;
     candle_analytic_erase_sqrt_certificates_def]);;

let candle_q_packed_object_item_sqrt_erasure = prove
 (`!radii center_root center_derivative box_root box_derivative
      box_second_reciprocal item.
     candle_analytic_erase_sqrt_certificates
       (candle_q_packed_object_item_box_expr
         (candle_q_packed_object_source_item_sqrt radii center_root
           center_derivative box_root box_derivative box_second_reciprocal
           item)) =
     Candle_analytic_sqrt 0 0 0 0 0 0
       (candle_analytic_erase_sqrt_certificates
         (candle_q_packed_object_item_box_expr item))`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `item:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_sqrt_def;
     candle_q_packed_object_item_box_expr_def;
     candle_packed_analytic_sqrt_with_interval_def;
     candle_analytic_erase_sqrt_certificates_def]);;

let candle_q_packed_object_item_atn_erasure = prove
 (`!radii center_input center_result center_square center_derivative
      box_input box_square box_derivative box_derivative_square item.
     candle_analytic_erase_sqrt_certificates
       (candle_q_packed_object_item_box_expr
         (candle_q_packed_object_source_item_atn radii center_input
           center_result center_square center_derivative box_input box_square
           box_derivative box_derivative_square item)) =
     Candle_analytic_atn
       (candle_analytic_erase_sqrt_certificates
         (candle_q_packed_object_item_box_expr item))`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPEC `item:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC
    [candle_q_packed_object_source_item_atn_def;
     candle_q_packed_object_item_box_expr_def;
     candle_analytic_erase_sqrt_certificates_def]);;

let candle_q_packed_object_item_pi_half_erasure = prove
 (`candle_analytic_erase_sqrt_certificates
      (candle_q_packed_object_item_box_expr
        candle_q_packed_object_source_item_pi_half) =
    Candle_analytic_pi_half`,
  REWRITE_TAC
    [candle_q_packed_object_source_item_pi_half_def;
     candle_q_packed_object_item_box_expr_def;
     candle_analytic_erase_sqrt_certificates_def]);;

let _ = print_endline "CANDLE_OBJECT_IDENTITY_PHASE nonpoly-step begin";;
let candle_q_packed_object_nonpoly_step_erased_equal = prove
 (`!left_radii right_radii source left_certificates right_certificates
      left_stack right_stack left_next right_next left_certificate_rest
      right_certificate_rest.
     candle_q_packed_object_source_nonpoly_step left_radii source
       left_certificates left_stack left_next left_certificate_rest /\
     candle_q_packed_object_source_nonpoly_step right_radii source
       right_certificates right_stack right_next right_certificate_rest /\
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
  REWRITE_TAC[candle_q_packed_object_source_nonpoly_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  REMOVE_THEN "right_step" MP_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_object_source_nonpoly_step_def;
     distinctness "candle_analytic_instruction";
     injectivity "candle_analytic_instruction"] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  REMOVE_THEN "input_identity" MP_TAC THEN
  ASM_REWRITE_TAC
    [candle_q_packed_object_erased_stack_def;
     candle_q_packed_object_item_neg_erasure;
     candle_q_packed_object_item_add_erasure;
     candle_q_packed_object_item_mul_erasure;
     candle_q_packed_object_item_inverse_erasure;
     candle_q_packed_object_item_sqrt_erasure;
     candle_q_packed_object_item_atn_erasure;
     candle_q_packed_object_item_pi_half_erasure;
     MAP; CONS_11; FST; SND] THEN
  ASM_MESON_TAC[]);;
let _ = print_endline "CANDLE_OBJECT_IDENTITY_PHASE nonpoly-step end";;

let candle_q_packed_object_nonpoly_step_not_push_poly = prove
 (`!radii source certificates stack next certificate_rest program.
     candle_q_packed_object_source_nonpoly_step radii source certificates
       stack next certificate_rest
     ==>
     ~(source = Candle_analytic_push_poly program)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_nonpoly_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC[distinctness "candle_analytic_instruction"]);;

let _ = print_endline "CANDLE_OBJECT_IDENTITY_PHASE ordinary-step begin";;
let candle_q_packed_object_ordinary_step_erased_equal = prove
 (`!left_center_boxes right_center_boxes left_outer_boxes right_outer_boxes
      left_radii right_radii source left_certificates right_certificates
      left_stack right_stack left_next right_next left_certificate_rest
      right_certificate_rest.
     candle_q_packed_object_source_ordinary_step left_center_boxes
       left_outer_boxes left_radii source left_certificates left_stack
       left_next left_certificate_rest /\
     candle_q_packed_object_source_ordinary_step right_center_boxes
       right_outer_boxes right_radii source right_certificates right_stack
       right_next right_certificate_rest /\
     candle_q_packed_object_erased_stack left_stack =
       candle_q_packed_object_erased_stack right_stack
     ==>
     candle_q_packed_object_erased_stack left_next =
       candle_q_packed_object_erased_stack right_next`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_ordinary_step_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "left_step")
      (CONJUNCTS_THEN2 (LABEL_TAC "right_step")
        (LABEL_TAC "input_identity"))) THEN
  REMOVE_THEN "left_step"
    (DISJ_CASES_THEN2 (LABEL_TAC "left_poly")
      (LABEL_TAC "left_nonpoly")) THENL
   [REMOVE_THEN "right_step"
      (DISJ_CASES_THEN2 (LABEL_TAC "right_poly")
      (LABEL_TAC "right_nonpoly")) THENL
     [REMOVE_THEN "left_poly" STRIP_ASSUME_TAC THEN
      REMOVE_THEN "right_poly" STRIP_ASSUME_TAC THEN
      SUBGOAL_THEN
       `(program:candle_q_instruction list) = program'`
      (LABEL_TAC "program_identity") THENL
       [MATCH_MP_TAC
          (SPECL
            [`program:candle_q_instruction list`;
             `program':candle_q_instruction list`]
            candle_analytic_push_poly_injective) THEN
        ACCEPT_TAC
          (TRANS
            (SYM
              (ASSUME
                `source = Candle_analytic_push_poly program`))
            (ASSUME
              `source = Candle_analytic_push_poly program'`));
        SUBGOAL_THEN
         `candle_q_packed_object_poly_run right_radii right_center_boxes
            right_outer_boxes program [] [result']`
        ASSUME_TAC THENL
         [ONCE_REWRITE_TAC
            [ASSUME `(program:candle_q_instruction list) = program'`] THEN
          ASM_REWRITE_TAC[];
          SUBGOAL_THEN
          `candle_q_packed_object_erased_stack [result] =
            candle_q_packed_object_erased_stack [result']`
          ASSUME_TAC THENL
           [MATCH_MP_TAC candle_q_packed_object_poly_run_erased_equal THEN
            MAP_EVERY EXISTS_TAC
              [`program:candle_q_instruction list`;
               `left_radii:((num#num)#num)list`;
               `right_radii:((num#num)#num)list`;
               `left_center_boxes:
                 ((((num#num)#num)#((num#num)#num))list)`;
               `right_center_boxes:
                 ((((num#num)#num)#((num#num)#num))list)`;
               `left_outer_boxes:
                 ((((num#num)#num)#((num#num)#num))list)`;
               `right_outer_boxes:
                 ((((num#num)#num)#((num#num)#num))list)`;
               `[]:candle_q_packed_object_item list`;
               `[]:candle_q_packed_object_item list`] THEN
            ASM_REWRITE_TAC[candle_q_packed_object_erased_stack_def];
            SUBGOAL_THEN
             `candle_analytic_erase_sqrt_certificates
                (candle_q_packed_object_item_box_expr result) =
              candle_analytic_erase_sqrt_certificates
                (candle_q_packed_object_item_box_expr result')`
            ASSUME_TAC THENL
             [MP_TAC
                (ASSUME
                  `candle_q_packed_object_erased_stack [result] =
                   candle_q_packed_object_erased_stack [result']`) THEN
              REWRITE_TAC
                [candle_q_packed_object_erased_stack_def; MAP; CONS_11];
              ASM_REWRITE_TAC
                [candle_q_packed_object_erased_stack_def; MAP; CONS_11] THEN
              USE_THEN "input_identity" MP_TAC THEN
              REWRITE_TAC[candle_q_packed_object_erased_stack_def]]]]];
      REMOVE_THEN "left_poly" STRIP_ASSUME_TAC THEN
      MP_TAC
        (MATCH_MP
          (SPECL
            [`right_radii:((num#num)#num)list`;
             `source:candle_analytic_instruction`;
             `right_certificates:(((num#num)#num)#((num#num)#num))list`;
             `right_stack:candle_q_packed_object_item list`;
             `right_next:candle_q_packed_object_item list`;
             `right_certificate_rest:
               (((num#num)#num)#((num#num)#num))list`;
             `program:candle_q_instruction list`]
            candle_q_packed_object_nonpoly_step_not_push_poly)
          (ASSUME
            `candle_q_packed_object_source_nonpoly_step right_radii source
              right_certificates right_stack right_next
              right_certificate_rest`)) THEN
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "right_step"
      (DISJ_CASES_THEN2 (LABEL_TAC "right_poly")
        (LABEL_TAC "right_nonpoly")) THENL
     [REMOVE_THEN "right_poly" STRIP_ASSUME_TAC THEN
      MP_TAC
        (MATCH_MP
          (SPECL
            [`left_radii:((num#num)#num)list`;
             `source:candle_analytic_instruction`;
             `left_certificates:(((num#num)#num)#((num#num)#num))list`;
             `left_stack:candle_q_packed_object_item list`;
             `left_next:candle_q_packed_object_item list`;
             `left_certificate_rest:
               (((num#num)#num)#((num#num)#num))list`;
             `program:candle_q_instruction list`]
            candle_q_packed_object_nonpoly_step_not_push_poly)
          (ASSUME
            `candle_q_packed_object_source_nonpoly_step left_radii source
              left_certificates left_stack left_next
              left_certificate_rest`)) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_packed_object_nonpoly_step_erased_equal THEN
      MAP_EVERY EXISTS_TAC
        [`left_radii:((num#num)#num)list`;
         `right_radii:((num#num)#num)list`;
         `source:candle_analytic_instruction`;
         `left_certificates:(((num#num)#num)#((num#num)#num))list`;
         `right_certificates:(((num#num)#num)#((num#num)#num))list`;
         `left_stack:candle_q_packed_object_item list`;
         `right_stack:candle_q_packed_object_item list`;
         `left_certificate_rest:(((num#num)#num)#((num#num)#num))list`;
         `right_certificate_rest:(((num#num)#num)#((num#num)#num))list`] THEN
      ASM_REWRITE_TAC[]]]);;
let _ = print_endline "CANDLE_OBJECT_IDENTITY_PHASE ordinary-step end";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_analytic_push_poly_injective;
     candle_q_packed_object_item_inverse_erasure;
     candle_q_packed_object_item_sqrt_erasure;
     candle_q_packed_object_item_atn_erasure;
     candle_q_packed_object_item_pi_half_erasure;
     candle_q_packed_object_nonpoly_step_erased_equal;
     candle_q_packed_object_nonpoly_step_not_push_poly;
     candle_q_packed_object_ordinary_step_erased_equal] then
  failwith "packed object identity: ordinary assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_IDENTITY_ORDINARY_OK DEVELOPMENT_NON_RELEASE";;

end;;
