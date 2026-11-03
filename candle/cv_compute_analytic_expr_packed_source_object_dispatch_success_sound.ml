(* ========================================================================== *)
(* Success reflection for the exact packed object-q source dispatcher.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Executable success for every authenticated   *)
(* ordinary or specialized instruction recovers its logical successor and   *)
(* the exact encoded successor state.                                        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_dispatch_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_ordinary_certificate_success_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_dispatch_success_sound = struct

open Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound;;
open Candle_cv_analytic_expr_packed_source_object_complete_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_compute;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_success_sound;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_certificate_success_sound;;

let candle_q_packed_object_specialized_plan_step_exists = prove
 (`!center_boxes outer_boxes radii code source certificates stack.
     LENGTH radii = 6 /\
     candle_q_packed_source_plan_instruction code source /\
     ~(code = 0)
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_planned_step
         center_boxes outer_boxes radii code source certificates stack next
         certificate_rest /\
       candle_cv_q_packed_object_specialized_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii) (Cexp_num code)
         (candle_cv_analytic_instruction source)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack) =
       candle_cv_q_packed_object_certificate_state T
         (candle_cv_q_packed_object_stack_encode next)
         (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "radii_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "plan")
        (LABEL_TAC "nonzero"))) THEN
  USE_THEN "plan" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_plan_instruction_def] THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
      (CONJUNCTS_THEN2
        (LABEL_TAC "ordinary_code") (LABEL_TAC "ordinary_source"))
      (DISJ_CASES_THEN2
        (X_CHOOSE_THEN `coordinate:num`
          (CONJUNCTS_THEN2 (LABEL_TAC "product_code")
            (CONJUNCTS_THEN2 (LABEL_TAC "product_bound")
              (LABEL_TAC "product_source"))))
        (X_CHOOSE_THEN `coordinate:num`
          (CONJUNCTS_THEN2 (LABEL_TAC "negative_code")
            (CONJUNCTS_THEN2 (LABEL_TAC "negative_coordinate")
              (LABEL_TAC "negative_source")))))) THENL
   [ASM_MESON_TAC[];
    EXISTS_TAC
      `CONS
        (candle_q_packed_object_delta_product_source_item
          radii center_boxes outer_boxes coordinate)
        stack` THEN
    EXISTS_TAC
      `certificates:(((num#num)#num)#((num#num)#num))list` THEN
    SUBGOAL_THEN
     `candle_q_packed_object_source_planned_step
        center_boxes outer_boxes radii code source certificates stack
        (CONS
          (candle_q_packed_object_delta_product_source_item
            radii center_boxes outer_boxes coordinate)
          stack)
        certificates`
    (LABEL_TAC "planned") THENL
     [REWRITE_TAC[candle_q_packed_object_source_planned_step_def] THEN
      DISJ2_TAC THEN DISJ1_TAC THEN
      EXISTS_TAC `coordinate:num` THEN
      ASM_REWRITE_TAC[];
      CONJ_TAC THENL
       [USE_THEN "planned" ACCEPT_TAC;
        MATCH_MP_TAC candle_cv_q_packed_object_specialized_planned_correct THEN
        ASM_REWRITE_TAC[]]];
    EXISTS_TAC
      `CONS
        (candle_q_packed_object_delta_neg_derivative_item
          radii center_boxes coordinate)
        stack` THEN
    EXISTS_TAC
      `certificates:(((num#num)#num)#((num#num)#num))list` THEN
    SUBGOAL_THEN
     `candle_q_packed_object_source_planned_step
        center_boxes outer_boxes radii code source certificates stack
        (CONS
          (candle_q_packed_object_delta_neg_derivative_item
            radii center_boxes coordinate)
          stack)
        certificates`
    (LABEL_TAC "planned") THENL
     [REWRITE_TAC[candle_q_packed_object_source_planned_step_def] THEN
      DISJ2_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `coordinate:num` THEN
      ASM_REWRITE_TAC[];
      CONJ_TAC THENL
       [USE_THEN "planned" ACCEPT_TAC;
        MATCH_MP_TAC candle_cv_q_packed_object_specialized_planned_correct THEN
        ASM_REWRITE_TAC[]]]]);;

let candle_cv_q_packed_object_ordinary_instruction_sound = prove
 (`!center_boxes outer_boxes radii source certificates stack.
     candle_q_packed_source_ordinary_instruction source /\
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_ordinary_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_analytic_instruction source)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_ordinary_step
         center_boxes outer_boxes radii source certificates stack next
         certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_ordinary_instruction_def] THEN
  MESON_TAC
    [candle_q_packed_object_ordinary_poly_exists;
     candle_cv_q_packed_object_ordinary_neg_sound;
     candle_cv_q_packed_object_ordinary_add_sound;
     candle_cv_q_packed_object_ordinary_mul_sound;
     candle_cv_q_packed_object_ordinary_square_sound;
     candle_cv_q_packed_object_ordinary_inv_sound;
     candle_cv_q_packed_object_ordinary_sqrt_sound;
     candle_cv_q_packed_object_ordinary_atn_sound;
     candle_q_packed_object_ordinary_pi_half_exists]);;

let candle_cv_q_packed_object_dispatch_zero_sound = prove
 (`!center_boxes outer_boxes radii source certificates stack.
     candle_q_packed_source_plan_instruction 0 source /\
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_dispatch_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii) (Cexp_num 0)
         (candle_cv_analytic_instruction source)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_planned_step
         center_boxes outer_boxes radii 0 source certificates stack next
         certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_packed_source_plan_instruction_def;
     candle_cv_q_packed_object_dispatch_step_def;
     candle_q_packed_object_source_planned_step_def;
     cexp_eq_def; cexp_if_def; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MESON_TAC[candle_cv_q_packed_object_ordinary_instruction_sound]);;

let candle_cv_q_packed_object_dispatch_success_planned = prove
 (`!center_boxes outer_boxes radii code source certificates stack.
     LENGTH radii = 6 /\
     candle_q_packed_source_plan_instruction code source /\
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_dispatch_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii) (Cexp_num code)
         (candle_cv_analytic_instruction source)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_planned_step
         center_boxes outer_boxes radii code source certificates stack next
         certificate_rest`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `code = 0` THENL
   [UNDISCH_TAC `code = 0` THEN DISCH_THEN SUBST_ALL_TAC THEN
    MATCH_MP_TAC candle_cv_q_packed_object_dispatch_zero_sound THEN
    ASM_REWRITE_TAC[];
    MP_TAC
      (SPECL
        [`center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`; `code:num`;
         `source:candle_analytic_instruction`;
         `certificates:(((num#num)#num)#((num#num)#num))list`;
         `stack:(candle_q_packed_object_item)list`]
        candle_q_packed_object_specialized_plan_step_exists) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let candle_cv_q_packed_object_dispatch_success_exact = prove
 (`!center_boxes outer_boxes radii code source certificates stack.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_source_plan_instruction code source /\
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_dispatch_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii) (Cexp_num code)
         (candle_cv_analytic_instruction source)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?next certificate_rest.
       candle_q_packed_object_source_planned_step
         center_boxes outer_boxes radii code source certificates stack next
         certificate_rest /\
       candle_cv_q_packed_object_dispatch_step
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii) (Cexp_num code)
         (candle_cv_analytic_instruction source)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack) =
       candle_cv_q_packed_object_certificate_state T
         (candle_cv_q_packed_object_stack_encode next)
         (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "input") THEN
  MATCH_MP_TAC candle_exists_pair_strengthen THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_cv_q_packed_object_dispatch_success_planned THEN
    USE_THEN "input" MP_TAC THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC candle_cv_q_packed_object_dispatch_planned_correct THEN
    USE_THEN "input" MP_TAC THEN ASM_MESON_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_specialized_plan_step_exists;
     candle_cv_q_packed_object_ordinary_instruction_sound;
     candle_cv_q_packed_object_dispatch_zero_sound;
     candle_cv_q_packed_object_dispatch_success_planned;
     candle_cv_q_packed_object_dispatch_success_exact] then
  failwith "packed object dispatch success sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_DISPATCH_SUCCESS_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
