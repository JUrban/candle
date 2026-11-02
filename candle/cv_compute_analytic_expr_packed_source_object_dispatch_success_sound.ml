(* ========================================================================== *)
(* Success reflection for the exact packed object-q source dispatcher.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This first packet covers the six specialized *)
(* delta instructions.  Their authenticated plan identity fixes the logical  *)
(* successor exactly and they consume no certificate data.                   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_dispatch_compute.ml";;

module Candle_cv_analytic_expr_packed_source_object_dispatch_success_sound = struct

open Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound;;
open Candle_cv_analytic_expr_packed_source_object_complete_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_compute;;

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

if hyp candle_q_packed_object_specialized_plan_step_exists <> [] then
  failwith "packed object specialized success sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_DISPATCH_SPECIALIZED_SUCCESS_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
