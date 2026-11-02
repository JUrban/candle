(* ========================================================================== *)
(* Complete authenticated exact object-q source-program soundness.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Plan code zero uses the ordinary exact object *)
(* evaluator.  Codes one through six are admitted only with the established  *)
(* source-specialization identities and push the corresponding proved exact  *)
(* delta object.  The run consumes code and source lists in lockstep.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_ordinary_program_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_delta_neg_derivative_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_delta_product_source_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certificate_dispatch_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_complete_program_sound = struct

open Candle_cv_analytic_expr_packed_source_delta_specialization_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_delta_neg_derivative_sound;;
open Candle_cv_analytic_expr_packed_source_object_delta_product_source_sound;;

let candle_q_packed_object_source_planned_step_def = new_definition
 `candle_q_packed_object_source_planned_step
      center_boxes outer_boxes radii code source certificates stack next
      certificate_rest <=>
    (code = 0 /\
     candle_q_packed_source_ordinary_instruction source /\
     candle_q_packed_object_source_ordinary_step
       center_boxes outer_boxes radii source certificates stack next
       certificate_rest) \/
    (?coordinate.
       code = SUC coordinate /\
       coordinate < 3 /\
       candle_packed_delta_product_source_instruction coordinate source /\
       next =
         CONS
           (candle_q_packed_object_delta_product_source_item
             radii center_boxes outer_boxes coordinate) stack /\
       certificate_rest = certificates) \/
    (?coordinate.
       code = SUC coordinate /\
       (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5) /\
       candle_packed_delta_neg_derivative_source_instruction
         coordinate source /\
       next =
         CONS
           (candle_q_packed_object_delta_neg_derivative_item
             radii center_boxes coordinate) stack /\
       certificate_rest = certificates)`;;

let candle_q_packed_object_source_planned_step_analytic_invariant = prove
 (`!center_boxes outer_boxes radii code source certificates stack next
       certificate_rest.
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_planned_step
       center_boxes outer_boxes radii code source certificates stack next
       certificate_rest
     ==>
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes next`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 (LABEL_TAC "stack_invariant")
            (LABEL_TAC "step"))))) THEN
  USE_THEN "step" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_planned_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THENL
   [(fun goal ->
      (MATCH_MP_TAC
         candle_q_packed_object_source_ordinary_step_analytic_invariant THEN
       EXISTS_TAC `radii:((num#num)#num)list` THEN
       EXISTS_TAC `source:candle_analytic_instruction` THEN
       EXISTS_TAC
         `certificates:(((num#num)#num)#((num#num)#num))list` THEN
       EXISTS_TAC `stack:candle_q_packed_object_item list` THEN
       EXISTS_TAC
         `certificate_rest:(((num#num)#num)#((num#num)#num))list` THEN
       ASM_REWRITE_TAC[]) goal);
    (fun goal ->
      (REMOVE_THEN "stack_invariant" MP_TAC THEN
       ASM_REWRITE_TAC
         [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
       STRIP_TAC THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC
           candle_q_packed_object_delta_product_source_item_invariant THEN
         ASM_REWRITE_TAC[];
         ASM_REWRITE_TAC[]]) goal);
    (fun goal ->
      (REMOVE_THEN "stack_invariant" MP_TAC THEN
       ASM_REWRITE_TAC
         [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
       STRIP_TAC THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC
           candle_q_packed_object_delta_neg_derivative_item_invariant THEN
         ASM_REWRITE_TAC[];
         ASM_REWRITE_TAC[]]) goal);
    (fun goal ->
      (REMOVE_THEN "stack_invariant" MP_TAC THEN
       ASM_REWRITE_TAC
         [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
       STRIP_TAC THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC
           candle_q_packed_object_delta_neg_derivative_item_invariant THEN
         ASM_REWRITE_TAC[];
         ASM_REWRITE_TAC[]]) goal);
    (fun goal ->
      (REMOVE_THEN "stack_invariant" MP_TAC THEN
       ASM_REWRITE_TAC
         [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
       STRIP_TAC THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC
           candle_q_packed_object_delta_neg_derivative_item_invariant THEN
         ASM_REWRITE_TAC[];
         ASM_REWRITE_TAC[]]) goal)]);;

let candle_q_packed_object_source_planned_program_run_def = define
 `(candle_q_packed_object_source_planned_program_run
      center_boxes outer_boxes radii [] [] certificates stack result
      certificate_rest <=>
      result = stack /\ certificate_rest = certificates) /\
  (candle_q_packed_object_source_planned_program_run
      center_boxes outer_boxes radii [] (CONS source sources)
      certificates stack result certificate_rest <=> F) /\
  (candle_q_packed_object_source_planned_program_run
      center_boxes outer_boxes radii (CONS code codes) []
      certificates stack result certificate_rest <=> F) /\
  (candle_q_packed_object_source_planned_program_run
      center_boxes outer_boxes radii (CONS code codes)
      (CONS source sources) certificates stack result certificate_rest <=>
     ?next next_certificates.
       candle_q_packed_object_source_planned_step
         center_boxes outer_boxes radii code source certificates stack next
         next_certificates /\
       candle_q_packed_object_source_planned_program_run
         center_boxes outer_boxes radii codes sources next_certificates next
         result certificate_rest)`;;

let candle_q_packed_object_source_planned_program_run_analytic_invariant =
  prove
 (`!codes sources center_boxes outer_boxes radii certificates stack result
       certificate_rest.
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_planned_program_run
       center_boxes outer_boxes radii codes sources certificates stack result
       certificate_rest
     ==>
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes result`,
  LIST_INDUCT_TAC THENL
   [X_GEN_TAC `sources:candle_analytic_instruction list` THEN
    MP_TAC
      (ISPEC `sources:candle_analytic_instruction list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `source_head:candle_analytic_instruction`
          (X_CHOOSE_THEN
            `source_tail:candle_analytic_instruction list`
            SUBST_ALL_TAC))) THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_packed_object_source_planned_program_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    X_GEN_TAC `sources:candle_analytic_instruction list` THEN
    MP_TAC
      (ISPEC `sources:candle_analytic_instruction list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `source_head:candle_analytic_instruction`
          (X_CHOOSE_THEN
            `source_tail:candle_analytic_instruction list`
            SUBST_ALL_TAC))) THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_q_packed_object_source_planned_program_run_def];
      REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_q_packed_object_source_planned_program_run_def] THEN
      DISCH_THEN
        (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 ASSUME_TAC
              (CONJUNCTS_THEN2 (LABEL_TAC "stack_invariant")
                (REPEAT_TCL CHOOSE_THEN
                  (CONJUNCTS_THEN2 (LABEL_TAC "step")
                    (LABEL_TAC "tail_run"))))))) THEN
      SUBGOAL_THEN
       `candle_q_packed_object_source_stack_analytic_invariant
          center_boxes outer_boxes next`
      (LABEL_TAC "next_invariant") THENL
       [MATCH_MP_TAC
          candle_q_packed_object_source_planned_step_analytic_invariant THEN
        EXISTS_TAC `radii:((num#num)#num)list` THEN
        EXISTS_TAC `h:num` THEN
        EXISTS_TAC `source_head:candle_analytic_instruction` THEN
        EXISTS_TAC
          `certificates:(((num#num)#num)#((num#num)#num))list` THEN
        EXISTS_TAC `stack:candle_q_packed_object_item list` THEN
        EXISTS_TAC
          `next_certificates:
            (((num#num)#num)#((num#num)#num))list` THEN
        ASM_REWRITE_TAC[];
        USE_THEN "induction_hypothesis" MATCH_MP_TAC THEN
        EXISTS_TAC `source_tail:candle_analytic_instruction list` THEN
        EXISTS_TAC `radii:((num#num)#num)list` THEN
        EXISTS_TAC
          `next_certificates:
            (((num#num)#num)#((num#num)#num))list` THEN
        EXISTS_TAC `next:candle_q_packed_object_item list` THEN
        EXISTS_TAC
          `certificate_rest:
            (((num#num)#num)#((num#num)#num))list` THEN
        ASM_REWRITE_TAC[]]]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_source_planned_step_analytic_invariant;
     candle_q_packed_object_source_planned_program_run_analytic_invariant]
then
  failwith "packed object complete program sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_COMPLETE_PROGRAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
