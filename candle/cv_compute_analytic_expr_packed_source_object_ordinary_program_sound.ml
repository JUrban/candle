(* ========================================================================== *)
(* Complete exact object-q soundness for ordinary source instructions.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Polynomial blocks execute from a fresh local *)
(* stack and must return exactly one item.  Every other supported ordinary   *)
(* instruction uses the certificate-aware non-polynomial relation.  Delta   *)
(* specialization is intentionally not included in this ordinary boundary.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_poly_program_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_nonpoly_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_ordinary_program_sound = struct

open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_poly_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_program_sound;;

let candle_q_packed_object_source_ordinary_step_def = new_definition
 `candle_q_packed_object_source_ordinary_step center_boxes outer_boxes radii
      source certificates stack next certificate_rest <=>
    (?program result.
       source = Candle_analytic_push_poly program /\
       candle_q_packed_object_poly_run radii center_boxes outer_boxes
         program [] [result] /\
       next = CONS result stack /\
       certificate_rest = certificates) \/
    candle_q_packed_object_source_nonpoly_step
      radii source certificates stack next certificate_rest`;;

let candle_q_packed_object_source_ordinary_step_analytic_invariant = prove
 (`!center_boxes outer_boxes radii source certificates stack next
       certificate_rest.
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
       radii source certificates stack next certificate_rest
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
  REWRITE_TAC[candle_q_packed_object_source_ordinary_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `candle_q_packed_object_source_item_analytic_invariant
        center_boxes outer_boxes result`
    (LABEL_TAC "result_invariant") THENL
     [MP_TAC
        (SPECL
          [`program:candle_q_instruction list`;
           `center_boxes:
              (((num#num)#num)#((num#num)#num))list`;
           `outer_boxes:
              (((num#num)#num)#((num#num)#num))list`;
           `radii:((num#num)#num)list`;
           `[]:candle_q_packed_object_item list`;
           `[result]:candle_q_packed_object_item list`]
          candle_q_packed_object_poly_run_analytic_invariant) THEN
      ASM_REWRITE_TAC
        [candle_q_packed_object_source_stack_analytic_invariant_def; ALL];
      USE_THEN "stack_invariant" MP_TAC THEN
      REWRITE_TAC
        [candle_q_packed_object_source_stack_analytic_invariant_def] THEN
      ASM_REWRITE_TAC[ALL]];
    MATCH_MP_TAC
      candle_q_packed_object_source_nonpoly_step_analytic_invariant THEN
    EXISTS_TAC `radii:((num#num)#num)list` THEN
    EXISTS_TAC `source:candle_analytic_instruction` THEN
    EXISTS_TAC
      `certificates:(((num#num)#num)#((num#num)#num))list` THEN
    EXISTS_TAC `stack:candle_q_packed_object_item list` THEN
    EXISTS_TAC
      `certificate_rest:(((num#num)#num)#((num#num)#num))list` THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_packed_object_source_ordinary_program_run_def = define
 `(candle_q_packed_object_source_ordinary_program_run center_boxes outer_boxes
      radii [] certificates stack result certificate_rest <=>
      result = stack /\ certificate_rest = certificates) /\
  (candle_q_packed_object_source_ordinary_program_run center_boxes outer_boxes
      radii (CONS source sources) certificates stack result
      certificate_rest <=>
     ?next next_certificates.
       candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
         radii source certificates stack next next_certificates /\
       candle_q_packed_object_source_ordinary_program_run
         center_boxes outer_boxes radii sources next_certificates next
         result certificate_rest)`;;

let candle_q_packed_object_source_ordinary_program_run_analytic_invariant =
  prove
 (`!sources center_boxes outer_boxes radii certificates stack result
       certificate_rest.
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_ordinary_program_run
       center_boxes outer_boxes radii sources certificates stack result
       certificate_rest
     ==>
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes result`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_packed_object_source_ordinary_program_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_packed_object_source_ordinary_program_run_def] THEN
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
        candle_q_packed_object_source_ordinary_step_analytic_invariant THEN
      EXISTS_TAC `radii:((num#num)#num)list` THEN
      EXISTS_TAC `h:candle_analytic_instruction` THEN
      EXISTS_TAC
        `certificates:(((num#num)#num)#((num#num)#num))list` THEN
      EXISTS_TAC `stack:candle_q_packed_object_item list` THEN
      EXISTS_TAC
        `next_certificates:(((num#num)#num)#((num#num)#num))list` THEN
      ASM_REWRITE_TAC[];
      USE_THEN "induction_hypothesis" MATCH_MP_TAC THEN
      EXISTS_TAC `radii:((num#num)#num)list` THEN
      EXISTS_TAC
        `next_certificates:(((num#num)#num)#((num#num)#num))list` THEN
      EXISTS_TAC `next:candle_q_packed_object_item list` THEN
      EXISTS_TAC
        `certificate_rest:(((num#num)#num)#((num#num)#num))list` THEN
      ASM_REWRITE_TAC[]]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_source_ordinary_step_analytic_invariant;
     candle_q_packed_object_source_ordinary_program_run_analytic_invariant]
then
  failwith "packed object ordinary program sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_ORDINARY_PROGRAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
