(* ========================================================================== *)
(* Exact object-q soundness for compact polynomial postfix blocks.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the ordinary-HOL counterpart of the  *)
(* HOL4 object-q polynomial run: constants and variables seed complete six-  *)
(* field states, and algebraic instructions reuse the exact object           *)
(* constructors proved by the surrounding source-program layer.  Underflow  *)
(* and out-of-range variables have no step and therefore fail closed.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_poly_program_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;

let candle_q_packed_object_poly_step_def = new_definition
 `candle_q_packed_object_poly_step radii center_boxes outer_boxes
      instruction stack next <=>
    (?positive negative denominator_predecessor.
       instruction =
         Candle_q_push positive negative denominator_predecessor /\
       next =
         CONS
           (Candle_q_packed_object_item
             (Candle_q_packed_object_state T
               (candle_q_packed_object_constant_interval
                 positive negative denominator_predecessor)
               candle_q_packed_object_zero_gradient6
               (candle_q_packed_object_constant_interval
                 positive negative denominator_predecessor)
               candle_q_packed_object_zero_gradient6
               candle_q_packed_object_zero_hessian21)
             (Candle_analytic_poly
               (Candle_poly_const
                 positive negative denominator_predecessor))
             (Candle_analytic_poly
               (Candle_poly_const
                 positive negative denominator_predecessor)))
           stack) \/
    (?variable.
       instruction = Candle_q_load variable /\
       variable < 6 /\
       next =
         CONS
           (Candle_q_packed_object_item
             (Candle_q_packed_object_state T
               (candle_q_interval_lookup variable center_boxes)
               (candle_q_packed_object_unit_gradient6 variable)
               (candle_q_interval_lookup variable outer_boxes)
               (candle_q_packed_object_unit_gradient6 variable)
               candle_q_packed_object_zero_hessian21)
             (Candle_analytic_poly (Candle_poly_var variable))
             (Candle_analytic_poly (Candle_poly_var variable)))
           stack) \/
    (?item rest.
       instruction = Candle_q_neg /\
       stack = CONS item rest /\
       next =
         CONS (candle_q_packed_object_source_item_neg radii item) rest) \/
    (?right left rest.
       instruction = Candle_q_add /\
       stack = CONS right (CONS left rest) /\
       next =
         CONS
           (candle_q_packed_object_source_item_add radii left right) rest) \/
    (?right left rest.
       instruction = Candle_q_mul /\
       stack = CONS right (CONS left rest) /\
       next =
         CONS
           (candle_q_packed_object_source_item_mul radii left right) rest) \/
    (?item rest.
       instruction = Candle_q_square /\
       stack = CONS item rest /\
       next =
         CONS
           (candle_q_packed_object_source_item_mul radii item item) rest)`;;

let candle_q_packed_object_poly_step_analytic_invariant = prove
 (`!center_boxes outer_boxes radii instruction stack next.
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_poly_step
       radii center_boxes outer_boxes instruction stack next
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
  REWRITE_TAC[candle_q_packed_object_poly_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_ACCEPT_TAC
        candle_q_packed_object_source_item_constant_analytic_invariant;
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC
        candle_q_packed_object_source_item_variable_analytic_invariant THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC
        candle_q_packed_object_source_item_neg_analytic_invariant_generic THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC
        candle_q_packed_object_source_item_add_analytic_invariant_generic THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC
        candle_q_packed_object_source_item_mul_analytic_invariant_generic THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC
        candle_q_packed_object_source_item_square_analytic_invariant THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

let candle_q_packed_object_poly_run_def = define
 `(candle_q_packed_object_poly_run radii center_boxes outer_boxes []
      stack result <=> result = stack) /\
  (candle_q_packed_object_poly_run radii center_boxes outer_boxes
      (CONS instruction instructions) stack result <=>
     ?next.
       candle_q_packed_object_poly_step radii center_boxes outer_boxes
         instruction stack next /\
       candle_q_packed_object_poly_run radii center_boxes outer_boxes
         instructions next result)`;;

let candle_q_packed_object_poly_run_analytic_invariant = prove
 (`!instructions center_boxes outer_boxes radii stack result.
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_poly_run
       radii center_boxes outer_boxes instructions stack result
     ==>
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes result`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_object_poly_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_object_poly_run_def] THEN
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
     [MATCH_MP_TAC candle_q_packed_object_poly_step_analytic_invariant THEN
      EXISTS_TAC `radii:((num#num)#num)list` THEN
      EXISTS_TAC `h:candle_q_instruction` THEN
      EXISTS_TAC `stack:candle_q_packed_object_item list` THEN
      ASM_REWRITE_TAC[];
      USE_THEN "induction_hypothesis" MATCH_MP_TAC THEN
      EXISTS_TAC `radii:((num#num)#num)list` THEN
      EXISTS_TAC `next:candle_q_packed_object_item list` THEN
      ASM_REWRITE_TAC[]]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_object_poly_step_analytic_invariant;
     candle_q_packed_object_poly_run_analytic_invariant]
then
  failwith "packed object polynomial program sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_POLY_PROGRAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
