(* ========================================================================== *)
(* Exact object-q soundness for ordinary non-polynomial source instructions. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This relation uses the authenticated source   *)
(* instruction constructors and the exact flat certificate stream consumed  *)
(* by the current source entry.  Polynomial blocks and recognized delta      *)
(* instructions remain separate proof obligations; there is no catch-all    *)
(* branch, so every unsupported instruction fails closed.                    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_nonpoly_program_sound = struct

open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;

let candle_q_packed_object_source_nonpoly_step_def = new_definition
 `candle_q_packed_object_source_nonpoly_step radii source certificates
      stack next certificate_rest <=>
    (?item rest.
       source = Candle_analytic_program_neg /\
       stack = CONS item rest /\
       next =
         CONS (candle_q_packed_object_source_item_neg radii item) rest /\
       certificate_rest = certificates) \/
    (?right left rest.
       source = Candle_analytic_program_add /\
       stack = CONS right (CONS left rest) /\
       next =
         CONS
           (candle_q_packed_object_source_item_add radii left right) rest /\
       certificate_rest = certificates) \/
    (?right left rest.
       source = Candle_analytic_program_mul /\
       stack = CONS right (CONS left rest) /\
       next =
         CONS
           (candle_q_packed_object_source_item_mul radii left right) rest /\
       certificate_rest = certificates) \/
    (?item rest.
       source = Candle_analytic_program_square /\
       stack = CONS item rest /\
       next =
         CONS
           (candle_q_packed_object_source_item_mul radii item item) rest /\
       certificate_rest = certificates) \/
    (?item rest center_reciprocal box_reciprocal.
       source = Candle_analytic_program_inv /\
       certificates =
         CONS center_reciprocal (CONS box_reciprocal certificate_rest) /\
       stack = CONS item rest /\
       candle_q_interval_inv_certificate
         (candle_q_packed_object_item_center_value item)
         center_reciprocal /\
       candle_q_interval_inv_certificate
         (candle_q_packed_object_item_value_bound item)
         box_reciprocal /\
       next =
         CONS
           (candle_q_packed_object_source_item_inverse radii
             center_reciprocal box_reciprocal item) rest) \/
    (?source_sqrt item rest center_root box_root center_derivative
        box_derivative box_second_reciprocal.
       source = Candle_analytic_program_sqrt source_sqrt /\
       certificates =
         CONS center_root
           (CONS box_root
             (CONS center_derivative
               (CONS box_derivative
                 (CONS box_second_reciprocal certificate_rest)))) /\
       stack = CONS item rest /\
       candle_q_interval_sqrt_certificate
         (candle_q_packed_object_item_center_value item) center_root /\
       candle_q_interval_inv_certificate
         (candle_q_interval_add center_root center_root)
         center_derivative /\
       candle_q_interval_sqrt_certificate
         (candle_q_packed_object_item_value_bound item) box_root /\
       candle_q_interval_inv_certificate
         (candle_q_interval_add box_root box_root) box_derivative /\
       candle_q_interval_inv_certificate
         (candle_q_interval_mul
           (candle_q_interval_add box_root box_root)
           (candle_q_interval_add
             (candle_q_packed_object_item_value_bound item)
             (candle_q_packed_object_item_value_bound item)))
         box_second_reciprocal /\
       next =
         CONS
           (candle_q_packed_object_source_item_sqrt radii center_root
             center_derivative box_root box_derivative
             box_second_reciprocal item) rest) \/
    (?item rest center_input box_input center_result center_square
        center_derivative box_square box_derivative box_derivative_square.
       source = Candle_analytic_program_atn /\
       certificates =
         CONS center_input
           (CONS box_input
             (CONS center_result
               (CONS center_square
                 (CONS center_derivative
                   (CONS box_square
                     (CONS box_derivative
                       (CONS box_derivative_square certificate_rest))))))) /\
       stack = CONS item rest /\
       candle_q_interval_atn_outer_certificate
         (candle_q_packed_object_item_center_value item)
         center_input center_result /\
       candle_q_interval_square_outer_certificate
         (candle_q_packed_object_item_center_value item)
         center_input center_square /\
       candle_q_interval_inv_certificate
         (candle_q_packed_object_atn_denominator center_square)
         center_derivative /\
       candle_q_interval_square_outer_certificate
         (candle_q_packed_object_item_value_bound item)
         box_input box_square /\
       candle_q_interval_inv_certificate
         (candle_q_packed_object_atn_denominator box_square)
         box_derivative /\
       candle_q_interval_square_outer_certificate
         box_derivative box_derivative box_derivative_square /\
       next =
         CONS
           (candle_q_packed_object_source_item_atn radii center_input
             center_result center_square center_derivative box_input
             box_square box_derivative box_derivative_square item) rest) \/
    (source = Candle_analytic_program_pi_half /\
     next = CONS candle_q_packed_object_source_item_pi_half stack /\
     certificate_rest = certificates)`;;

let candle_q_packed_object_source_nonpoly_step_analytic_invariant = prove
 (`!center_boxes outer_boxes radii source certificates stack next
       certificate_rest.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_nonpoly_step
       radii source certificates stack next certificate_rest
     ==>
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes next`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "stack_invariant")
          (LABEL_TAC "step")))) THEN
  USE_THEN "step" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_nonpoly_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "stack_invariant" MP_TAC THEN
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
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC
        candle_q_packed_object_source_item_inverse_analytic_invariant_generic THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC
        candle_q_packed_object_source_item_sqrt_analytic_invariant_generic THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC
        candle_q_packed_object_source_item_atn_analytic_invariant_generic THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REMOVE_THEN "stack_invariant" MP_TAC THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_ACCEPT_TAC
        candle_q_packed_object_source_item_pi_half_analytic_invariant;
      ASM_REWRITE_TAC[]]]);;

let candle_q_packed_object_source_nonpoly_program_run_def = define
 `(candle_q_packed_object_source_nonpoly_program_run radii []
      certificates stack result certificate_rest <=>
      result = stack /\ certificate_rest = certificates) /\
  (candle_q_packed_object_source_nonpoly_program_run radii
      (CONS source sources) certificates stack result certificate_rest <=>
     ?next next_certificates.
       candle_q_packed_object_source_nonpoly_step
         radii source certificates stack next next_certificates /\
       candle_q_packed_object_source_nonpoly_program_run
         radii sources next_certificates next result certificate_rest)`;;

let candle_q_packed_object_source_nonpoly_program_run_analytic_invariant =
  prove
 (`!sources center_boxes outer_boxes radii certificates stack result
       certificate_rest.
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_nonpoly_program_run
       radii sources certificates stack result certificate_rest
     ==>
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes result`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_object_source_nonpoly_program_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_object_source_nonpoly_program_run_def] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 (LABEL_TAC "stack_invariant")
            (REPEAT_TCL CHOOSE_THEN
              (CONJUNCTS_THEN2 (LABEL_TAC "step")
                (LABEL_TAC "tail_run")))))) THEN
    SUBGOAL_THEN
     `candle_q_packed_object_source_stack_analytic_invariant
        center_boxes outer_boxes next`
    (LABEL_TAC "next_invariant") THENL
     [MATCH_MP_TAC
        candle_q_packed_object_source_nonpoly_step_analytic_invariant THEN
      EXISTS_TAC `radii:((num#num)#num)list` THEN
      EXISTS_TAC `h:candle_analytic_instruction` THEN
      EXISTS_TAC
        `certificates:(((num#num)#num)#((num#num)#num))list` THEN
      EXISTS_TAC
        `stack:candle_q_packed_object_item list` THEN
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
    [candle_q_packed_object_source_nonpoly_step_analytic_invariant;
     candle_q_packed_object_source_nonpoly_program_run_analytic_invariant]
then
  failwith "packed object nonpoly program sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_NONPOLY_PROGRAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
