(* ========================================================================== *)
(* Cell soundness of the complete authenticated exact object-q source run.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A successful planned run supplies the exact   *)
(* analytic invariant for its singleton result.  The existing packed Taylor  *)
(* acceptance theorem then proves negativity throughout the authenticated    *)
(* source cell.                                                               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_complete_program_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_entry_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_complete_entry_sound = struct

open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_complete_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_entry_sound;;

let candle_q_packed_object_source_planned_program_accept_cell_pass = prove
 (`!source_boxes center_boxes outer_boxes radii codes sources certificates
       certificate_rest domain center_value center_gradient value_bound
       gradient_bounds packed_hessian center_e box_e.
     LENGTH source_boxes = 6 /\
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_planned_program_run
       center_boxes outer_boxes radii codes sources certificates []
       [Candle_q_packed_object_item
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian) center_e box_e]
       certificate_rest /\
     candle_cv_q_packed_object_accept6
       (candle_cv_bool domain)
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_value)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval_list packed_hessian) = Cexp_num 1
     ==>
     m_cell_pass (candle_analytic_denote_dim box_e)
       ((candle_q_box_lower_vector source_boxes:real^6),
        (candle_q_box_upper_vector source_boxes:real^6))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (ISPECL
      [`source_boxes:
         ((((num#num)#num)#((num#num)#num))list)`;
       `center_boxes:
         ((((num#num)#num)#((num#num)#num))list)`;
       `outer_boxes:
         ((((num#num)#num)#((num#num)#num))list)`;
       `radii:((num#num)#num)list`; `domain:bool`;
       `center_value:(((num#num)#num)#((num#num)#num))`;
       `center_gradient:
         ((((num#num)#num)#((num#num)#num))list)`;
       `value_bound:(((num#num)#num)#((num#num)#num))`;
       `gradient_bounds:
         ((((num#num)#num)#((num#num)#num))list)`;
       `packed_hessian:
         ((((num#num)#num)#((num#num)#num))list)`;
       `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`]
      candle_q_packed_source_object_accept_contract_cell_pass) THEN
  REWRITE_TAC[candle_q_packed_source_object_accept_contract_def] THEN
  ASM_REWRITE_TAC[] THEN
  let result_invariant =
    MATCH_MP
      (SPECL
        [`codes:num list`; `sources:candle_analytic_instruction list`;
         `center_boxes:
            ((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:
            ((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`;
         `certificates:
            (((num#num)#num)#((num#num)#num))list`;
         `[]:candle_q_packed_object_item list`;
         `[Candle_q_packed_object_item
            (Candle_q_packed_object_state domain center_value center_gradient
              value_bound gradient_bounds packed_hessian) center_e box_e]`;
         `certificate_rest:
            (((num#num)#num)#((num#num)#num))list`]
        candle_q_packed_object_source_planned_program_run_analytic_invariant)
      (end_itlist CONJ
        [ASSUME
           `LENGTH
             (center_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
           `LENGTH
             (outer_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
           `candle_q_packed_source_correspondence
             outer_boxes center_boxes outer_boxes radii`;
         prove
           (`candle_q_packed_object_source_stack_analytic_invariant
               center_boxes outer_boxes []`,
            REWRITE_TAC
              [candle_q_packed_object_source_stack_analytic_invariant_def;
               ALL]);
         ASSUME
           `candle_q_packed_object_source_planned_program_run
             center_boxes outer_boxes radii codes sources certificates []
             [Candle_q_packed_object_item
               (Candle_q_packed_object_state domain center_value
                 center_gradient value_bound gradient_bounds packed_hessian)
               center_e box_e]
             certificate_rest`]) in
  let item_invariant =
    REWRITE_RULE
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL;
       candle_q_packed_object_source_item_analytic_invariant_def]
      result_invariant in
  let object_invariant =
    CONJUNCT2 (CONJUNCT2 (CONJUNCT2 item_invariant)) in
  MATCH_ACCEPT_TAC object_invariant);;

if hyp candle_q_packed_object_source_planned_program_accept_cell_pass <> [] then
  failwith "packed object complete entry sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_COMPLETE_ENTRY_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
