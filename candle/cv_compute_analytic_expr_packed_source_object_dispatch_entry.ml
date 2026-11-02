(* ========================================================================== *)
(* Fail-closed entry for the exact packed object-q source dispatcher.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The entry accepts only a successful replay   *)
(* with exactly one object state and no remaining certificate.  It then      *)
(* applies the existing exact packed Taylor acceptor to that state.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_dispatch_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_complete_entry_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_dispatch_entry = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_compute;;
open Candle_cv_analytic_expr_packed_source_object_complete_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_complete_entry_sound;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_compute;;

let candle_cv_q_packed_object_dispatch_entry_def = new_definition
 `candle_cv_q_packed_object_dispatch_entry
      center_boxes outer_boxes radii codes sources certificates =
    let execution =
      candle_cv_q_packed_object_dispatch_program
        center_boxes outer_boxes radii codes sources certificates
        (Cexp_num 0) in
    let stack = Cexp_fst (Cexp_snd execution) in
    let certificate_rest = Cexp_snd (Cexp_snd execution) in
    Cexp_if (Cexp_eq (Cexp_fst execution) (Cexp_num 1))
      (Cexp_if (Cexp_ispair stack)
        (Cexp_if (Cexp_eq (Cexp_snd stack) (Cexp_num 0))
          (Cexp_if (Cexp_eq certificate_rest (Cexp_num 0))
            (candle_cv_q_packed_object_state_accept6 radii
              (Cexp_fst stack))
            (Cexp_num 0))
          (Cexp_num 0))
        (Cexp_num 0))
      (Cexp_num 0)`;;

let candle_cv_q_packed_object_dispatch_entry_planned_correct = prove
 (`!center_boxes outer_boxes radii codes sources certificates
       domain center_value center_gradient value_bound gradient_bounds
       packed_hessian center_e box_e.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_planned_program_run
       center_boxes outer_boxes radii codes sources certificates []
       [Candle_q_packed_object_item
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian) center_e box_e]
       []
     ==>
     candle_cv_q_packed_object_dispatch_entry
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_packed_object_plan_code_list codes)
       (candle_cv_analytic_instruction_list sources)
       (candle_cv_q_interval_list certificates) =
     candle_cv_q_packed_object_accept6
       (candle_cv_bool domain)
       (candle_cv_q_list radii)
       (candle_cv_q_interval center_value)
       (candle_cv_q_interval_list center_gradient)
       (candle_cv_q_interval_list packed_hessian)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_dispatch_program
      (candle_cv_q_interval_list center_boxes)
      (candle_cv_q_interval_list outer_boxes)
      (candle_cv_q_list radii)
      (candle_cv_q_packed_object_plan_code_list codes)
      (candle_cv_analytic_instruction_list sources)
      (candle_cv_q_interval_list certificates)
      (candle_cv_q_packed_object_stack_encode []) =
    candle_cv_q_packed_object_certificate_state T
      (candle_cv_q_packed_object_stack_encode
        [Candle_q_packed_object_item
          (Candle_q_packed_object_state domain center_value center_gradient
            value_bound gradient_bounds packed_hessian) center_e box_e])
      (candle_cv_q_interval_list [])`
  (LABEL_TAC "execution") THENL
   [MATCH_MP_TAC candle_cv_q_packed_object_dispatch_program_forward THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL];
    ALL_TAC] THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_dispatch_entry_def; LET_DEF; LET_END_DEF;
     candle_cv_q_packed_object_stack_encode_def] THEN
  USE_THEN "execution"
    (fun theorem ->
      REWRITE_TAC
        [REWRITE_RULE
          [candle_cv_q_packed_object_stack_encode_def;
           candle_cv_q_interval_list_def]
          theorem]) THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_certificate_state_def;
     candle_cv_q_packed_object_stack_encode_def;
     candle_cv_q_interval_list_def;
     candle_cv_bool_def; candle_cv_cval_one_suc;
     cexp_fst_def; cexp_snd_def; cexp_eq_def; cexp_ispair_def;
     cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_item_state_encode_def;
     candle_cv_q_packed_object_state_accept6_correct;
     candle_cv_bool_def; candle_cv_cval_one_suc]);;

let _ = print_endline "CANDLE_OBJECT_DISPATCH_ENTRY_STAGE planned_correct";;

let candle_cv_q_packed_object_dispatch_entry_accept_cell_pass = prove
 (`!source_boxes center_boxes outer_boxes radii codes sources certificates
       domain center_value center_gradient value_bound gradient_bounds
       packed_hessian center_e box_e.
     LENGTH source_boxes = 6 /\
     LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_planned_program_run
       center_boxes outer_boxes radii codes sources certificates []
       [Candle_q_packed_object_item
         (Candle_q_packed_object_state domain center_value center_gradient
           value_bound gradient_bounds packed_hessian) center_e box_e]
       [] /\
     candle_cv_q_packed_object_dispatch_entry
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_packed_object_plan_code_list codes)
       (candle_cv_analytic_instruction_list sources)
       (candle_cv_q_interval_list certificates) = Cexp_num 1
     ==>
     m_cell_pass (candle_analytic_denote_dim box_e)
       ((candle_q_box_lower_vector source_boxes:real^6),
        (candle_q_box_upper_vector source_boxes:real^6))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_accept6
      (candle_cv_bool domain)
      (candle_cv_q_list radii)
      (candle_cv_q_interval center_value)
      (candle_cv_q_interval_list center_gradient)
      (candle_cv_q_interval_list packed_hessian) = Cexp_num 1`
  (LABEL_TAC "accepted") THENL
   [MP_TAC
      (SPECL
        [`center_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`; `codes:num list`;
         `sources:candle_analytic_instruction list`;
         `certificates:
           (((num#num)#num)#((num#num)#num))list`;
         `domain:bool`;
         `center_value:(((num#num)#num)#((num#num)#num))`;
         `center_gradient:
           ((((num#num)#num)#((num#num)#num))list)`;
         `value_bound:(((num#num)#num)#((num#num)#num))`;
         `gradient_bounds:
           ((((num#num)#num)#((num#num)#num))list)`;
         `packed_hessian:
           ((((num#num)#num)#((num#num)#num))list)`;
         `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`]
        candle_cv_q_packed_object_dispatch_entry_planned_correct) THEN
    ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  let cell_pass =
    MATCH_MP
      (ISPECL
        [`source_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `center_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`; `codes:num list`;
         `sources:candle_analytic_instruction list`;
         `certificates:
           (((num#num)#num)#((num#num)#num))list`;
         `[]:((((num#num)#num)#((num#num)#num))list)`;
         `domain:bool`;
         `center_value:(((num#num)#num)#((num#num)#num))`;
         `center_gradient:
           ((((num#num)#num)#((num#num)#num))list)`;
         `value_bound:(((num#num)#num)#((num#num)#num))`;
         `gradient_bounds:
           ((((num#num)#num)#((num#num)#num))list)`;
         `packed_hessian:
           ((((num#num)#num)#((num#num)#num))list)`;
         `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`]
        candle_q_packed_object_source_planned_program_accept_cell_pass)
      (end_itlist CONJ
        [ASSUME
           `LENGTH
             (source_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
           `LENGTH
             (center_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
           `LENGTH
             (outer_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
           `candle_q_packed_source_correspondence
             source_boxes center_boxes outer_boxes radii`;
         ASSUME
           `candle_q_packed_source_correspondence
             outer_boxes center_boxes outer_boxes radii`;
         ASSUME
           `candle_q_packed_object_source_planned_program_run
             center_boxes outer_boxes radii codes sources certificates []
             [Candle_q_packed_object_item
               (Candle_q_packed_object_state domain center_value
                 center_gradient value_bound gradient_bounds packed_hessian)
               center_e box_e]
             []`;
         ASSUME
           `candle_cv_q_packed_object_accept6
             (candle_cv_bool domain)
             (candle_cv_q_list radii)
             (candle_cv_q_interval center_value)
             (candle_cv_q_interval_list center_gradient)
             (candle_cv_q_interval_list packed_hessian) = Cexp_num 1`]) in
  MATCH_ACCEPT_TAC cell_pass);;

let _ = print_endline "CANDLE_OBJECT_DISPATCH_ENTRY_STAGE cell_pass";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_dispatch_entry_planned_correct;
     candle_cv_q_packed_object_dispatch_entry_accept_cell_pass] then
  failwith "packed object dispatch entry: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_DISPATCH_ENTRY_OK DEVELOPMENT_NON_RELEASE";;

end;;
