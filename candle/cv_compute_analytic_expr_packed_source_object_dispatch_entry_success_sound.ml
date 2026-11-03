(* ========================================================================== *)
(* Success reflection for the exact-object dispatcher entry.                 *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  An accepted entry must contain one logical   *)
(* object result and no unused certificate.  Complete-program reflection then*)
(* recovers the authenticated source run, and the existing analytic entry    *)
(* theorem turns its accepted object into a genuine cell theorem.             *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_dispatch_entry.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_dispatch_program_success_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certificate_dispatch_entry_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_dispatch_entry_success_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_cval_list;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_program_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_entry_sound;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_compute;;
open Candle_cv_analytic_expr_packed_source_object_complete_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_compute;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_entry;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_program_success_sound;;

let candle_cv_q_packed_object_dispatch_entry_complete = prove
 (`!center_boxes outer_boxes radii codes sources certificates.
     candle_cv_q_packed_object_dispatch_entry
       center_boxes outer_boxes radii codes sources certificates =
       Cexp_num 1
     ==>
     candle_q_packed_source_certificate_dispatch_state_complete
       (candle_cv_q_packed_object_dispatch_program
         center_boxes outer_boxes radii codes sources certificates
         (Cexp_num 0))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_dispatch_entry_def;
     LET_DEF; LET_END_DEF;
     candle_q_packed_source_certificate_dispatch_state_complete_def;
     candle_cv_equal_correct; candle_cv_ispair_correct;
     candle_cv_guarded_accept_one] THEN
  MESON_TAC[candle_cval_pair_zero_tail]);;

let candle_cv_q_packed_object_stack_encode_length = prove
 (`!items.
     candle_cv_list_length
       (candle_cv_q_packed_object_stack_encode items) =
     Cexp_num (LENGTH items)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC
      [candle_cv_q_packed_object_stack_encode_def;
       candle_cv_list_length_def; LENGTH];
    ASM_REWRITE_TAC
      [candle_cv_q_packed_object_stack_encode_def;
       candle_cv_list_length_def; LENGTH; cexp_add_def;
       ARITH_RULE `1 + n = SUC n`]]);;

let candle_q_packed_object_stack_singleton = prove
 (`!items encoded_result.
     candle_cv_q_packed_object_stack_encode items =
       Cexp_pair encoded_result (Cexp_num 0)
     ==>
     ?item. items = CONS item []`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MP_TAC o AP_TERM `candle_cv_list_length`) THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_stack_encode_length;
     candle_cv_list_length_def; cexp_add_def; injectivity "cval"] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MESON_TAC[candle_list_length_one]);;

let candle_q_packed_object_dispatch_state_complete_shape = prove
 (`!items certificates.
     candle_q_packed_source_certificate_dispatch_state_complete
       (candle_cv_q_packed_object_certificate_state T
         (candle_cv_q_packed_object_stack_encode items)
         (candle_cv_q_interval_list certificates))
     ==>
     ?item. items = CONS item [] /\ certificates = []`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_q_packed_source_certificate_dispatch_state_complete_def;
     candle_cv_q_packed_object_certificate_state_def;
     candle_cv_bool_def; cexp_fst_def; cexp_snd_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MESON_TAC
    [candle_q_packed_object_stack_singleton;
     candle_cv_q_interval_list_empty]);;

let candle_cv_q_packed_object_dispatch_program_complete_exact = prove
 (`!center_boxes outer_boxes radii codes sources certificates.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_source_planned_program_instructions codes sources /\
     candle_q_packed_source_certificate_dispatch_state_complete
       (candle_cv_q_packed_object_dispatch_program
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_q_packed_object_plan_code_list codes)
         (candle_cv_analytic_instruction_list sources)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode []))
     ==>
     ?item.
       candle_q_packed_object_source_planned_program_run
         center_boxes outer_boxes radii codes sources certificates []
         (CONS item []) [] /\
       candle_cv_q_packed_object_dispatch_program
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_q_packed_object_plan_code_list codes)
         (candle_cv_analytic_instruction_list sources)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode []) =
       candle_cv_q_packed_object_certificate_state T
         (candle_cv_q_packed_object_stack_encode [item])
         (candle_cv_q_interval_list [])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "outer_length")
        (CONJUNCTS_THEN2 (LABEL_TAC "radii_length")
          (CONJUNCTS_THEN2 (LABEL_TAC "correspondence")
            (CONJUNCTS_THEN2 (LABEL_TAC "planned_program")
              (LABEL_TAC "complete_dispatch")))))) THEN
  SUBGOAL_THEN
   `?result certificate_rest.
      candle_q_packed_object_source_planned_program_run
        center_boxes outer_boxes radii codes sources certificates [] result
        certificate_rest /\
      candle_cv_q_packed_object_dispatch_program
        (candle_cv_q_interval_list center_boxes)
        (candle_cv_q_interval_list outer_boxes)
        (candle_cv_q_list radii)
        (candle_cv_q_packed_object_plan_code_list codes)
        (candle_cv_analytic_instruction_list sources)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_packed_object_stack_encode []) =
      candle_cv_q_packed_object_certificate_state T
        (candle_cv_q_packed_object_stack_encode result)
        (candle_cv_q_interval_list certificate_rest)`
  MP_TAC THENL
   [MATCH_MP_TAC
      candle_cv_q_packed_object_dispatch_program_success_exact THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL;
       candle_cv_q_packed_source_certificate_success_def] THEN
    ASM_MESON_TAC
      [candle_q_packed_source_certificate_dispatch_state_complete_def];
    ALL_TAC] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `result:(candle_q_packed_object_item)list`
      (X_CHOOSE_THEN
        `certificate_rest:(((num#num)#num)#((num#num)#num))list`
        (CONJUNCTS_THEN2 (LABEL_TAC "logical_run")
          (LABEL_TAC "execution")))) THEN
  MP_TAC
    (SPECL
      [`result:(candle_q_packed_object_item)list`;
       `certificate_rest:(((num#num)#num)#((num#num)#num))list`]
      candle_q_packed_object_dispatch_state_complete_shape) THEN
  ANTS_TAC THENL
   [USE_THEN "execution" (fun theorem -> REWRITE_TAC[GSYM theorem]) THEN
    USE_THEN "complete_dispatch" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `item:candle_q_packed_object_item`
      (CONJUNCTS_THEN2 (LABEL_TAC "result_shape")
        (LABEL_TAC "certificate_shape"))) THEN
  EXISTS_TAC `item:candle_q_packed_object_item` THEN
  CONJ_TAC THENL
   [USE_THEN "logical_run" MP_TAC THEN
    USE_THEN "result_shape" (fun theorem -> REWRITE_TAC[theorem]) THEN
    USE_THEN "certificate_shape" (fun theorem -> REWRITE_TAC[theorem]);
    USE_THEN "execution" MP_TAC THEN
    USE_THEN "result_shape" (fun theorem -> REWRITE_TAC[theorem]) THEN
    USE_THEN "certificate_shape" (fun theorem -> REWRITE_TAC[theorem])]);;

let candle_cv_q_packed_object_dispatch_entry_accept_cell_pass = prove
 (`!source_boxes center_boxes outer_boxes radii codes sources certificates.
     LENGTH source_boxes = 6 /\
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_source_planned_program_instructions codes sources /\
     candle_cv_q_packed_object_dispatch_entry
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_packed_object_plan_code_list codes)
       (candle_cv_analytic_instruction_list sources)
       (candle_cv_q_interval_list certificates) = Cexp_num 1
     ==>
     ?domain center_value center_gradient value_bound gradient_bounds
        packed_hessian center_e box_e.
       candle_q_packed_object_source_planned_program_run
         center_boxes outer_boxes radii codes sources certificates []
         [Candle_q_packed_object_item
           (Candle_q_packed_object_state domain center_value center_gradient
             value_bound gradient_bounds packed_hessian) center_e box_e]
         [] /\
       m_cell_pass (candle_analytic_denote_dim box_e)
         ((candle_q_box_lower_vector source_boxes:real^6),
          (candle_q_box_upper_vector source_boxes:real^6))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "source_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "center_length")
        (CONJUNCTS_THEN2 (LABEL_TAC "outer_length")
          (CONJUNCTS_THEN2 (LABEL_TAC "radii_length")
            (CONJUNCTS_THEN2 (LABEL_TAC "source_correspondence")
              (CONJUNCTS_THEN2 (LABEL_TAC "outer_correspondence")
                (CONJUNCTS_THEN2 (LABEL_TAC "planned_program")
                  (LABEL_TAC "entry_accept")))))))) THEN
  SUBGOAL_THEN
   `candle_q_packed_source_certificate_dispatch_state_complete
      (candle_cv_q_packed_object_dispatch_program
        (candle_cv_q_interval_list center_boxes)
        (candle_cv_q_interval_list outer_boxes)
        (candle_cv_q_list radii)
        (candle_cv_q_packed_object_plan_code_list codes)
        (candle_cv_analytic_instruction_list sources)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_packed_object_stack_encode []))`
  (LABEL_TAC "complete_dispatch") THENL
   [REWRITE_TAC[candle_cv_q_packed_object_stack_encode_def] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_dispatch_entry_complete THEN
    USE_THEN "entry_accept" ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC
    (SPECL
      [`center_boxes:((((num#num)#num)#((num#num)#num))list)`;
       `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
       `radii:((num#num)#num)list`; `codes:num list`;
       `sources:candle_analytic_instruction list`;
       `certificates:(((num#num)#num)#((num#num)#num))list`]
      candle_cv_q_packed_object_dispatch_program_complete_exact) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN
      (X_CHOOSE_THEN `item:candle_q_packed_object_item`
        (CONJUNCTS_THEN2 (LABEL_TAC "logical_run")
          (LABEL_TAC "execution")))] THEN
  MP_TAC
    (SPEC `item:candle_q_packed_object_item`
      candle_q_packed_object_item_full_cases) THEN
  DISCH_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  MAP_EVERY EXISTS_TAC
    [`domain:bool`;
     `center_value:(((num#num)#num)#((num#num)#num))`;
     `center_gradient:((((num#num)#num)#((num#num)#num))list)`;
     `value_bound:(((num#num)#num)#((num#num)#num))`;
     `gradient_bounds:((((num#num)#num)#((num#num)#num))list)`;
     `packed_hessian:((((num#num)#num)#((num#num)#num))list)`;
     `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`] THEN
  CONJ_TAC THENL
   [USE_THEN "logical_run" ACCEPT_TAC;
    MATCH_MP_TAC
      (SPECL
        [`source_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`; `codes:num list`;
         `sources:candle_analytic_instruction list`;
         `certificates:(((num#num)#num)#((num#num)#num))list`;
         `domain:bool`;
         `center_value:(((num#num)#num)#((num#num)#num))`;
         `center_gradient:((((num#num)#num)#((num#num)#num))list)`;
         `value_bound:(((num#num)#num)#((num#num)#num))`;
         `gradient_bounds:((((num#num)#num)#((num#num)#num))list)`;
         `packed_hessian:((((num#num)#num)#((num#num)#num))list)`;
         `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`]
        Candle_cv_analytic_expr_packed_source_object_dispatch_entry.candle_cv_q_packed_object_dispatch_entry_accept_cell_pass) THEN
    ASM_REWRITE_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_dispatch_entry_complete;
     candle_cv_q_packed_object_stack_encode_length;
     candle_q_packed_object_stack_singleton;
     candle_q_packed_object_dispatch_state_complete_shape;
     candle_cv_q_packed_object_dispatch_program_complete_exact;
     candle_cv_q_packed_object_dispatch_entry_accept_cell_pass] then
  failwith "packed object dispatch entry success sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_DISPATCH_ENTRY_SUCCESS_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
