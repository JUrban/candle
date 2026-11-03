(* ========================================================================== *)
(* Success reflection for complete exact-object source dispatch programs.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The proof is generic in the instruction-list *)
(* length.  Each executable head success recovers one authenticated logical  *)
(* step and its exact state; induction then recovers the complete logical run.*)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_dispatch_success_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certificate_dispatch_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_dispatch_program_success_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_complete_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_compute;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_compute;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_success_sound;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_success_sound;;

let candle_cv_q_packed_object_dispatch_program_head_success = prove
 (`!step recursive failure_stack failure_certificates.
     candle_cv_q_packed_source_certificate_success
       (Cexp_if (Cexp_eq (Cexp_fst step) (Cexp_num 1))
         recursive
         (candle_cv_q_packed_object_certificate_failure
           failure_stack failure_certificates))
     ==>
     candle_cv_q_packed_source_certificate_success step`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `candle_cv_q_packed_source_certificate_success step` THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_cv_q_packed_source_certificate_success_def]) THEN
  ASM_REWRITE_TAC
    [cexp_eq_def; cexp_if_def;
     candle_cv_q_packed_object_certificate_success_failure]);;

let candle_cv_q_packed_object_dispatch_program_cons_head = prove
 (`!center_boxes outer_boxes radii code codes source sources certificates
       stack.
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_dispatch_program
         center_boxes outer_boxes radii
         (Cexp_pair code codes) (Cexp_pair source sources)
         certificates stack)
     ==>
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_dispatch_step
         center_boxes outer_boxes radii code source certificates stack)`,
  REPEAT GEN_TAC THEN DISCH_THEN
    (fun theorem ->
      ACCEPT_TAC
        (MATCH_MP
          (SPECL
            [`candle_cv_q_packed_object_dispatch_step
                center_boxes outer_boxes radii code source certificates
                stack`;
             `candle_cv_q_packed_object_dispatch_program
                center_boxes outer_boxes radii codes sources
                (Cexp_snd
                  (Cexp_snd
                    (candle_cv_q_packed_object_dispatch_step
                      center_boxes outer_boxes radii code source certificates
                      stack)))
                (Cexp_fst
                  (Cexp_snd
                    (candle_cv_q_packed_object_dispatch_step
                      center_boxes outer_boxes radii code source certificates
                      stack)))`;
             `stack:cval`; `certificates:cval`]
            candle_cv_q_packed_object_dispatch_program_head_success)
          (REWRITE_RULE
            [candle_cv_q_packed_object_dispatch_program_def;
             LET_DEF; LET_END_DEF]
            theorem))));;

let candle_cv_q_packed_object_dispatch_program_cons_tail = prove
 (`!center_boxes outer_boxes radii code codes source sources certificates
       stack next next_certificates.
     candle_cv_q_packed_object_dispatch_step
       center_boxes outer_boxes radii code source certificates stack =
       candle_cv_q_packed_object_certificate_state T next next_certificates /\
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_dispatch_program
         center_boxes outer_boxes radii
         (Cexp_pair code codes) (Cexp_pair source sources)
         certificates stack)
     ==>
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_dispatch_program
         center_boxes outer_boxes radii codes sources next_certificates next)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "step_exact")
      (LABEL_TAC "whole_success")) THEN
  USE_THEN "whole_success" MP_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_dispatch_program_def;
     LET_DEF; LET_END_DEF] THEN
  USE_THEN "step_exact" (fun theorem -> REWRITE_TAC[theorem]) THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_certificate_state_def;
     candle_cv_bool_def; cexp_fst_def; cexp_snd_def;
     cexp_eq_def; cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[candle_cv_q_packed_object_if_one]);;

let candle_q_packed_object_source_planned_program_run_cons = prove
 (`!center_boxes outer_boxes radii code codes source sources certificates
       stack next next_certificates result certificate_rest.
     candle_q_packed_object_source_planned_step
       center_boxes outer_boxes radii code source certificates stack next
       next_certificates /\
     candle_q_packed_object_source_planned_program_run
       center_boxes outer_boxes radii codes sources next_certificates next
       result certificate_rest
     ==>
     candle_q_packed_object_source_planned_program_run
       center_boxes outer_boxes radii (CONS code codes)
       (CONS source sources) certificates stack result certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_planned_program_run_def] THEN
  MESON_TAC[]);;

let candle_cv_q_packed_object_dispatch_program_success_planned = prove
 (`!codes sources center_boxes outer_boxes radii certificates stack.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_source_planned_program_instructions codes sources /\
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_dispatch_program
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_q_packed_object_plan_code_list codes)
         (candle_cv_analytic_instruction_list sources)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?result certificate_rest.
       candle_q_packed_object_source_planned_program_run
         center_boxes outer_boxes radii codes sources certificates stack
         result certificate_rest`,
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
      [candle_q_packed_source_planned_program_instructions_def;
       candle_cv_q_packed_object_plan_code_list_def;
       candle_cv_analytic_instruction_list_def;
       candle_cv_q_packed_object_dispatch_program_def;
       candle_cv_q_packed_object_certificate_success_state;
       candle_q_packed_object_source_planned_program_run_def] THEN
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
        [candle_q_packed_source_planned_program_instructions_def];
      REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_q_packed_source_planned_program_instructions_def;
         candle_cv_q_packed_object_plan_code_list_def;
         candle_cv_analytic_instruction_list_def] THEN
      DISCH_THEN
        (CONJUNCTS_THEN2 (LABEL_TAC "center_length")
          (CONJUNCTS_THEN2 (LABEL_TAC "outer_length")
            (CONJUNCTS_THEN2 (LABEL_TAC "radii_length")
              (CONJUNCTS_THEN2 (LABEL_TAC "correspondence")
                (CONJUNCTS_THEN2 (LABEL_TAC "stack_invariant")
                  (CONJUNCTS_THEN2
                    (CONJUNCTS_THEN2 (LABEL_TAC "head_plan")
                      (LABEL_TAC "tail_plan"))
                    (LABEL_TAC "whole_success"))))))) THEN
      SUBGOAL_THEN
       `candle_cv_q_packed_source_certificate_success
          (candle_cv_q_packed_object_dispatch_step
            (candle_cv_q_interval_list center_boxes)
            (candle_cv_q_interval_list outer_boxes)
            (candle_cv_q_list radii) (Cexp_num h)
            (candle_cv_analytic_instruction source_head)
            (candle_cv_q_interval_list certificates)
            (candle_cv_q_packed_object_stack_encode stack))`
      (LABEL_TAC "head_success") THENL
       [MATCH_MP_TAC
          (SPECL
            [`candle_cv_q_interval_list center_boxes`;
             `candle_cv_q_interval_list outer_boxes`;
             `candle_cv_q_list radii`; `Cexp_num h`;
             `candle_cv_q_packed_object_plan_code_list t`;
             `candle_cv_analytic_instruction source_head`;
             `candle_cv_analytic_instruction_list source_tail`;
             `candle_cv_q_interval_list certificates`;
             `candle_cv_q_packed_object_stack_encode stack`]
            candle_cv_q_packed_object_dispatch_program_cons_head) THEN
        USE_THEN "whole_success" ACCEPT_TAC;
        ALL_TAC] THEN
      MP_TAC
        (SPECL
          [`center_boxes:((((num#num)#num)#((num#num)#num))list)`;
           `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
           `radii:((num#num)#num)list`; `h:num`;
           `source_head:candle_analytic_instruction`;
           `certificates:(((num#num)#num)#((num#num)#num))list`;
           `stack:(candle_q_packed_object_item)list`]
          candle_cv_q_packed_object_dispatch_success_exact) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN
          (X_CHOOSE_THEN `next:(candle_q_packed_object_item)list`
            (X_CHOOSE_THEN
              `next_certificates:
                (((num#num)#num)#((num#num)#num))list`
              (CONJUNCTS_THEN2 (LABEL_TAC "head_step")
                (LABEL_TAC "head_exact"))))] THEN
      SUBGOAL_THEN
       `candle_q_packed_object_source_stack_analytic_invariant
          center_boxes outer_boxes next`
      (LABEL_TAC "next_invariant") THENL
       [MATCH_MP_TAC
          candle_q_packed_object_source_planned_step_analytic_invariant THEN
        MAP_EVERY EXISTS_TAC
          [`radii:((num#num)#num)list`; `h:num`;
           `source_head:candle_analytic_instruction`;
           `certificates:(((num#num)#num)#((num#num)#num))list`;
           `stack:(candle_q_packed_object_item)list`;
           `next_certificates:
             (((num#num)#num)#((num#num)#num))list`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `candle_cv_q_packed_source_certificate_success
          (candle_cv_q_packed_object_dispatch_program
            (candle_cv_q_interval_list center_boxes)
            (candle_cv_q_interval_list outer_boxes)
            (candle_cv_q_list radii)
            (candle_cv_q_packed_object_plan_code_list t)
            (candle_cv_analytic_instruction_list source_tail)
            (candle_cv_q_interval_list next_certificates)
            (candle_cv_q_packed_object_stack_encode next))`
      (LABEL_TAC "tail_success") THENL
       [MATCH_MP_TAC
          (SPECL
            [`candle_cv_q_interval_list center_boxes`;
             `candle_cv_q_interval_list outer_boxes`;
             `candle_cv_q_list radii`; `Cexp_num h`;
             `candle_cv_q_packed_object_plan_code_list t`;
             `candle_cv_analytic_instruction source_head`;
             `candle_cv_analytic_instruction_list source_tail`;
             `candle_cv_q_interval_list certificates`;
             `candle_cv_q_packed_object_stack_encode stack`;
             `candle_cv_q_packed_object_stack_encode next`;
             `candle_cv_q_interval_list next_certificates`]
            candle_cv_q_packed_object_dispatch_program_cons_tail) THEN
        CONJ_TAC THENL
         [USE_THEN "head_exact" ACCEPT_TAC;
          USE_THEN "whole_success" ACCEPT_TAC];
        ALL_TAC] THEN
      USE_THEN "induction_hypothesis"
        (fun theorem ->
          MP_TAC
            (SPECL
              [`source_tail:candle_analytic_instruction list`;
               `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
               `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
               `radii:((num#num)#num)list`;
               `next_certificates:
                 (((num#num)#num)#((num#num)#num))list`;
               `next:(candle_q_packed_object_item)list`]
              theorem)) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN
          (X_CHOOSE_THEN `result:(candle_q_packed_object_item)list`
            (X_CHOOSE_THEN
              `certificate_rest:
                (((num#num)#num)#((num#num)#num))list`
              (LABEL_TAC "tail_run")))] THEN
      MAP_EVERY EXISTS_TAC
        [`result:(candle_q_packed_object_item)list`;
         `certificate_rest:(((num#num)#num)#((num#num)#num))list`] THEN
      MATCH_MP_TAC candle_q_packed_object_source_planned_program_run_cons THEN
      MAP_EVERY EXISTS_TAC
        [`next:(candle_q_packed_object_item)list`;
         `next_certificates:
           (((num#num)#num)#((num#num)#num))list`] THEN
      ASM_REWRITE_TAC[]]]);;

let candle_cv_q_packed_object_dispatch_program_success_exact = prove
 (`!codes sources center_boxes outer_boxes radii certificates stack.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_source_planned_program_instructions codes sources /\
     candle_cv_q_packed_source_certificate_success
       (candle_cv_q_packed_object_dispatch_program
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_q_packed_object_plan_code_list codes)
         (candle_cv_analytic_instruction_list sources)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack))
     ==>
     ?result certificate_rest.
       candle_q_packed_object_source_planned_program_run
         center_boxes outer_boxes radii codes sources certificates stack
         result certificate_rest /\
       candle_cv_q_packed_object_dispatch_program
         (candle_cv_q_interval_list center_boxes)
         (candle_cv_q_interval_list outer_boxes)
         (candle_cv_q_list radii)
         (candle_cv_q_packed_object_plan_code_list codes)
         (candle_cv_analytic_instruction_list sources)
         (candle_cv_q_interval_list certificates)
         (candle_cv_q_packed_object_stack_encode stack) =
       candle_cv_q_packed_object_certificate_state T
         (candle_cv_q_packed_object_stack_encode result)
         (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "input") THEN
  MP_TAC
    (SPECL
      [`codes:num list`; `sources:candle_analytic_instruction list`;
       `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
       `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
       `radii:((num#num)#num)list`;
       `certificates:(((num#num)#num)#((num#num)#num))list`;
       `stack:(candle_q_packed_object_item)list`]
      candle_cv_q_packed_object_dispatch_program_success_planned) THEN
  ANTS_TAC THENL
   [USE_THEN "input" ACCEPT_TAC;
    DISCH_THEN
      (X_CHOOSE_THEN `result:(candle_q_packed_object_item)list`
        (X_CHOOSE_THEN
          `certificate_rest:(((num#num)#num)#((num#num)#num))list`
          (LABEL_TAC "logical_run")))] THEN
  MAP_EVERY EXISTS_TAC
    [`result:(candle_q_packed_object_item)list`;
     `certificate_rest:(((num#num)#num)#((num#num)#num))list`] THEN
  CONJ_TAC THENL
   [USE_THEN "logical_run" ACCEPT_TAC;
    MATCH_MP_TAC candle_cv_q_packed_object_dispatch_program_forward THEN
    USE_THEN "input" MP_TAC THEN ASM_MESON_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_dispatch_program_head_success;
     candle_cv_q_packed_object_dispatch_program_cons_head;
     candle_cv_q_packed_object_dispatch_program_cons_tail;
     candle_q_packed_object_source_planned_program_run_cons;
     candle_cv_q_packed_object_dispatch_program_success_planned;
     candle_cv_q_packed_object_dispatch_program_success_exact] then
  failwith "packed object dispatch program success sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_DISPATCH_PROGRAM_SUCCESS_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
