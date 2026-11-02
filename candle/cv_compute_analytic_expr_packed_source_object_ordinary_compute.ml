(* ========================================================================== *)
(* Fail-closed executable replay of complete ordinary object-q source steps.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. Polynomial blocks execute from an empty local  *)
(* stack and must return exactly one encoded item. All remaining ordinary     *)
(* instructions use the certificate-aware non-polynomial executor.            *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_nonpoly_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_ordinary_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_ordinary_compute = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_poly_compute;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_compute;;

let candle_cv_q_packed_object_ordinary_step_def = new_definition
 `candle_cv_q_packed_object_ordinary_step center_boxes outer_boxes radii
      source certificates stack =
    Cexp_if (Cexp_ispair source)
      (Cexp_if (Cexp_eq (Cexp_fst source) (Cexp_num 0))
        (let execution =
           candle_cv_q_packed_object_poly_run center_boxes outer_boxes radii
             (Cexp_snd source)
             (candle_cv_q_packed_object_execution_state T (Cexp_num 0)) in
         let result_stack = Cexp_snd execution in
         Cexp_if (Cexp_fst execution)
           (Cexp_if (Cexp_ispair result_stack)
             (Cexp_if (Cexp_eq (Cexp_snd result_stack) (Cexp_num 0))
               (candle_cv_q_packed_object_certificate_state T
                 (Cexp_pair (Cexp_fst result_stack) stack) certificates)
               (candle_cv_q_packed_object_certificate_failure
                 stack certificates))
             (candle_cv_q_packed_object_certificate_failure
               stack certificates))
           (candle_cv_q_packed_object_certificate_failure
             stack certificates))
        (candle_cv_q_packed_object_nonpoly_step
          center_boxes outer_boxes radii source certificates stack))
      (candle_cv_q_packed_object_nonpoly_step
        center_boxes outer_boxes radii source certificates stack)`;;

let candle_cv_q_packed_object_ordinary_push_poly_correct = prove
 (`!center_boxes outer_boxes radii certificates stack program result.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_poly_run radii center_boxes outer_boxes
       program [] [result]
     ==>
     candle_cv_q_packed_object_ordinary_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction (Candle_analytic_push_poly program))
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode stack) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode (CONS result stack))
       (candle_cv_q_interval_list certificates)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_poly_run
      (candle_cv_q_interval_list center_boxes)
      (candle_cv_q_interval_list outer_boxes)
      (candle_cv_q_list radii)
      (candle_cv_q_instruction_list program)
      (candle_cv_q_packed_object_execution_state T
        (candle_cv_q_packed_object_stack_encode [])) =
    candle_cv_q_packed_object_execution_state T
      (candle_cv_q_packed_object_stack_encode [result])`
  (LABEL_TAC "poly") THENL
   [MATCH_MP_TAC candle_cv_q_packed_object_poly_run_correct THEN
    ASM_REWRITE_TAC
      [candle_q_packed_object_source_stack_analytic_invariant_def; ALL];
    REWRITE_TAC
      [candle_cv_q_packed_object_ordinary_step_def;
       candle_cv_analytic_instruction_def;
       candle_cv_q_packed_object_execution_state_def;
       candle_cv_q_packed_object_stack_encode_def;
       LET_DEF; LET_END_DEF;
       cexp_ispair_def; cexp_eq_def; cexp_if_def;
       cexp_fst_def; cexp_snd_def;
       injectivity "cval"; NOT_SUC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cexp_if_def] THEN
    USE_THEN "poly"
      (fun theorem ->
        REWRITE_TAC
          [REWRITE_RULE
            [candle_cv_q_packed_object_execution_state_def;
             candle_cv_q_packed_object_stack_encode_def]
            theorem]) THEN
    REWRITE_TAC
      [candle_cv_bool_def; candle_cv_cval_one_suc;
       cexp_fst_def; cexp_snd_def; cexp_ispair_def;
       cexp_eq_def; cexp_if_def; injectivity "cval"; NOT_SUC;
       candle_cv_q_packed_object_stack_encode_def] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cexp_if_def]]);;

let _ = print_endline "CANDLE_OBJECT_ORDINARY_STAGE push_poly";;

let candle_cv_q_packed_object_ordinary_nonpoly_dispatch = prove
 (`!center_boxes outer_boxes radii source certificates stack next
       certificate_rest.
     candle_q_packed_object_source_nonpoly_step
       radii source certificates stack next certificate_rest
     ==>
     candle_cv_q_packed_object_ordinary_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction source)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode stack) =
     candle_cv_q_packed_object_nonpoly_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction source)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode stack)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_nonpoly_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_packed_object_ordinary_step_def;
     candle_cv_analytic_instruction_def;
     cexp_ispair_def; cexp_fst_def; cexp_eq_def; cexp_if_def;
     injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def]);;

let _ = print_endline "CANDLE_OBJECT_ORDINARY_STAGE nonpoly_dispatch";;

let candle_cv_q_packed_object_ordinary_step_correct = prove
 (`!center_boxes outer_boxes radii source certificates stack next
       certificate_rest.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_ordinary_step center_boxes outer_boxes
       radii source certificates stack next certificate_rest
     ==>
     candle_cv_q_packed_object_ordinary_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction source)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode stack) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode next)
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_length")
      (CONJUNCTS_THEN2 (LABEL_TAC "outer_length")
        (CONJUNCTS_THEN2 (LABEL_TAC "radii_length")
          (CONJUNCTS_THEN2 (LABEL_TAC "correspondence")
            (CONJUNCTS_THEN2 (LABEL_TAC "stack_invariant")
              (LABEL_TAC "step")))))) THEN
  USE_THEN "step" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_ordinary_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_ordinary_push_poly_correct THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `candle_cv_q_packed_object_ordinary_step
        (candle_cv_q_interval_list center_boxes)
        (candle_cv_q_interval_list outer_boxes)
        (candle_cv_q_list radii)
        (candle_cv_analytic_instruction source)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_packed_object_stack_encode stack) =
      candle_cv_q_packed_object_nonpoly_step
        (candle_cv_q_interval_list center_boxes)
        (candle_cv_q_interval_list outer_boxes)
        (candle_cv_q_list radii)
        (candle_cv_analytic_instruction source)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_packed_object_stack_encode stack)`
    (LABEL_TAC "dispatch") THENL
     [MATCH_MP_TAC
        (SPECL
          [`center_boxes:
              ((((num#num)#num)#((num#num)#num))list)`;
           `outer_boxes:
              ((((num#num)#num)#((num#num)#num))list)`;
           `radii:((num#num)#num)list`;
           `source:candle_analytic_instruction`;
           `certificates:
              ((((num#num)#num)#((num#num)#num))list)`;
           `stack:candle_q_packed_object_item list`;
           `next:candle_q_packed_object_item list`;
           `certificate_rest:
              ((((num#num)#num)#((num#num)#num))list)`]
          candle_cv_q_packed_object_ordinary_nonpoly_dispatch) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "dispatch" (fun theorem -> REWRITE_TAC[theorem]) THEN
    MATCH_MP_TAC candle_cv_q_packed_object_nonpoly_step_correct THEN
    ASM_REWRITE_TAC[]]);;

let _ = print_endline "CANDLE_OBJECT_ORDINARY_STAGE generic_step";;

let candle_cv_q_packed_object_ordinary_run_def = define
 `(candle_cv_q_packed_object_ordinary_run center_boxes outer_boxes radii
      (Cexp_num n) execution = execution) /\
  (candle_cv_q_packed_object_ordinary_run center_boxes outer_boxes radii
      (Cexp_pair source sources) execution =
    Cexp_if (Cexp_fst execution)
      (candle_cv_q_packed_object_ordinary_run center_boxes outer_boxes radii
        sources
        (candle_cv_q_packed_object_ordinary_step
          center_boxes outer_boxes radii source
          (Cexp_snd (Cexp_snd execution))
          (Cexp_fst (Cexp_snd execution))))
      execution)`;;

let candle_cv_q_packed_object_ordinary_run_correct = prove
 (`!sources center_boxes outer_boxes radii certificates stack result
       certificate_rest.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_ordinary_program_run
       center_boxes outer_boxes radii sources certificates stack result
       certificate_rest
     ==>
     candle_cv_q_packed_object_ordinary_run
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii)
       (candle_cv_analytic_instruction_list sources)
       (candle_cv_q_packed_object_certificate_state T
         (candle_cv_q_packed_object_stack_encode stack)
         (candle_cv_q_interval_list certificates)) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode result)
       (candle_cv_q_interval_list certificate_rest)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_packed_object_source_ordinary_program_run_def;
       candle_cv_analytic_instruction_list_def;
       candle_cv_q_packed_object_ordinary_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_packed_object_source_ordinary_program_run_def] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "center_length")
        (CONJUNCTS_THEN2 (LABEL_TAC "outer_length")
          (CONJUNCTS_THEN2 (LABEL_TAC "radii_length")
            (CONJUNCTS_THEN2 (LABEL_TAC "correspondence")
              (CONJUNCTS_THEN2 (LABEL_TAC "stack_invariant")
                (REPEAT_TCL CHOOSE_THEN
                  (CONJUNCTS_THEN2 (LABEL_TAC "step")
                    (LABEL_TAC "tail_run")))))))) THEN
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
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_cv_q_packed_object_ordinary_step
        (candle_cv_q_interval_list center_boxes)
        (candle_cv_q_interval_list outer_boxes)
        (candle_cv_q_list radii)
        (candle_cv_analytic_instruction h)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_packed_object_stack_encode stack) =
      candle_cv_q_packed_object_certificate_state T
        (candle_cv_q_packed_object_stack_encode next)
        (candle_cv_q_interval_list next_certificates)`
    (LABEL_TAC "step_compute") THENL
     [MATCH_MP_TAC candle_cv_q_packed_object_ordinary_step_correct THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_list_def;
       candle_cv_q_packed_object_ordinary_run_def;
       candle_cv_q_packed_object_certificate_state_def;
       candle_cv_bool_def; candle_cv_cval_one_suc;
       cexp_fst_def; cexp_snd_def; cexp_if_def] THEN
    USE_THEN "step_compute"
      (fun theorem ->
        REWRITE_TAC
          [REWRITE_RULE[candle_cv_q_packed_object_certificate_state_def]
            theorem]) THEN
    REWRITE_TAC[candle_cv_bool_def] THEN
    USE_THEN "induction_hypothesis"
      (fun theorem ->
        MATCH_MP_TAC
          (REWRITE_RULE
            [candle_cv_q_packed_object_certificate_state_def;
             candle_cv_bool_def]
            theorem)) THEN
    ASM_REWRITE_TAC[]]);;

let _ = print_endline "CANDLE_OBJECT_ORDINARY_STAGE program_run";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_ordinary_push_poly_correct;
     candle_cv_q_packed_object_ordinary_nonpoly_dispatch;
     candle_cv_q_packed_object_ordinary_step_correct;
     candle_cv_q_packed_object_ordinary_run_correct] then
  failwith "packed object ordinary compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_ORDINARY_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
