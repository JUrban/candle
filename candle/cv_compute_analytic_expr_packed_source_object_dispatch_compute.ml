(* ========================================================================== *)
(* Executable planned dispatch for the exact packed object-q source replay.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Code zero uses the ordinary exact-object     *)
(* evaluator.  Codes one through six first authenticate the exact source    *)
(* instruction and then push the matching explicit-radius object state.      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_ordinary_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_specialized_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_complete_program_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_dispatch_compute = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_packed_source_delta_specialization_sound;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_complete_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_representation;;
open Candle_cv_analytic_expr_packed_source_object_nonpoly_compute;;
open Candle_cv_analytic_expr_packed_source_object_ordinary_compute;;
open Candle_cv_analytic_expr_packed_source_object_specialized_compute;;

let candle_cv_q_packed_object_specialized_step_def = new_definition
 `candle_cv_q_packed_object_specialized_step
      center_boxes outer_boxes radii code source certificates stack =
    Cexp_if (Cexp_eq code (Cexp_num 1))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (candle_packed_delta_product_source_poly 0)))))
        (candle_cv_q_packed_object_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_object_delta_product_source_item_state
              radii center_boxes outer_boxes (Cexp_num 0)) stack)
          certificates)
        (candle_cv_q_packed_object_certificate_failure stack certificates))
    (Cexp_if (Cexp_eq code (Cexp_num 2))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (candle_packed_delta_product_source_poly 1)))))
        (candle_cv_q_packed_object_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_object_delta_product_source_item_state
              radii center_boxes outer_boxes (Cexp_num 1)) stack)
          certificates)
        (candle_cv_q_packed_object_certificate_failure stack certificates))
    (Cexp_if (Cexp_eq code (Cexp_num 3))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (candle_packed_delta_product_source_poly 2)))))
        (candle_cv_q_packed_object_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_object_delta_product_source_item_state
              radii center_boxes outer_boxes (Cexp_num 2)) stack)
          certificates)
        (candle_cv_q_packed_object_certificate_failure stack certificates))
    (Cexp_if (Cexp_eq code (Cexp_num 4))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (candle_packed_delta_neg_derivative_poly 3)))))
        (candle_cv_q_packed_object_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_object_delta_neg_derivative_item_state
              radii center_boxes (Cexp_num 3)) stack)
          certificates)
        (candle_cv_q_packed_object_certificate_failure stack certificates))
    (Cexp_if (Cexp_eq code (Cexp_num 5))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (candle_packed_delta_neg_derivative_poly 4)))))
        (candle_cv_q_packed_object_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_object_delta_neg_derivative_item_state
              radii center_boxes (Cexp_num 4)) stack)
          certificates)
        (candle_cv_q_packed_object_certificate_failure stack certificates))
    (Cexp_if (Cexp_eq code (Cexp_num 6))
      (Cexp_if
        (Cexp_eq source
          (candle_cv_analytic_instruction
            (Candle_analytic_push_poly
              (candle_poly_compile
                (candle_packed_delta_neg_derivative_poly 5)))))
        (candle_cv_q_packed_object_certificate_state T
          (Cexp_pair
            (candle_cv_q_packed_object_delta_neg_derivative_item_state
              radii center_boxes (Cexp_num 5)) stack)
          certificates)
        (candle_cv_q_packed_object_certificate_failure stack certificates))
      (candle_cv_q_packed_object_certificate_failure
        stack certificates))))))`;;

let candle_cv_q_packed_object_if_one = prove
 (`!positive negative. Cexp_if (Cexp_num 1) positive negative = positive`,
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; cexp_if_def]);;

let candle_cv_q_packed_object_specialized_product_correct = prove
 (`!center_boxes outer_boxes radii coordinate source certificates stack.
     LENGTH radii = 6 /\
     candle_packed_delta_product_source_instruction coordinate source
     ==>
     candle_cv_q_packed_object_specialized_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii) (Cexp_num (SUC coordinate))
       (candle_cv_analytic_instruction source)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode stack) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (candle_q_packed_object_delta_product_source_item
             radii center_boxes outer_boxes coordinate) stack))
       (candle_cv_q_interval_list certificates)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_packed_delta_product_source_instruction_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2`
    MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  let state_th =
    MATCH_MP
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_boxes:
            ((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:
            ((((num#num)#num)#((num#num)#num))list)`;
         `coordinate:num`]
        candle_cv_q_packed_object_delta_product_source_item_state_correct)
      (ASSUME `LENGTH (radii:((num#num)#num)list) = 6`) in
  ASM_REWRITE_TAC
      [candle_cv_q_packed_object_specialized_step_def;
       state_th;
       candle_cv_q_packed_object_stack_encode_def;
       cexp_eq_def; injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[candle_cv_q_packed_object_if_one; cexp_if_def]);;

let _ = print_endline "CANDLE_OBJECT_DISPATCH_STAGE specialized_product";;

let candle_cv_q_packed_object_specialized_neg_correct = prove
 (`!center_boxes outer_boxes radii coordinate source certificates stack.
     LENGTH radii = 6 /\
     candle_packed_delta_neg_derivative_source_instruction coordinate source
     ==>
     candle_cv_q_packed_object_specialized_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii) (Cexp_num (SUC coordinate))
       (candle_cv_analytic_instruction source)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode stack) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode
         (CONS
           (candle_q_packed_object_delta_neg_derivative_item
             radii center_boxes coordinate) stack))
       (candle_cv_q_interval_list certificates)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_packed_delta_neg_derivative_source_instruction_def] THEN
  STRIP_TAC THEN
  let state_3 =
    MATCH_MP
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_boxes:
            ((((num#num)#num)#((num#num)#num))list)`;
         `3`]
        candle_cv_q_packed_object_delta_neg_derivative_item_state_correct)
      (CONJ
        (ASSUME `LENGTH (radii:((num#num)#num)list) = 6`)
        (ARITH_RULE `3 = 3 \/ 3 = 4 \/ 3 = 5`)) in
  let state_4 =
    MATCH_MP
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_boxes:
            ((((num#num)#num)#((num#num)#num))list)`;
         `4`]
        candle_cv_q_packed_object_delta_neg_derivative_item_state_correct)
      (CONJ
        (ASSUME `LENGTH (radii:((num#num)#num)list) = 6`)
        (ARITH_RULE `4 = 3 \/ 4 = 4 \/ 4 = 5`)) in
  let state_5 =
    MATCH_MP
      (SPECL
        [`radii:((num#num)#num)list`;
         `center_boxes:
            ((((num#num)#num)#((num#num)#num))list)`;
         `5`]
        candle_cv_q_packed_object_delta_neg_derivative_item_state_correct)
      (CONJ
        (ASSUME `LENGTH (radii:((num#num)#num)list) = 6`)
        (ARITH_RULE `5 = 3 \/ 5 = 4 \/ 5 = 5`)) in
  ASM_REWRITE_TAC
    [candle_cv_q_packed_object_specialized_step_def;
     state_3; state_4; state_5;
     candle_cv_q_packed_object_stack_encode_def;
     cexp_eq_def; injectivity "cval"; NOT_SUC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[candle_cv_q_packed_object_if_one; cexp_if_def]);;

let _ = print_endline "CANDLE_OBJECT_DISPATCH_STAGE specialized_neg";;

let candle_cv_q_packed_object_specialized_planned_correct = prove
 (`!center_boxes outer_boxes radii code source certificates stack next
       certificate_rest.
     LENGTH radii = 6 /\
     candle_q_packed_object_source_planned_step
       center_boxes outer_boxes radii code source certificates stack next
       certificate_rest /\
     ~(code = 0)
     ==>
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
      (CONJUNCTS_THEN2 (LABEL_TAC "planned")
        (LABEL_TAC "nonzero"))) THEN
  USE_THEN "planned" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_object_source_planned_step_def] THEN
  DISCH_THEN STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_specialized_product_correct THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_specialized_neg_correct THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_specialized_neg_correct THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_specialized_neg_correct THEN
    ASM_MESON_TAC[]]);;

let _ = print_endline "CANDLE_OBJECT_DISPATCH_STAGE specialized_planned";;

let candle_cv_q_packed_object_dispatch_step_def = new_definition
 `candle_cv_q_packed_object_dispatch_step
      center_boxes outer_boxes radii code source certificates stack =
    Cexp_if (Cexp_eq code (Cexp_num 0))
      (candle_cv_q_packed_object_ordinary_step
        center_boxes outer_boxes radii source certificates stack)
      (candle_cv_q_packed_object_specialized_step
        center_boxes outer_boxes radii code source certificates stack)`;;

let candle_cv_q_packed_object_dispatch_planned_correct = prove
 (`!center_boxes outer_boxes radii code source certificates stack next
       certificate_rest.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_planned_step
       center_boxes outer_boxes radii code source certificates stack next
       certificate_rest
     ==>
     candle_cv_q_packed_object_dispatch_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list outer_boxes)
       (candle_cv_q_list radii) (Cexp_num code)
       (candle_cv_analytic_instruction source)
       (candle_cv_q_interval_list certificates)
       (candle_cv_q_packed_object_stack_encode stack) =
     candle_cv_q_packed_object_certificate_state T
       (candle_cv_q_packed_object_stack_encode next)
       (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `code = 0` THENL
   [ASM_REWRITE_TAC
      [candle_cv_q_packed_object_dispatch_step_def;
       cexp_eq_def; cexp_if_def] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_ordinary_step_correct THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
      `candle_q_packed_object_source_planned_step
        center_boxes outer_boxes radii code source certificates stack next
        certificate_rest` THEN
    REWRITE_TAC[candle_q_packed_object_source_planned_step_def] THEN
    ASM_REWRITE_TAC[NOT_SUC] THEN MESON_TAC[];
    ASM_REWRITE_TAC
      [candle_cv_q_packed_object_dispatch_step_def;
       cexp_eq_def; injectivity "cval"; cexp_if_def] THEN
    MATCH_MP_TAC candle_cv_q_packed_object_specialized_planned_correct THEN
    ASM_REWRITE_TAC[]]);;

let _ = print_endline "CANDLE_OBJECT_DISPATCH_STAGE planned_step";;

let candle_cv_q_packed_object_plan_code_list_def = define
 `(candle_cv_q_packed_object_plan_code_list [] = Cexp_num 0) /\
  (candle_cv_q_packed_object_plan_code_list (CONS code codes) =
     Cexp_pair (Cexp_num code)
       (candle_cv_q_packed_object_plan_code_list codes))`;;

let candle_cv_q_packed_object_dispatch_program_def = define
 `(candle_cv_q_packed_object_dispatch_program
      center_boxes outer_boxes radii
      (Cexp_num code_end) (Cexp_num source_end) certificates stack =
      candle_cv_q_packed_object_certificate_state T stack certificates) /\
  (candle_cv_q_packed_object_dispatch_program
      center_boxes outer_boxes radii
      (Cexp_num code_end) (Cexp_pair source sources) certificates stack =
      candle_cv_q_packed_object_certificate_failure stack certificates) /\
  (candle_cv_q_packed_object_dispatch_program
      center_boxes outer_boxes radii
      (Cexp_pair code codes) (Cexp_num source_end) certificates stack =
      candle_cv_q_packed_object_certificate_failure stack certificates) /\
  (candle_cv_q_packed_object_dispatch_program
      center_boxes outer_boxes radii
      (Cexp_pair code codes) (Cexp_pair source sources)
      certificates stack =
     let step =
       candle_cv_q_packed_object_dispatch_step
         center_boxes outer_boxes radii code source certificates stack in
     Cexp_if (Cexp_eq (Cexp_fst step) (Cexp_num 1))
       (candle_cv_q_packed_object_dispatch_program
         center_boxes outer_boxes radii codes sources
         (Cexp_snd (Cexp_snd step))
         (Cexp_fst (Cexp_snd step)))
       (candle_cv_q_packed_object_certificate_failure
         stack certificates))`;;

let candle_cv_q_packed_object_dispatch_program_forward = prove
 (`!codes sources center_boxes outer_boxes radii certificates stack result
       certificate_rest.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_object_source_stack_analytic_invariant
       center_boxes outer_boxes stack /\
     candle_q_packed_object_source_planned_program_run
       center_boxes outer_boxes radii codes sources certificates stack result
       certificate_rest
     ==>
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
      [candle_q_packed_object_source_planned_program_run_def;
       candle_cv_q_packed_object_plan_code_list_def;
       candle_cv_analytic_instruction_list_def;
       candle_cv_q_packed_object_dispatch_program_def] THEN
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
        ALL_TAC] THEN
      SUBGOAL_THEN
       `candle_cv_q_packed_object_dispatch_step
          (candle_cv_q_interval_list center_boxes)
          (candle_cv_q_interval_list outer_boxes)
          (candle_cv_q_list radii) (Cexp_num h)
          (candle_cv_analytic_instruction source_head)
          (candle_cv_q_interval_list certificates)
          (candle_cv_q_packed_object_stack_encode stack) =
        candle_cv_q_packed_object_certificate_state T
          (candle_cv_q_packed_object_stack_encode next)
          (candle_cv_q_interval_list next_certificates)`
      (LABEL_TAC "step_compute") THENL
       [MATCH_MP_TAC candle_cv_q_packed_object_dispatch_planned_correct THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `candle_cv_q_packed_object_dispatch_program
          (candle_cv_q_interval_list center_boxes)
          (candle_cv_q_interval_list outer_boxes)
          (candle_cv_q_list radii)
          (candle_cv_q_packed_object_plan_code_list t)
          (candle_cv_analytic_instruction_list source_tail)
          (candle_cv_q_interval_list next_certificates)
          (candle_cv_q_packed_object_stack_encode next) =
        candle_cv_q_packed_object_certificate_state T
          (candle_cv_q_packed_object_stack_encode result)
          (candle_cv_q_interval_list certificate_rest)`
      (LABEL_TAC "tail_compute") THENL
       [USE_THEN "induction_hypothesis" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC
        [candle_cv_q_packed_object_plan_code_list_def;
         candle_cv_analytic_instruction_list_def;
         candle_cv_q_packed_object_dispatch_program_def;
         LET_DEF; LET_END_DEF] THEN
      USE_THEN "step_compute"
        (fun theorem -> REWRITE_TAC[theorem]) THEN
      REWRITE_TAC
        [candle_cv_q_packed_object_certificate_state_def;
         candle_cv_bool_def; cexp_fst_def; cexp_snd_def;
         cexp_eq_def; cexp_if_def] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[candle_cv_q_packed_object_if_one] THEN
      USE_THEN "tail_compute"
        (fun theorem ->
          REWRITE_TAC
            [REWRITE_RULE
              [candle_cv_q_packed_object_certificate_state_def;
               candle_cv_bool_def]
              theorem] THEN
          REWRITE_TAC[candle_cv_cval_one_suc])]]);;

let _ = print_endline "CANDLE_OBJECT_DISPATCH_STAGE planned_program";;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_object_if_one;
     candle_cv_q_packed_object_specialized_product_correct;
     candle_cv_q_packed_object_specialized_neg_correct;
     candle_cv_q_packed_object_specialized_planned_correct;
     candle_cv_q_packed_object_dispatch_planned_correct;
     candle_cv_q_packed_object_dispatch_program_forward] then
  failwith "packed object dispatch compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_DISPATCH_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
