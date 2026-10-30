(* ========================================================================== *)
(* Exact whole-program soundness for planned packed source dispatch.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Successful executable replay is tied to one   *)
(* authenticated logical source/certificate run and its exact returned state. *)
(* ========================================================================== *)

module Candle_cv_analytic_expr_packed_source_certificate_dispatch_program_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_program_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_step_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound;;

let candle_cv_q_packed_source_plan_code_list_def = define
 `(candle_cv_q_packed_source_plan_code_list [] = Cexp_num 0) /\
  (candle_cv_q_packed_source_plan_code_list (CONS code codes) =
     Cexp_pair (Cexp_num code)
       (candle_cv_q_packed_source_plan_code_list codes))`;;

let candle_q_packed_source_planned_program_instructions_def = define
 `(candle_q_packed_source_planned_program_instructions [] [] <=> T) /\
  (candle_q_packed_source_planned_program_instructions
      [] (CONS source sources) <=> F) /\
  (candle_q_packed_source_planned_program_instructions
      (CONS code codes) [] <=> F) /\
  (candle_q_packed_source_planned_program_instructions
      (CONS code codes) (CONS source sources) <=>
     candle_q_packed_source_plan_instruction code source /\
     candle_q_packed_source_planned_program_instructions codes sources)`;;

let candle_q_packed_source_planned_certificate_program_run_def = define
 `(candle_q_packed_source_planned_certificate_program_run
      boxes [] [] certificates stack result certificate_rest <=>
      result = stack /\ certificate_rest = certificates) /\
  (candle_q_packed_source_planned_certificate_program_run
      boxes [] (CONS source sources) certificates stack result
      certificate_rest <=> F) /\
  (candle_q_packed_source_planned_certificate_program_run
      boxes (CONS code codes) [] certificates stack result
      certificate_rest <=> F) /\
  (candle_q_packed_source_planned_certificate_program_run
      boxes (CONS code codes) (CONS source sources) certificates stack
      result certificate_rest <=>
     ?next next_certificates.
       candle_q_packed_source_planned_certificate_step
         boxes code source certificates stack next next_certificates /\
       candle_q_packed_source_planned_certificate_program_run
         boxes codes sources next_certificates next result
         certificate_rest)`;;

let candle_cv_q_packed_source_certificate_dispatch_program_def = define
 `(candle_cv_q_packed_source_certificate_dispatch_program
      boxes (Cexp_num code_end) (Cexp_num source_end) certificates stack =
      candle_cv_q_packed_source_certificate_state T stack certificates) /\
  (candle_cv_q_packed_source_certificate_dispatch_program
      boxes (Cexp_num code_end) (Cexp_pair source sources)
      certificates stack =
      candle_cv_q_packed_source_certificate_failure stack certificates) /\
  (candle_cv_q_packed_source_certificate_dispatch_program
      boxes (Cexp_pair code codes) (Cexp_num source_end)
      certificates stack =
      candle_cv_q_packed_source_certificate_failure stack certificates) /\
  (candle_cv_q_packed_source_certificate_dispatch_program
      boxes (Cexp_pair code codes) (Cexp_pair source sources)
      certificates stack =
     let step =
       candle_cv_q_packed_source_certificate_dispatch_step
         boxes code source certificates stack in
     Cexp_if (Cexp_eq (Cexp_fst step) (Cexp_num 1))
       (candle_cv_q_packed_source_certificate_dispatch_program
         boxes codes sources
         (Cexp_snd (Cexp_snd step))
         (Cexp_fst (Cexp_snd step)))
       (candle_cv_q_packed_source_certificate_failure
         stack certificates))`;;

print_endline "CANDLE_V1901_DISPATCH_PROGRAM_DEFINITIONS_OK";;

let candle_q_packed_source_planned_certificate_program_run_refines = prove
 (`!boxes codes sources certificates stack result certificate_rest.
    candle_q_packed_source_planned_certificate_program_run
      boxes codes sources certificates stack result certificate_rest
    ==> candle_q_packed_source_certificate_program_run
      boxes sources certificates stack result certificate_rest`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC (ISPEC `sources:candle_analytic_instruction list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_packed_source_planned_certificate_program_run_def;
       candle_q_packed_source_certificate_program_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    GEN_TAC THEN
    MP_TAC (ISPEC `sources:candle_analytic_instruction list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_q_packed_source_planned_certificate_program_run_def];
      REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_q_packed_source_planned_certificate_program_run_def;
         candle_q_packed_source_certificate_program_run_def] THEN
      DISCH_THEN (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
      USE_THEN "induction_hypothesis" MP_TAC THEN
      ASM_MESON_TAC
        [candle_q_packed_source_planned_certificate_step_source_step]]]);;

let candle_cv_q_packed_source_certificate_state_true = prove
 (`!stack certificates.
    candle_cv_q_packed_source_certificate_state T stack certificates =
    Cexp_pair (Cexp_num 1) (Cexp_pair stack certificates)`,
  REWRITE_TAC[candle_cv_q_packed_source_certificate_state_def;
              candle_cv_bool_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_source_certificate_dispatch_program_forward = prove
 (`!boxes codes sources certificates stack result certificate_rest.
    candle_q_packed_source_planned_certificate_program_run
      boxes codes sources certificates stack result certificate_rest
    ==> candle_cv_q_packed_source_certificate_dispatch_program
      (candle_cv_q_interval_list boxes)
      (candle_cv_q_packed_source_plan_code_list codes)
      (candle_cv_analytic_instruction_list sources)
      (candle_cv_q_interval_list certificates)
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results stack)) =
    candle_cv_q_packed_source_certificate_state T
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results result))
      (candle_cv_q_interval_list certificate_rest)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC (ISPEC `sources:candle_analytic_instruction list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_packed_source_planned_certificate_program_run_def;
       candle_cv_q_packed_source_plan_code_list_def;
       candle_cv_analytic_instruction_list_def;
       candle_cv_q_packed_source_certificate_dispatch_program_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    GEN_TAC THEN
    MP_TAC (ISPEC `sources:candle_analytic_instruction list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_q_packed_source_planned_certificate_program_run_def];
      REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_q_packed_source_planned_certificate_program_run_def] THEN
      DISCH_THEN
        (REPEAT_TCL CHOOSE_THEN
          (CONJUNCTS_THEN2 (LABEL_TAC "planned") (LABEL_TAC "tail"))) THEN
      REWRITE_TAC
        [candle_cv_q_packed_source_plan_code_list_def;
         candle_cv_analytic_instruction_list_def;
         candle_cv_q_packed_source_certificate_dispatch_program_def;
         LET_DEF; LET_END_DEF] THEN
      USE_THEN "planned"
        (fun theorem ->
          REWRITE_TAC
            [MATCH_MP
              (SPEC_ALL
                candle_cv_q_packed_source_certificate_dispatch_planned_correct)
              theorem]) THEN
      REWRITE_TAC
        [candle_cv_q_packed_source_certificate_state_def;
         candle_cv_bool_def; cexp_fst_def; cexp_snd_def;
         cexp_eq_def; cexp_if_def] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[candle_cv_q_packed_source_certificate_if_one] THEN
      ONCE_REWRITE_TAC
        [GSYM candle_cv_q_packed_source_certificate_state_true] THEN
      USE_THEN "induction_hypothesis" MATCH_MP_TAC THEN
      USE_THEN "tail" ACCEPT_TAC]]);;

print_endline "CANDLE_V1902_DISPATCH_PROGRAM_FORWARD_OK";;

let candle_cv_q_packed_source_certificate_dispatch_program_head_success = prove
 (`!step recursive failure_stack failure_certificates.
    candle_cv_q_packed_source_certificate_success
      (Cexp_if (Cexp_eq (Cexp_fst step) (Cexp_num 1))
        recursive
        (candle_cv_q_packed_source_certificate_failure
          failure_stack failure_certificates))
    ==> candle_cv_q_packed_source_certificate_success step`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `candle_cv_q_packed_source_certificate_success step` THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_cv_q_packed_source_certificate_success_def]) THEN
  ASM_REWRITE_TAC
    [cexp_eq_def; cexp_if_def;
     candle_cv_q_packed_source_certificate_success_failure]);;

let candle_cv_q_packed_source_certificate_dispatch_program_cons_head = prove
 (`!boxes code codes source sources certificates stack.
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_program
        boxes (Cexp_pair code codes) (Cexp_pair source sources)
        certificates stack)
    ==> candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_step
        boxes code source certificates stack)`,
  REPEAT GEN_TAC THEN DISCH_THEN
   (fun theorem ->
      ACCEPT_TAC
       (MATCH_MP
         (SPECL
          [`candle_cv_q_packed_source_certificate_dispatch_step
              boxes code source certificates stack`;
           `candle_cv_q_packed_source_certificate_dispatch_program
              boxes codes sources
              (Cexp_snd
                (Cexp_snd
                  (candle_cv_q_packed_source_certificate_dispatch_step
                    boxes code source certificates stack)))
              (Cexp_fst
                (Cexp_snd
                  (candle_cv_q_packed_source_certificate_dispatch_step
                    boxes code source certificates stack)))`;
           `stack:cval`; `certificates:cval`]
          candle_cv_q_packed_source_certificate_dispatch_program_head_success)
         (REWRITE_RULE
           [candle_cv_q_packed_source_certificate_dispatch_program_def;
            LET_DEF; LET_END_DEF]
           theorem))));;

let candle_cv_q_packed_source_certificate_dispatch_program_cons_tail = prove
 (`!boxes code codes source sources certificates stack next next_certificates.
    candle_cv_q_packed_source_certificate_dispatch_step
      boxes code source certificates stack =
      candle_cv_q_packed_source_certificate_state T next next_certificates /\
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_program
        boxes (Cexp_pair code codes) (Cexp_pair source sources)
        certificates stack)
    ==> candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_program
        boxes codes sources next_certificates next)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "step_exact") (LABEL_TAC "whole_success")) THEN
  USE_THEN "whole_success" MP_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_dispatch_program_def;
     LET_DEF; LET_END_DEF] THEN
  USE_THEN "step_exact" (fun theorem -> REWRITE_TAC[theorem]) THEN
  REWRITE_TAC
    [candle_cv_q_packed_source_certificate_state_def;
     candle_cv_bool_def; cexp_fst_def; cexp_snd_def;
     cexp_eq_def; cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[candle_cv_q_packed_source_certificate_if_one]);;

print_endline "CANDLE_V1903_DISPATCH_PROGRAM_STRUCTURAL_OK";;

let candle_dispatch_program_cons_exact_statement =
 `?next next_certificates.
    candle_q_packed_source_planned_certificate_step
      boxes code source certificates stack next next_certificates /\
    candle_cv_q_packed_source_certificate_dispatch_step
      (candle_cv_q_interval_list boxes) (Cexp_num code)
      (candle_cv_analytic_instruction source)
      (candle_cv_q_interval_list certificates)
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results stack)) =
    candle_cv_q_packed_source_certificate_state T
      (candle_cv_q_dim_taylor_model_result_list_encode
        (candle_q_packed_source_item_results next))
      (candle_cv_q_interval_list next_certificates)`;;

let candle_dispatch_program_cons_finish theorem
    (assumptions,goal_term as goal) =
  let planned_step,step_exact = CONJ_PAIR theorem in
  let _,arguments = strip_comb (concl planned_step) in
  let next = el 5 arguments
  and next_certificates = el 6 arguments in
  let _,state_arguments = strip_comb (rhs (concl step_exact)) in
  let encoded_next = el 1 state_arguments
  and encoded_next_certificates = el 2 state_arguments in
  let success_pattern =
    `candle_cv_q_packed_source_certificate_success state` in
  let whole_success =
    find
      (fun theorem ->
        can (term_match [] success_pattern) (concl theorem))
      (map snd assumptions) in
  let tail_success =
    MATCH_MP
      (SPECL
        [`candle_cv_q_interval_list boxes`; `Cexp_num code`;
         `code_tail:cval`; `candle_cv_analytic_instruction source`;
         `source_tail:cval`; `candle_cv_q_interval_list certificates`;
         `candle_cv_q_dim_taylor_model_result_list_encode
            (candle_q_packed_source_item_results stack)`;
         encoded_next; encoded_next_certificates]
        candle_cv_q_packed_source_certificate_dispatch_program_cons_tail)
      (CONJ step_exact whole_success) in
  (MAP_EVERY EXISTS_TAC [next; next_certificates] THEN
   ACCEPT_TAC (CONJ planned_step tail_success)) goal;;

let candle_dispatch_program_cons_exact_tactic =
  MATCH_MP_TAC
    candle_cv_q_packed_source_certificate_dispatch_success_exact THEN
  CONJ_TAC THENL
   [FIRST_ASSUM MATCH_ACCEPT_TAC;
    MATCH_MP_TAC
      (SPECL
        [`candle_cv_q_interval_list boxes`; `Cexp_num code`;
         `code_tail:cval`; `candle_cv_analytic_instruction source`;
         `source_tail:cval`; `candle_cv_q_interval_list certificates`;
         `candle_cv_q_dim_taylor_model_result_list_encode
            (candle_q_packed_source_item_results stack)`]
        candle_cv_q_packed_source_certificate_dispatch_program_cons_head) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC];;

let candle_dispatch_program_cons_witness_tactic goal =
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN candle_dispatch_program_cons_exact_statement MP_TAC THENL
    [candle_dispatch_program_cons_exact_tactic;
     DISCH_THEN
       (REPEAT_TCL CHOOSE_THEN candle_dispatch_program_cons_finish)]) goal;;

let candle_cv_q_packed_source_certificate_dispatch_program_cons_witness = prove
 (`!boxes code code_tail source source_tail certificates stack.
    candle_q_packed_source_plan_instruction code source /\
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_program
        (candle_cv_q_interval_list boxes)
        (Cexp_pair (Cexp_num code) code_tail)
        (Cexp_pair (candle_cv_analytic_instruction source) source_tail)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?next next_certificates.
      candle_q_packed_source_planned_certificate_step
        boxes code source certificates stack next next_certificates /\
      candle_cv_q_packed_source_certificate_success
        (candle_cv_q_packed_source_certificate_dispatch_program
          (candle_cv_q_interval_list boxes) code_tail source_tail
          (candle_cv_q_interval_list next_certificates)
          (candle_cv_q_dim_taylor_model_result_list_encode
            (candle_q_packed_source_item_results next)))`,
  candle_dispatch_program_cons_witness_tactic);;

let candle_q_packed_source_planned_certificate_program_run_cons = prove
 (`!boxes code codes source sources certificates stack next next_certificates
       result certificate_rest.
    candle_q_packed_source_planned_certificate_step
      boxes code source certificates stack next next_certificates /\
    candle_q_packed_source_planned_certificate_program_run
      boxes codes sources next_certificates next result certificate_rest
    ==> candle_q_packed_source_planned_certificate_program_run
      boxes (CONS code codes) (CONS source sources) certificates stack
      result certificate_rest`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_packed_source_planned_certificate_program_run_def] THEN
  MESON_TAC[]);;

let candle_cv_q_packed_source_certificate_dispatch_program_cons_logic = prove
 (`!boxes code codes source sources certificates stack.
    (!next_certificates next.
       candle_cv_q_packed_source_certificate_success
         (candle_cv_q_packed_source_certificate_dispatch_program
           (candle_cv_q_interval_list boxes)
           (candle_cv_q_packed_source_plan_code_list codes)
           (candle_cv_analytic_instruction_list sources)
           (candle_cv_q_interval_list next_certificates)
           (candle_cv_q_dim_taylor_model_result_list_encode
             (candle_q_packed_source_item_results next)))
       ==> ?result certificate_rest.
         candle_q_packed_source_planned_certificate_program_run
           boxes codes sources next_certificates next result certificate_rest) /\
    candle_q_packed_source_plan_instruction code source /\
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_program
        (candle_cv_q_interval_list boxes)
        (Cexp_pair (Cexp_num code)
          (candle_cv_q_packed_source_plan_code_list codes))
        (Cexp_pair (candle_cv_analytic_instruction source)
          (candle_cv_analytic_instruction_list sources))
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?result certificate_rest.
      candle_q_packed_source_planned_certificate_program_run
        boxes (CONS code codes) (CONS source sources) certificates stack
        result certificate_rest`,
  MESON_TAC
   [candle_cv_q_packed_source_certificate_dispatch_program_cons_witness;
    candle_q_packed_source_planned_certificate_program_run_cons]);;

let candle_cv_q_packed_source_certificate_dispatch_program_cons_induction =
  prove
 (`!boxes code codes source sources certificates stack.
    (!actual_sources actual_certificates actual_stack.
       candle_q_packed_source_planned_program_instructions
         codes actual_sources /\
       candle_cv_q_packed_source_certificate_success
         (candle_cv_q_packed_source_certificate_dispatch_program
           (candle_cv_q_interval_list boxes)
           (candle_cv_q_packed_source_plan_code_list codes)
           (candle_cv_analytic_instruction_list actual_sources)
           (candle_cv_q_interval_list actual_certificates)
           (candle_cv_q_dim_taylor_model_result_list_encode
             (candle_q_packed_source_item_results actual_stack)))
       ==> ?result certificate_rest.
         candle_q_packed_source_planned_certificate_program_run
           boxes codes actual_sources actual_certificates actual_stack
           result certificate_rest) /\
    candle_q_packed_source_plan_instruction code source /\
    candle_q_packed_source_planned_program_instructions codes sources /\
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_program
        (candle_cv_q_interval_list boxes)
        (Cexp_pair (Cexp_num code)
          (candle_cv_q_packed_source_plan_code_list codes))
        (Cexp_pair (candle_cv_analytic_instruction source)
          (candle_cv_analytic_instruction_list sources))
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?result certificate_rest.
      candle_q_packed_source_planned_certificate_program_run
        boxes (CONS code codes) (CONS source sources) certificates stack
        result certificate_rest`,
  MESON_TAC
    [candle_cv_q_packed_source_certificate_dispatch_program_cons_logic]);;

let candle_cv_q_packed_source_certificate_dispatch_program_success_planned =
  prove
 (`!boxes codes sources certificates stack.
    candle_q_packed_source_planned_program_instructions codes sources /\
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_program
        (candle_cv_q_interval_list boxes)
        (candle_cv_q_packed_source_plan_code_list codes)
        (candle_cv_analytic_instruction_list sources)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?result certificate_rest.
      candle_q_packed_source_planned_certificate_program_run
        boxes codes sources certificates stack result certificate_rest`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC (ISPEC `sources:candle_analytic_instruction list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_packed_source_planned_program_instructions_def;
       candle_cv_q_packed_source_plan_code_list_def;
       candle_cv_analytic_instruction_list_def;
       candle_cv_q_packed_source_certificate_dispatch_program_def;
       candle_cv_q_packed_source_certificate_success_state;
       candle_q_packed_source_planned_certificate_program_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    GEN_TAC THEN
    MP_TAC (ISPEC `sources:candle_analytic_instruction list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_q_packed_source_planned_program_instructions_def];
      REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_q_packed_source_planned_program_instructions_def;
         candle_cv_q_packed_source_plan_code_list_def;
         candle_cv_analytic_instruction_list_def] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC
        candle_cv_q_packed_source_certificate_dispatch_program_cons_induction THEN
      ASM_REWRITE_TAC[]]]);;

let candle_cv_q_packed_source_certificate_dispatch_program_success_exact = prove
 (`!boxes codes sources certificates stack.
    candle_q_packed_source_planned_program_instructions codes sources /\
    candle_cv_q_packed_source_certificate_success
      (candle_cv_q_packed_source_certificate_dispatch_program
        (candle_cv_q_interval_list boxes)
        (candle_cv_q_packed_source_plan_code_list codes)
        (candle_cv_analytic_instruction_list sources)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)))
    ==> ?result certificate_rest.
      candle_q_packed_source_planned_certificate_program_run
        boxes codes sources certificates stack result certificate_rest /\
      candle_cv_q_packed_source_certificate_dispatch_program
        (candle_cv_q_interval_list boxes)
        (candle_cv_q_packed_source_plan_code_list codes)
        (candle_cv_analytic_instruction_list sources)
        (candle_cv_q_interval_list certificates)
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results stack)) =
      candle_cv_q_packed_source_certificate_state T
        (candle_cv_q_dim_taylor_model_result_list_encode
          (candle_q_packed_source_item_results result))
        (candle_cv_q_interval_list certificate_rest)`,
  REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "input") THEN
  MATCH_MP_TAC candle_exists_pair_strengthen THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC
      candle_cv_q_packed_source_certificate_dispatch_program_success_planned THEN
    USE_THEN "input" ACCEPT_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC
      candle_cv_q_packed_source_certificate_dispatch_program_forward THEN
    ASM_REWRITE_TAC[]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_source_planned_certificate_program_run_refines;
     candle_cv_q_packed_source_certificate_dispatch_program_forward;
     candle_cv_q_packed_source_certificate_dispatch_program_head_success;
     candle_cv_q_packed_source_certificate_dispatch_program_cons_head;
     candle_cv_q_packed_source_certificate_dispatch_program_cons_tail;
     candle_cv_q_packed_source_certificate_dispatch_program_cons_witness;
     candle_q_packed_source_planned_certificate_program_run_cons;
     candle_cv_q_packed_source_certificate_dispatch_program_cons_logic;
     candle_cv_q_packed_source_certificate_dispatch_program_cons_induction;
     candle_cv_q_packed_source_certificate_dispatch_program_success_planned;
     candle_cv_q_packed_source_certificate_dispatch_program_success_exact]
then failwith "packed dispatch program sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFICATE_DISPATCH_PROGRAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
