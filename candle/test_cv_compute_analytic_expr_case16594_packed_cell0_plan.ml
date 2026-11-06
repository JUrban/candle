(* ========================================================================== *)
(* Genuine case-16594 cell 0: authenticate the complete packed source plan.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Polynomial witnesses are recovered by the     *)
(* proved postfix decoder and then recompiled in the logic.  The six nonzero  *)
(* plan codes are admitted only after exact source equality with the general  *)
(* delta specialization predicates.                                          *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_cell0_entry_fixture.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_cell0_plan = struct

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_analytic_expr_packed_source_delta_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_specialization_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_program_sound;;
open Candle_cv_analytic_expr_packed_source_identity_sound;;
open Test_cv_compute_analytic_expr_case16594_packed_cell0_entry_fixture;;

let candle_case16594_cell0_poly_of_program program =
  let decode_term =
    list_mk_comb (`candle_poly_decode_run`,[program; `[]:candle_poly_expr list`]) in
  let decode =
    REWRITE_CONV
      [candle_poly_decode_run_def; candle_poly_decode_step_def;
       candle_poly_decode_head_def; candle_poly_decode_tail_def]
      decode_term in
  match dest_list (rand (concl decode)) with
  | [polynomial] -> polynomial
  | _ -> failwith "case16594 cell0 plan: polynomial program did not decode to one value";;

let candle_case16594_cell0_poly_compile program polynomial =
  let compilation =
    REWRITE_CONV[candle_poly_compile_def; APPEND]
      (mk_comb (`candle_poly_compile`,polynomial)) in
  if not (aconv (rand (concl compilation)) program) then
    failwith "case16594 cell0 plan: decoded polynomial did not recompile";
  compilation;;

let candle_case16594_cell0_push_poly_source source =
  let constructor,program = dest_comb source in
  if not (aconv constructor
      `Candle_analytic_push_poly:
         candle_q_instruction list->candle_analytic_instruction`) then
    failwith "case16594 cell0 plan: expected polynomial source";
  program;;

let candle_case16594_cell0_ordinary_plan code source =
  if not (aconv code `0`) then
    failwith "case16594 cell0 plan: ordinary code is not zero";
  let ordinary_goal =
    mk_comb (`candle_q_packed_source_ordinary_instruction`,source) in
  let ordinary =
    try
      EQT_ELIM
        ((REWRITE_CONV
           [candle_q_packed_source_ordinary_instruction_def;
            distinctness "candle_analytic_instruction";
            injectivity "candle_analytic_instruction"]
          THENC NUM_REDUCE_CONV) ordinary_goal)
    with Failure _ ->
      try
        prove
          (ordinary_goal,
           REWRITE_TAC
             [candle_q_packed_source_ordinary_instruction_def;
              distinctness "candle_analytic_instruction";
              injectivity "candle_analytic_instruction"] THEN
           MESON_TAC[])
      with Failure _ ->
      let program = candle_case16594_cell0_push_poly_source source in
      let polynomial = candle_case16594_cell0_poly_of_program program in
      let valid_goal =
        list_mk_comb (`candle_poly_valid_dim`,[`6`;polynomial]) in
      let valid =
        EQT_ELIM
          ((REWRITE_CONV[candle_poly_valid_dim_def] THENC NUM_REDUCE_CONV)
            valid_goal) in
      let compilation =
        candle_case16594_cell0_poly_compile program polynomial in
      let source_identity =
        SYM
          (AP_TERM
            `Candle_analytic_push_poly:
               candle_q_instruction list->candle_analytic_instruction`
            compilation) in
      prove
        (ordinary_goal,
         REWRITE_TAC[candle_q_packed_source_ordinary_instruction_def] THEN
         DISJ1_TAC THEN EXISTS_TAC polynomial THEN
         ACCEPT_TAC (CONJ valid source_identity)) in
  let goal =
    list_mk_comb
      (`candle_q_packed_source_plan_instruction`,[code;source]) in
  prove
    (goal,
     REWRITE_TAC[candle_q_packed_source_plan_instruction_def] THEN
     MESON_TAC[ordinary]);;

let candle_case16594_cell0_specialized_source coordinate source =
  let program = candle_case16594_cell0_push_poly_source source in
  let coordinate_term = mk_numeral (Num.num_of_int coordinate) in
  let expected_polynomial =
    if coordinate < 3 then
      mk_comb (`candle_packed_delta_product_source_poly`,coordinate_term)
    else
      mk_comb
        (`candle_packed_delta_neg_derivative_poly`,coordinate_term) in
  let coordinate_rewrites =
    map
      (fun candidate ->
         NUM_EQ_CONV
           (mk_eq
             (coordinate_term,
              mk_numeral (Num.num_of_int candidate))))
      [3;4;5] in
  let expected_compilation =
    REWRITE_CONV
      (coordinate_rewrites @
       [candle_packed_delta_product_source_poly_def;
        candle_packed_delta_neg_derivative_poly_def;
        candle_packed_delta_neg_derivative_poly3_def;
        candle_packed_delta_neg_derivative_poly4_def;
        candle_packed_delta_neg_derivative_poly5_def;
        candle_packed_delta_poly_def; candle_poly_diff_def;
        candle_poly_compile_def; APPEND])
      (mk_comb (`candle_poly_compile`,expected_polynomial)) in
  if not (aconv (rand (concl expected_compilation)) program) then
    failwith
      ("case16594 cell0 plan: specialized source mismatch at coordinate " ^
       string_of_int coordinate ^
       "\nactual=" ^ string_of_term program ^
       "\nexpected=" ^ string_of_term (rand (concl expected_compilation)));
  let source_identity =
    SYM
      (AP_TERM
        `Candle_analytic_push_poly:
           candle_q_instruction list->candle_analytic_instruction`
        expected_compilation) in
  if coordinate < 3 then
    let goal =
      list_mk_comb
        (`candle_packed_delta_product_source_instruction`,
         [coordinate_term;source]) in
    prove
      (goal,
       REWRITE_TAC[candle_packed_delta_product_source_instruction_def] THEN
       CONJ_TAC THENL
        [CONV_TAC NUM_REDUCE_CONV;
         ACCEPT_TAC source_identity])
  else
    let goal =
      list_mk_comb
        (`candle_packed_delta_neg_derivative_source_instruction`,
         [coordinate_term;source]) in
    prove
      (goal,
       REWRITE_TAC
         [candle_packed_delta_neg_derivative_source_instruction_def] THEN
       ACCEPT_TAC source_identity);;

let candle_case16594_cell0_specialized_plan code source =
  let code_number = Num.int_of_num (dest_numeral code) in
  if code_number < 1 || code_number > 6 then
    failwith "case16594 cell0 plan: specialized code outside 1--6";
  let coordinate = code_number - 1 in
  let coordinate_term = mk_numeral (Num.num_of_int coordinate) in
  let specialized =
    candle_case16594_cell0_specialized_source coordinate source in
  let goal =
    list_mk_comb
      (`candle_q_packed_source_plan_instruction`,[code;source]) in
  if coordinate < 3 then
    prove
      (goal,
       REWRITE_TAC[candle_q_packed_source_plan_instruction_def] THEN
       DISJ2_TAC THEN DISJ1_TAC THEN
       EXISTS_TAC coordinate_term THEN
       CONJ_TAC THENL
        [CONV_TAC NUM_REDUCE_CONV;
         CONJ_TAC THENL
          [CONV_TAC NUM_REDUCE_CONV;
           REWRITE_TAC[specialized]]])
  else
    prove
      (goal,
       REWRITE_TAC[candle_q_packed_source_plan_instruction_def] THEN
       DISJ2_TAC THEN DISJ2_TAC THEN
       EXISTS_TAC coordinate_term THEN
       CONJ_TAC THENL
        [CONV_TAC NUM_REDUCE_CONV;
         CONJ_TAC THENL
          [CONV_TAC NUM_REDUCE_CONV;
           REWRITE_TAC[specialized]]]);;

let candle_case16594_cell0_instruction_plans =
  let codes = dest_list candle_case16594_cell0_plan_codes
  and sources = dest_list candle_case16594_cell0_sources in
  if length codes <> length sources then
    failwith "case16594 cell0 plan: code/source length mismatch";
  let index = ref 0 in
  map2
    (fun code source ->
       let current = !index in
       index := current + 1;
       print_endline
         ("CANDLE_CV_CASE16594_CELL0_PLAN_INSTRUCTION index=" ^
          string_of_int current ^ " code=" ^ string_of_term code);
       try
         if aconv code `0` then
           candle_case16594_cell0_ordinary_plan code source
         else candle_case16594_cell0_specialized_plan code source
       with Failure message ->
         failwith
           ("case16594 cell0 plan instruction " ^ string_of_int current ^
            ": " ^ message))
    codes sources;;

let candle_case16594_cell0_plan_goal =
  list_mk_comb
    (`candle_q_packed_source_planned_program_instructions`,
     [candle_case16594_cell0_plan_codes;candle_case16594_cell0_sources]);;

let candle_case16594_cell0_plan =
  EQT_ELIM
    (REWRITE_CONV
      (candle_q_packed_source_planned_program_instructions_def ::
       candle_case16594_cell0_instruction_plans)
      candle_case16594_cell0_plan_goal);;

if hyp candle_case16594_cell0_plan <> [] ||
   not (aconv (concl candle_case16594_cell0_plan)
          candle_case16594_cell0_plan_goal) then
  failwith "case16594 cell0 plan: theorem validation failed";;

print_endline
  "CANDLE_CV_CASE16594_CELL0_PLAN_OK instructions=167 specialized=6 assumptions=0 DEVELOPMENT_NON_RELEASE";;

end;;
