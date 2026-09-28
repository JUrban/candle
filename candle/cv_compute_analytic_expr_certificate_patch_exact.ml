(* ========================================================================== *)
(* Exact certificate-slot matching for stable analytic source programs.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This layer rejects both missing and surplus   *)
(* square-root payloads by walking the authenticated instruction skeleton and *)
(* the proposed certificate list together.                                   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_certificate_patch_compute.ml";;

module Candle_cv_analytic_expr_certificate_patch_exact = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_certificate_patch_compute;;

let candle_analytic_instruction_is_sqrt_def = define
 `(candle_analytic_instruction_is_sqrt
      (Candle_analytic_push_poly p) <=> F) /\
  (candle_analytic_instruction_is_sqrt
      Candle_analytic_program_neg <=> F) /\
  (candle_analytic_instruction_is_sqrt
      Candle_analytic_program_add <=> F) /\
  (candle_analytic_instruction_is_sqrt
      Candle_analytic_program_mul <=> F) /\
  (candle_analytic_instruction_is_sqrt
      Candle_analytic_program_square <=> F) /\
  (candle_analytic_instruction_is_sqrt
      Candle_analytic_program_inv <=> F) /\
  (candle_analytic_instruction_is_sqrt
      (Candle_analytic_program_sqrt s) <=> T) /\
  (candle_analytic_instruction_is_sqrt
      Candle_analytic_program_atn <=> F) /\
  (candle_analytic_instruction_is_sqrt
      Candle_analytic_program_pi_half <=> F)`;;

let candle_analytic_program_sqrt_data_exact_def = define
 `(candle_analytic_program_sqrt_data_exact
      ([]:(((num#num)#num)#((num#num)#num))list) [] <=> T) /\
  (candle_analytic_program_sqrt_data_exact (CONS i intervals) [] <=> F) /\
  (candle_analytic_program_sqrt_data_exact []
      (CONS instruction program) <=>
     ~candle_analytic_instruction_is_sqrt instruction /\
     candle_analytic_program_sqrt_data_exact [] program) /\
  (candle_analytic_program_sqrt_data_exact (CONS i intervals)
      (CONS instruction program) <=>
     if candle_analytic_instruction_is_sqrt instruction then
       candle_analytic_program_sqrt_data_exact intervals program
     else
       candle_analytic_program_sqrt_data_exact
         (CONS i intervals) program)`;;

let candle_cv_analytic_instruction_is_sqrt_def = new_definition
 `candle_cv_analytic_instruction_is_sqrt instruction =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_eq (Cexp_fst instruction) (Cexp_num 1))
      (Cexp_num 0)`;;

let candle_cv_analytic_program_sqrt_data_exact_def = define
 `(candle_cv_analytic_program_sqrt_data_exact intervals (Cexp_num n) =
     Cexp_if (Cexp_ispair intervals) (Cexp_num 0) (Cexp_num 1)) /\
  (candle_cv_analytic_program_sqrt_data_exact intervals
      (Cexp_pair instruction program) =
     Cexp_if (candle_cv_analytic_instruction_is_sqrt instruction)
       (Cexp_if (Cexp_ispair intervals)
         (candle_cv_analytic_program_sqrt_data_exact
           (Cexp_snd intervals) program)
         (Cexp_num 0))
       (candle_cv_analytic_program_sqrt_data_exact intervals program))`;;

let candle_cv_analytic_program_sqrt_data_exact_compute = prove
 (`!intervals program.
     candle_cv_analytic_program_sqrt_data_exact intervals program =
     Cexp_if (Cexp_ispair program)
       (Cexp_if
         (candle_cv_analytic_instruction_is_sqrt (Cexp_fst program))
         (Cexp_if (Cexp_ispair intervals)
           (candle_cv_analytic_program_sqrt_data_exact
             (Cexp_snd intervals) (Cexp_snd program))
           (Cexp_num 0))
         (candle_cv_analytic_program_sqrt_data_exact
           intervals (Cexp_snd program)))
       (Cexp_if (Cexp_ispair intervals) (Cexp_num 0) (Cexp_num 1))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_analytic_program_sqrt_data_exact_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_analytic_instruction_is_sqrt_correct = prove
 (`!instruction.
     candle_cv_analytic_instruction_is_sqrt
       (candle_cv_analytic_instruction instruction) =
     Cexp_num
       (if candle_analytic_instruction_is_sqrt instruction
        then SUC 0 else 0)`,
  MATCH_MP_TAC candle_analytic_instruction_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_analytic_instruction_is_sqrt_def;
     candle_analytic_instruction_is_sqrt_def;
     candle_cv_analytic_instruction_def;
     cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_eq_def;
     distinctness "cval"; injectivity "cval"; NOT_SUC;
     ARITH_RULE `1 = SUC 0`]);;

let candle_cv_analytic_program_sqrt_data_exact_correct = prove
 (`!program intervals.
     candle_cv_analytic_program_sqrt_data_exact
       (candle_cv_q_interval_list intervals)
       (candle_cv_analytic_instruction_list program) =
     Cexp_num
       (if candle_analytic_program_sqrt_data_exact intervals program
        then SUC 0 else 0)`,
  MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL
   [LIST_INDUCT_TAC THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_list_def;
       candle_cv_q_interval_list_def;
       candle_cv_analytic_program_sqrt_data_exact_def;
       candle_analytic_program_sqrt_data_exact_def;
       cexp_if_def; cexp_ispair_def] THEN
    REWRITE_TAC[injectivity "cval"] THEN CONV_TAC NUM_REDUCE_CONV;
    MAP_EVERY X_GEN_TAC
      [`instruction:candle_analytic_instruction`;
       `program:candle_analytic_instruction list`] THEN
    DISCH_THEN (LABEL_TAC "program_ih") THEN
    GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `intervals:(((num#num)#num)#((num#num)#num))list`
        list_CASES) THEN
    ASM_CASES_TAC
      `candle_analytic_instruction_is_sqrt instruction` THEN
    USE_THEN "program_ih"
      (fun ih ->
        ASM_REWRITE_TAC
          [ih;
           candle_cv_analytic_instruction_list_def;
           candle_cv_analytic_program_sqrt_data_exact_def;
           candle_analytic_program_sqrt_data_exact_def;
           candle_cv_analytic_instruction_is_sqrt_correct] THEN
        ASM_REWRITE_TAC
          [candle_cv_q_interval_list_def;
           cexp_if_def; cexp_ispair_def; cexp_snd_def; ONE;
           injectivity "cval"; ARITH_RULE `1 = SUC 0`]) THEN
    REWRITE_TAC[injectivity "cval"] THEN CONV_TAC NUM_REDUCE_CONV]);;

let candle_cv_analytic_program_sqrt_data_exact_compute_eqs =
 [SPEC_ALL candle_cv_analytic_program_sqrt_data_exact_compute;
  SPEC_ALL candle_cv_analytic_instruction_is_sqrt_def];;

end;;
