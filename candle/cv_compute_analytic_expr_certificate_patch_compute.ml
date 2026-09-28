(* ========================================================================== *)
(* Executable certificate-data patching for stable analytic source programs. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The executable patcher mirrors the logical    *)
(* state-passing patcher.  It changes only tag-1 square-root payloads and     *)
(* returns unused interval data explicitly, so a checked caller can require  *)
(* exact consumption.                                                        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_certificate_patch.ml";;
needs "candle/cv_compute_analytic_expr_program_compute.ml";;

module Candle_cv_analytic_expr_certificate_patch_compute = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_certificate_patch;;

let candle_cv_analytic_instruction_patch_sqrt_def = new_definition
 `candle_cv_analytic_instruction_patch_sqrt intervals instruction =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 1))
        (Cexp_if (Cexp_ispair intervals)
          (Cexp_pair (Cexp_snd intervals)
            (Cexp_pair (Cexp_num 1) (Cexp_fst intervals)))
          (Cexp_pair intervals instruction))
        (Cexp_pair intervals instruction))
      (Cexp_pair intervals instruction)`;;

let candle_cv_analytic_program_patch_sqrt_def = define
 `(candle_cv_analytic_program_patch_sqrt intervals (Cexp_num n) =
     Cexp_pair intervals (Cexp_num n)) /\
  (candle_cv_analytic_program_patch_sqrt intervals
      (Cexp_pair instruction program) =
     let patched_instruction =
       candle_cv_analytic_instruction_patch_sqrt intervals instruction in
     let patched_program =
       candle_cv_analytic_program_patch_sqrt
         (Cexp_fst patched_instruction) program in
     Cexp_pair (Cexp_fst patched_program)
       (Cexp_pair (Cexp_snd patched_instruction)
         (Cexp_snd patched_program)))`;;

let candle_cv_analytic_program_patch_sqrt_compute = prove
 (`!intervals program.
     candle_cv_analytic_program_patch_sqrt intervals program =
     Cexp_if (Cexp_ispair program)
       (let patched_instruction =
          candle_cv_analytic_instruction_patch_sqrt intervals
            (Cexp_fst program) in
        let patched_program =
          candle_cv_analytic_program_patch_sqrt
            (Cexp_fst patched_instruction) (Cexp_snd program) in
        Cexp_pair (Cexp_fst patched_program)
          (Cexp_pair (Cexp_snd patched_instruction)
            (Cexp_snd patched_program)))
       (Cexp_pair intervals program)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_analytic_program_patch_sqrt_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_analytic_instruction_patch_sqrt_correct = prove
 (`!instruction intervals.
     candle_cv_analytic_instruction_patch_sqrt
       (candle_cv_q_interval_list intervals)
       (candle_cv_analytic_instruction instruction) =
     Cexp_pair
       (candle_cv_q_interval_list
         (FST (candle_analytic_instruction_patch_sqrt intervals instruction)))
       (candle_cv_analytic_instruction
         (SND
           (candle_analytic_instruction_patch_sqrt intervals instruction)))`,
  MATCH_MP_TAC candle_analytic_instruction_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       candle_cv_analytic_instruction_def;
       candle_cv_q_interval_list_def;
       cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def;
       cexp_eq_def; distinctness "cval"; injectivity "cval";
       NOT_SUC; ARITH_RULE `~(0 = 1)`; ARITH_RULE `1 = SUC 0`];
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       candle_cv_analytic_instruction_def;
       candle_cv_q_interval_list_def;
       cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       candle_cv_analytic_instruction_def;
       candle_cv_q_interval_list_def;
       cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       candle_cv_analytic_instruction_def;
       candle_cv_q_interval_list_def;
       cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       candle_cv_analytic_instruction_def;
       candle_cv_q_interval_list_def;
       cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       candle_cv_analytic_instruction_def;
       candle_cv_q_interval_list_def;
       cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def];
    GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       candle_cv_analytic_instruction_def;
       candle_cv_q_interval_list_def;
       cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def;
       cexp_eq_def; distinctness "cval"; injectivity "cval";
       ARITH_RULE `1 = SUC 0`];
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       candle_cv_analytic_instruction_def;
       candle_cv_q_interval_list_def;
       cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_analytic_instruction_patch_sqrt_def;
       candle_analytic_instruction_patch_sqrt_def;
       candle_cv_analytic_instruction_def;
       candle_cv_q_interval_list_def;
       cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]]);;

let candle_cv_analytic_program_patch_sqrt_correct = prove
 (`!program intervals.
     candle_cv_analytic_program_patch_sqrt
       (candle_cv_q_interval_list intervals)
       (candle_cv_analytic_instruction_list program) =
     Cexp_pair
       (candle_cv_q_interval_list
         (FST (candle_analytic_program_patch_sqrt intervals program)))
       (candle_cv_analytic_instruction_list
         (SND (candle_analytic_program_patch_sqrt intervals program)))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_analytic_instruction_list_def;
     candle_cv_analytic_program_patch_sqrt_def;
     candle_analytic_program_patch_sqrt_def;
     candle_cv_analytic_instruction_patch_sqrt_correct;
     cexp_fst_def; cexp_snd_def; LET_DEF; LET_END_DEF]);;

let candle_cv_analytic_program_patch_sqrt_compute_eqs =
 [SPEC_ALL candle_cv_analytic_program_patch_sqrt_compute;
  SPEC_ALL candle_cv_analytic_instruction_patch_sqrt_def];;

end;;
