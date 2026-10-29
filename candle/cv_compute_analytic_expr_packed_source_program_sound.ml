(* ========================================================================== *)
(* Whole-program semantic preservation for packed analytic source replay.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A successful logical run is a finite chain   *)
(* of authenticated source steps.  The theorem below lifts the one-step      *)
(* invariant to that chain without adding any arithmetic assumptions.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_step_sound.ml";;

module Candle_cv_analytic_expr_packed_source_program_sound = struct

open Candle_cv_analytic_expr_packed_source_item_invariant;;
open Candle_cv_analytic_expr_packed_source_step_sound;;

let candle_q_packed_source_program_run_def = define
 `(candle_q_packed_source_program_run boxes [] stack result <=>
     result = stack) /\
  (candle_q_packed_source_program_run boxes (CONS source sources)
      stack result <=>
     ?next.
       candle_q_packed_source_step boxes source stack next /\
       candle_q_packed_source_program_run boxes sources next result)`;;

let candle_q_packed_source_program_run_analytic_invariant = prove
 (`!boxes sources stack result.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_stack_analytic_invariant boxes stack /\
     candle_q_packed_source_program_run boxes sources stack result
     ==>
     candle_q_packed_source_stack_analytic_invariant boxes result`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_program_run_def] THEN
    MESON_TAC[];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_packed_source_program_run_def] THEN
    STRIP_TAC THEN
    ASM_MESON_TAC[candle_q_packed_source_step_analytic_invariant]]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_source_program_run_analytic_invariant] then
  failwith "packed source program sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_PROGRAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
