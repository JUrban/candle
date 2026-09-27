(* ========================================================================== *)
(* Suffix-aware logical execution for the fixed/rational analytic program.   *)
(*                                                                            *)
(* A prefix cannot choose its fixed-scale tail from the prefix alone: later  *)
(* instructions may still contain a nonlinear operation.  The explicit      *)
(* future flag below makes that dependency compositional, so compiled source *)
(* expressions can be proved correct by structural induction.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_program_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound = struct

open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;

let candle_fsa_program_has_nonlinear_append = prove
 (`!left right.
     candle_fsa_program_has_nonlinear (APPEND left right) =
     (candle_fsa_program_has_nonlinear left \/
      candle_fsa_program_has_nonlinear right)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; candle_fsa_program_has_nonlinear_def;
                  OR_CLAUSES; DISJ_ASSOC]);;

let candle_fsa_logical_program_run_with_future_def = define
 `(candle_fsa_logical_program_run_with_future future_nonlinear
      center_boxes boxes radii [] box_program stack = stack) /\
  (candle_fsa_logical_program_run_with_future future_nonlinear
      center_boxes boxes radii (CONS ch ct) [] stack = stack) /\
  (candle_fsa_logical_program_run_with_future future_nonlinear
      center_boxes boxes radii (CONS ch ct) (CONS bh bt) stack =
     candle_fsa_logical_program_run_with_future future_nonlinear
       center_boxes boxes radii ct bt
       (candle_fsa_logical_program_step center_boxes boxes radii
         (~(candle_fsa_program_has_nonlinear ct \/ future_nonlinear))
         ch bh stack))`;;

let candle_fsa_logical_program_run_with_future_false = prove
 (`!center_program box_program center_boxes boxes radii stack.
     candle_fsa_logical_program_run_with_future F
       center_boxes boxes radii center_program box_program stack =
     candle_fsa_logical_program_run center_boxes boxes radii
       center_program box_program stack`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_fsa_logical_program_run_with_future_def;
                candle_fsa_logical_program_run_def];
    LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[candle_fsa_logical_program_run_with_future_def;
                    candle_fsa_logical_program_run_def; OR_CLAUSES]]);;

let candle_fsa_logical_program_run_with_future_append = prove
 (`!center_left box_left center_right box_right center_boxes boxes radii
      stack future_nonlinear.
     LENGTH center_left = LENGTH box_left
     ==>
     candle_fsa_logical_program_run_with_future future_nonlinear
       center_boxes boxes radii
       (APPEND center_left center_right) (APPEND box_left box_right) stack =
     candle_fsa_logical_program_run_with_future future_nonlinear
       center_boxes boxes radii center_right box_right
       (candle_fsa_logical_program_run_with_future
         (candle_fsa_program_has_nonlinear center_right \/
          future_nonlinear)
         center_boxes boxes radii center_left box_left stack)`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LENGTH; APPEND;
                candle_fsa_logical_program_run_with_future_def] THEN
    ARITH_TAC;
    LIST_INDUCT_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REPEAT GEN_TAC THEN
      REWRITE_TAC[LENGTH; SUC_INJ; APPEND;
                  candle_fsa_logical_program_run_with_future_def;
                  candle_fsa_program_has_nonlinear_append; DISJ_ASSOC] THEN
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

end;;
