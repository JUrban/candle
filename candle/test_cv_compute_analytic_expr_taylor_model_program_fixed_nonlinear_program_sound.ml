(* Focused closed-theorem test for the fixed nonlinear program representation. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_program_sound.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_program_sound;;

let candle_fixed_nonlinear_program_sound_theorems =
 [candle_cv_fsn_logical_program_step_correct;
  candle_cv_fsn_logical_program_run_correct];;

if exists (fun th -> hyp th <> [])
  candle_fixed_nonlinear_program_sound_theorems then
  failwith "fixed nonlinear program theorem assumptions"
else if exists (fun th -> frees (concl th) <> [])
  candle_fixed_nonlinear_program_sound_theorems then
  failwith "fixed nonlinear program theorem free variables"
else
  print_endline
    ("CANDLE_FIXED_NONLINEAR_PROGRAM_SOUND_OK theorems=" ^
     string_of_int (length candle_fixed_nonlinear_program_sound_theorems) ^
     " assumptions=0 free_variables=0");;
