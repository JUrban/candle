(* Focused closed-theorem test for fixed nonlinear compiler soundness. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_compile_sound.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_compile_sound;;

let candle_fixed_nonlinear_compile_sound_theorems =
 [candle_fsn_logical_program_step_poly;
  candle_fsn_logical_program_step_sqrt;
  candle_fsn_logical_program_step_neg;
  candle_fsn_logical_program_step_add;
  candle_fsn_logical_program_step_mul;
  candle_fsn_logical_program_step_square;
  candle_fsn_logical_program_step_inv;
  candle_fsn_logical_program_step_atn;
  candle_fsn_logical_program_step_pi_half;
  candle_fsn_logical_program_run_append;
  candle_fsn_logical_program_run_append_single;
  candle_fsn_logical_program_run_append_binary;
  candle_fsn_logical_compile_run_analytic_invariant];;

if exists (fun th -> hyp th <> [])
  candle_fixed_nonlinear_compile_sound_theorems then
  failwith "fixed nonlinear compile theorem assumptions"
else if exists (fun th -> frees (concl th) <> [])
  candle_fixed_nonlinear_compile_sound_theorems then
  failwith "fixed nonlinear compile theorem free variables"
else
  print_endline
    ("CANDLE_FIXED_NONLINEAR_COMPILE_SOUND_OK theorems=" ^
     string_of_int (length candle_fixed_nonlinear_compile_sound_theorems) ^
     " assumptions=0 free_variables=0");;
