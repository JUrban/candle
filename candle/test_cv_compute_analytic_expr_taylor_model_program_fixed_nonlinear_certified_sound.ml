(* Focused closed-theorem test for fixed nonlinear certified soundness. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_certified_sound.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_certified_sound;;

let candle_fixed_nonlinear_certified_sound_theorems =
 [candle_cv_fsn_program_correct;
  candle_q_dim_taylor_model_program_fixed_nonlinear_result;
  candle_q_dim_taylor_model_fixed_nonlinear_compile_analytic_invariant;
  candle_cv_fsn_certified_check_correct;
  candle_q_dim_taylor_model_fixed_nonlinear_certified_upper_sound;
  candle_q_dim_taylor_model_fixed_nonlinear_certified_accept_sound];;

if exists (fun th -> hyp th <> [])
  candle_fixed_nonlinear_certified_sound_theorems then
  failwith "fixed nonlinear certified theorem assumptions"
else if exists (fun th -> frees (concl th) <> [])
  candle_fixed_nonlinear_certified_sound_theorems then
  failwith "fixed nonlinear certified theorem free variables"
else
  print_endline
    ("CANDLE_FIXED_NONLINEAR_CERTIFIED_SOUND_OK theorems=" ^
     string_of_int (length candle_fixed_nonlinear_certified_sound_theorems) ^
     " assumptions=0 free_variables=0");;
