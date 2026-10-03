(* Focused closed-theorem test for fixed-nonlinear compact topology. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_compact_stack_sound.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_compact_stack_sound;;

let candle_fixed_nonlinear_variable_compact_sound_theorems =
  [candle_q_dim_taylor_model_fixed_nonlinear_variable_compact_job_sound;
   candle_q_dim_taylor_model_fixed_nonlinear_variable_compact_run_sound;
   candle_q_dim_taylor_model_fixed_nonlinear_variable_compact_sound];;

if not
    (List.for_all
      (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
      candle_fixed_nonlinear_variable_compact_sound_theorems) then
  failwith "fixed nonlinear variable compact soundness: open theorem";;

print_endline
  ("CANDLE_FIXED_NONLINEAR_VARIABLE_COMPACT_STACK_SOUND_OK theorems=" ^
   string_of_int
     (length candle_fixed_nonlinear_variable_compact_sound_theorems) ^
   " assumptions=0 free_variables=0");;
