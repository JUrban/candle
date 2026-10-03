(* Focused closed-theorem test for the complete fixed-nonlinear checker. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_sound.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_sound;;

let candle_fixed_nonlinear_variable_complete_sound_theorems =
  [candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_components;
   candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_accept];;

if not
    (List.for_all
      (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
      candle_fixed_nonlinear_variable_complete_sound_theorems) then
  failwith "fixed nonlinear variable complete soundness: open theorem";;

print_endline
  ("CANDLE_FIXED_NONLINEAR_VARIABLE_COMPLETE_SOUND_OK theorems=" ^
   string_of_int
     (length candle_fixed_nonlinear_variable_complete_sound_theorems) ^
   " assumptions=0 free_variables=0");;
