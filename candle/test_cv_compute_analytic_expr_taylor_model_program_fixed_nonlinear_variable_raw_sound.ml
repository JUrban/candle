(* Focused closed-theorem test for canonical raw fixed-nonlinear batches. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_sound.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_sound;;

let candle_fixed_nonlinear_variable_raw_sound_theorems =
  [candle_cv_fsn_variable_raw_jobs_check_correct;
   candle_cv_fsn_variable_raw_jobs_check_representation_accept;
   candle_cv_fsn_variable_raw_jobs_check_accept];;

if not
    (List.for_all
      (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
      candle_fixed_nonlinear_variable_raw_sound_theorems) then
  failwith "fixed nonlinear variable raw soundness: open theorem";;

print_endline
  ("CANDLE_FIXED_NONLINEAR_VARIABLE_RAW_SOUND_OK theorems=" ^
   string_of_int (length candle_fixed_nonlinear_variable_raw_sound_theorems) ^
   " assumptions=0 free_variables=0");;
