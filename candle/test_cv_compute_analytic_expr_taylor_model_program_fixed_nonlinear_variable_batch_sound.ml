(* Focused closed-theorem test for fixed-nonlinear variable batches. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_batch_sound;;

let candle_fixed_nonlinear_variable_batch_sound_theorems =
  [candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept;
   candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept_mem;
   candle_cv_fsn_variable_jobs_check_correct];;

if not
    (List.for_all
      (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
      candle_fixed_nonlinear_variable_batch_sound_theorems) then
  failwith "fixed nonlinear variable batch soundness: open theorem";;

print_endline
  ("CANDLE_FIXED_NONLINEAR_VARIABLE_BATCH_SOUND_OK theorems=" ^
   string_of_int (length candle_fixed_nonlinear_variable_batch_sound_theorems) ^
   " assumptions=0 free_variables=0");;
