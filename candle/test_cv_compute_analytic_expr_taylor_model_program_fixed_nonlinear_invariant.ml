(* Focused closed-theorem test for the fixed-nonlinear analytic invariant. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_invariant.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_invariant;;

let candle_fixed_nonlinear_invariant_theorems =
 [candle_fsn_inv_hessian_contains;
  candle_fsn_inv_jet_components];;

if exists (fun th -> hyp th <> []) candle_fixed_nonlinear_invariant_theorems then
  failwith "fixed nonlinear invariant theorem assumptions"
else
  print_endline
    ("CANDLE_FIXED_NONLINEAR_INVARIANT_OK theorems=" ^
     string_of_int (length candle_fixed_nonlinear_invariant_theorems) ^
     " assumptions=0");;
