(* Focused closed-theorem test for fixed nonlinear logical tagged items. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_item_invariant.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_item_invariant;;

let candle_fixed_nonlinear_item_invariant_theorems =
 [candle_cv_fs_interval_zeros_q_dimensions_correct;
  candle_cv_fs_interval_zero_matrix_q_dimensions_correct;
  candle_cv_fsn_result_pi_half_q_dimensions_correct;
  candle_cv_fsn_logical_item_inv_correct;
  candle_cv_fsn_logical_item_sqrt_correct;
  candle_cv_fsn_logical_item_atn_correct;
  candle_cv_fsn_logical_item_pi_half_correct;
  candle_fsn_logical_item_inv_analytic_invariant;
  candle_fsn_logical_item_sqrt_analytic_invariant;
  candle_fsn_logical_item_atn_analytic_invariant;
  candle_fsn_logical_item_pi_half_analytic_invariant];;

if exists (fun th -> hyp th <> [])
  candle_fixed_nonlinear_item_invariant_theorems then
  failwith "fixed nonlinear logical item theorem assumptions"
else if exists (fun th -> frees (concl th) <> [])
  candle_fixed_nonlinear_item_invariant_theorems then
  failwith "fixed nonlinear logical item theorem free variables"
else
  print_endline
    ("CANDLE_FIXED_NONLINEAR_ITEM_INVARIANT_OK theorems=" ^
     string_of_int (length candle_fixed_nonlinear_item_invariant_theorems) ^
     " assumptions=0 free_variables=0");;
