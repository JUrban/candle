(* Focused closed-theorem test for the fixed-nonlinear analytic invariant. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_invariant.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_invariant;;

let candle_fixed_nonlinear_invariant_theorems =
 [candle_fsn_inv_hessian_contains;
  candle_fsn_inv_jet_components;
  candle_fsn_sqrt_value_contains;
  candle_fsn_sqrt_d_contains;
  candle_fsn_sqrt_dd_contains;
  candle_fsn_first_sqrt_contains;
  candle_fsn_unary_hessian_contains;
  candle_fsn_sqrt_hessian_contains;
  candle_fsn_sqrt_jet_components;
  candle_fsn_atn_value_contains;
  candle_fsn_atn_d_contains;
  candle_fsn_atn_dd_contains;
  candle_fsn_first_atn_contains;
  candle_fsn_atn_hessian_contains;
  candle_fsn_atn_jet_components;
  candle_fsn_pi_half_jet_components;
  candle_fsn_result_inv_analytic_hessian_contains;
  candle_fsn_result_inv_analytic_center_contains;
  candle_fsn_result_inv_analytic_center_shape;
  candle_fsn_result_inv_analytic_box_hessian_contains;
  candle_fsn_result_inv_analytic_invariant;
  candle_fsn_result_atn_analytic_hessian_contains;
  candle_fsn_result_atn_analytic_center_contains;
  candle_fsn_result_atn_analytic_center_shape;
  candle_fsn_result_atn_analytic_box_hessian_contains;
  candle_fsn_result_atn_analytic_invariant];;

if exists (fun th -> hyp th <> []) candle_fixed_nonlinear_invariant_theorems then
  failwith "fixed nonlinear invariant theorem assumptions"
else if exists (fun th -> frees (concl th) <> [])
  candle_fixed_nonlinear_invariant_theorems then
  failwith "fixed nonlinear invariant theorem free variables"
else
  print_endline
    ("CANDLE_FIXED_NONLINEAR_INVARIANT_OK theorems=" ^
     string_of_int (length candle_fixed_nonlinear_invariant_theorems) ^
     " assumptions=0 free_variables=0");;
