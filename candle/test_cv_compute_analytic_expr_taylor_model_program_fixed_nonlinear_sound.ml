(* Focused closed-theorem test for the first fixed-nonlinear soundness layer. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_sound.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_sound;;

let candle_fixed_nonlinear_helper_theorems =
 [candle_cv_raw_bool_correct;
  candle_cv_fsn_interval_mul_correct;
  candle_cv_fsn_interval_list_scale_correct;
  candle_cv_fsn_interval_matrix_scale_correct;
  candle_cv_fsn_interval_outer_correct;
  candle_cv_fsn_q_inv_interval_correct;
  candle_cv_fsn_first_inv_correct;
  candle_cv_fsn_inv_hessian_correct;
  candle_cv_fsn_result_inv_correct;
  candle_cv_fsn_sqrt_domain_correct;
  candle_cv_fsn_first_sqrt_correct;
  candle_cv_fsn_sqrt_hessian_correct;
  candle_cv_fsn_result_sqrt_correct;
  candle_cv_fsn_atn_domain_correct;
  candle_cv_fsn_atn_d_fixed_correct;
  candle_cv_fsn_atn_dd_fixed_correct;
  candle_cv_fsn_first_atn_correct;
  candle_cv_fsn_atn_hessian_correct;
  candle_cv_fsn_result_atn_correct;
  candle_cv_fsn_result_pi_half_correct;
  candle_fsn_interval_mul_contains;
  candle_fsn_interval_list_scale_length;
  candle_fsn_interval_matrix_scale_shape;
  candle_fsn_interval_outer_shape;
  candle_fsn_first_inv_gradient_length;
  candle_fsn_first_sqrt_gradient_length;
  candle_fsn_first_atn_gradient_length;
  candle_fsn_inv_hessian_shape;
  candle_fsn_sqrt_hessian_shape;
  candle_fsn_atn_hessian_shape;
  candle_fsn_inv_jet_shape;
  candle_fsn_sqrt_jet_shape;
  candle_fsn_atn_jet_shape;
  candle_fsn_pi_half_jet_shape;
  candle_fsn_interval_list_scale_contains;
  candle_fsn_interval_matrix_scale_contains;
  candle_fsn_interval_outer_contains];;

if exists (fun th -> hyp th <> []) candle_fixed_nonlinear_helper_theorems then
  failwith "fixed nonlinear helper theorem assumptions"
else
  print_endline
    ("CANDLE_FIXED_NONLINEAR_HELPER_SOUND_OK theorems=" ^
     string_of_int (length candle_fixed_nonlinear_helper_theorems) ^
     " assumptions=0");;
