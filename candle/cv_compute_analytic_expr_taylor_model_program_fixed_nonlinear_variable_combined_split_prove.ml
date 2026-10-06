(* Compact-topology handoff for independently checked fixed-nonlinear batches. *)
(* Numerical acceptance and representation are combined by proved APPEND laws; *)
(* the existing split stack/forest soundness path is then used unchanged.       *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_combine_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_combined_split_prove = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_combine_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_stack_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_split_forest_prove;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_result_of_acceptance
    acceptance =
  {fixed_nonlinear_variable_raw_prepared_source =
     acceptance.fixed_nonlinear_raw_acceptance_prepared;
   fixed_nonlinear_variable_raw_encoded_jobs_term =
     acceptance.fixed_nonlinear_raw_acceptance_encoded_jobs_term;
   fixed_nonlinear_variable_raw_decoded_jobs_term =
     acceptance.fixed_nonlinear_raw_acceptance_jobs_term;
   fixed_nonlinear_variable_raw_representation_theorem =
     acceptance.fixed_nonlinear_raw_acceptance_representation_theorem;
   fixed_nonlinear_variable_raw_accept_theorem =
     acceptance.fixed_nonlinear_raw_acceptance_theorem};;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_combined_split_stack_six
    acceptance tokens encoded_tokens =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_split_stack_six
    (candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_result_of_acceptance
      acceptance)
    tokens encoded_tokens;;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_combined_split_forest_six
    acceptance tokens encoded_tokens expected_stack_boxes =
  candle_q_dim_taylor_model_fixed_nonlinear_variable_split_forest_six
    acceptance.fixed_nonlinear_raw_acceptance_prepared
    (candle_q_dim_taylor_model_fixed_nonlinear_variable_raw_result_of_acceptance
      acceptance)
    tokens encoded_tokens expected_stack_boxes;;

print_endline
  "CANDLE_CV_FIXED_NONLINEAR_VARIABLE_COMBINED_SPLIT_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
