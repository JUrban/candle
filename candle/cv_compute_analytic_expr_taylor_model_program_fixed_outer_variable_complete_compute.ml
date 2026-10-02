(* ========================================================================== *)
(* Compute-only one-verdict checker for a complete variable certificate.      *)
(*                                                                            *)
(* This unit deliberately contains only the executable definition and the    *)
(* equations supplied to Kernel.compute.  The general analytic and topology  *)
(* soundness proofs remain in the separately loadable soundness unit.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check_def =
  new_definition
   `candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check
        source_program tree_dim tokens encoded_jobs =
      Cexp_pair
        (candle_cv_fso_variable_raw_jobs_check source_program encoded_jobs)
        (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
          tree_dim tokens encoded_jobs (Cexp_num 0))`;;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_compute_eqs () =
  union candle_cv_fso_variable_raw_compute_eqs
    (union
      candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs
      [SPEC_ALL
        candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check_def]);;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_COMPLETE_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
