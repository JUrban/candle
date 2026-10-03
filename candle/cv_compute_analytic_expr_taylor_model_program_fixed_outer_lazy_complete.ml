(* ========================================================================== *)
(* One-verdict complete certificate checker with lazy polynomial completion. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The topology evaluator and raw certificate    *)
(* guard are unchanged.  For an authenticated compiler-produced source, the  *)
(* complete call is proved equal to the established checker, so its existing *)
(* root and source soundness theorems remain the authority.                   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_lazy_variable_raw.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_lazy_complete = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_lazy_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound;;

let candle_cv_q_dim_taylor_model_fixed_outer_lazy_complete_check_def =
  new_definition
   `candle_cv_q_dim_taylor_model_fixed_outer_lazy_complete_check
        source_program tree_dim tokens encoded_jobs =
      Cexp_pair
        (candle_cv_fsol_variable_raw_jobs_check source_program encoded_jobs)
        (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
          tree_dim tokens encoded_jobs (Cexp_num 0))`;;

let candle_cv_q_dim_taylor_model_fixed_outer_lazy_complete_compute_eqs () =
  union candle_cv_fsol_variable_raw_compute_eqs
    (union
      candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs
      [SPEC_ALL
        candle_cv_q_dim_taylor_model_fixed_outer_lazy_complete_check_def]);;

let candle_cv_q_dim_taylor_model_fixed_outer_lazy_complete_compiled_exact =
  prove
   (`!source_e tree_dim tokens encoded_jobs.
       candle_cv_q_dim_taylor_model_fixed_outer_lazy_complete_check
         (candle_cv_analytic_instruction_list
           (candle_analytic_compile source_e))
         tree_dim tokens encoded_jobs =
       candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check
         (candle_cv_analytic_instruction_list
           (candle_analytic_compile source_e))
         tree_dim tokens encoded_jobs`,
    REWRITE_TAC
      [candle_cv_q_dim_taylor_model_fixed_outer_lazy_complete_check_def;
       candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check_def;
       candle_cv_fsol_variable_raw_jobs_check_compiled_exact]);;

let candle_cv_q_dim_taylor_model_fixed_outer_lazy_complete_accept = prove
 (`!source_e (type_witness:real^N) tokens encoded_jobs encoded_root.
     candle_analytic_valid_dim (dimindex (:N)) source_e /\
     candle_cv_q_dim_taylor_model_fixed_outer_lazy_complete_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e))
       (Cexp_num (dimindex (:N)))
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
         tokens)
       encoded_jobs =
     Cexp_pair (Cexp_num 1)
       (Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 0)
           (Cexp_pair encoded_root (Cexp_num 0))))
     ==>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector
          (candle_cv_q_interval_list_decode encoded_root):real^N),
        (candle_q_box_upper_vector
          (candle_cv_q_interval_list_decode encoded_root):real^N))`,
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_fixed_outer_lazy_complete_compiled_exact] THEN
  MATCH_ACCEPT_TAC
    candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_accept);;

print_endline
  "CANDLE_CV_FIXED_OUTER_LAZY_COMPLETE_OK DEVELOPMENT_NON_RELEASE";;

end;;
