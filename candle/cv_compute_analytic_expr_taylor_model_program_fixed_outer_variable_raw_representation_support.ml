(* ========================================================================== *)
(* Separately loadable representation consequence for raw accepted jobs.      *)
(*                                                                            *)
(* Keeping this theorem in a small support unit lets a lean checkpoint prove  *)
(* and load it after the expensive numerical computation.                     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_representation_support = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;

let candle_cv_fso_variable_raw_jobs_check_representation_accept = prove
 (`!encoded source_e.
     candle_cv_fso_variable_raw_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e)) encoded = Cexp_num 1
     ==>
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
       (candle_cv_fso_variable_jobs_decode encoded) = encoded`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_fso_variable_raw_jobs_check_correct;candle_cv_bool_def] THEN
  COND_CASES_TAC THENL
   [ASM_MESON_TAC[];
    REWRITE_TAC[injectivity "cval"] THEN CONV_TAC NUM_REDUCE_CONV]);;

end;;
