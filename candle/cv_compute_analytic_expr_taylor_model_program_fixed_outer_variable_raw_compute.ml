(* Kernel.compute characteristic equations for canonical raw batches. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;

let candle_cv_lc_num_canonical_compute = prove
 (`!encoded.
     candle_cv_lc_num_canonical encoded =
     Cexp_if (Cexp_ispair encoded) (Cexp_num 0) encoded`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_lc_num_canonical_def;cexp_ispair_def;cexp_if_def]);;

let candle_cv_lc_z_canonical_compute = prove
 (`!encoded.
     candle_cv_lc_z_canonical encoded =
     Cexp_if (Cexp_ispair encoded)
       (Cexp_pair (candle_cv_lc_num_canonical (Cexp_fst encoded))
         (candle_cv_lc_num_canonical (Cexp_snd encoded)))
       (Cexp_pair (Cexp_num 0) (Cexp_num 0))`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_lc_z_canonical_def;cexp_ispair_def;cexp_if_def;
     cexp_fst_def;cexp_snd_def]);;

let candle_cv_q_canonical_compute = prove
 (`!encoded.
     candle_cv_q_canonical encoded =
     Cexp_if (Cexp_ispair encoded)
       (Cexp_pair (candle_cv_lc_z_canonical (Cexp_fst encoded))
         (candle_cv_lc_num_canonical (Cexp_snd encoded)))
       (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0))`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_canonical_def;cexp_ispair_def;cexp_if_def;
     cexp_fst_def;cexp_snd_def]);;

let candle_cv_q_interval_canonical_compute = prove
 (`!encoded.
     candle_cv_q_interval_canonical encoded =
     Cexp_if (Cexp_ispair encoded)
       (Cexp_pair (candle_cv_q_canonical (Cexp_fst encoded))
         (candle_cv_q_canonical (Cexp_snd encoded)))
       (Cexp_pair
         (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0))
         (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0)))`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_interval_canonical_def;cexp_ispair_def;cexp_if_def;
     cexp_fst_def;cexp_snd_def]);;

let candle_cv_q_interval_list_canonical_compute = prove
 (`!encoded.
     candle_cv_q_interval_list_canonical encoded =
     Cexp_if (Cexp_ispair encoded)
       (Cexp_pair
         (candle_cv_q_interval_canonical (Cexp_fst encoded))
         (candle_cv_q_interval_list_canonical (Cexp_snd encoded)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_interval_list_canonical_def;cexp_ispair_def;cexp_if_def;
     cexp_fst_def;cexp_snd_def]);;

let candle_cv_fso_variable_jobs_canonical_compute = prove
 (`!encoded.
     candle_cv_fso_variable_jobs_canonical encoded =
     Cexp_if (Cexp_ispair encoded)
       (Cexp_pair
         (candle_cv_fso_variable_job_canonical (Cexp_fst encoded))
         (candle_cv_fso_variable_jobs_canonical (Cexp_snd encoded)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fso_variable_jobs_canonical_def;cexp_ispair_def;cexp_if_def;
     cexp_fst_def;cexp_snd_def]);;

let candle_cv_fso_variable_raw_compute_eqs =
  union candle_cv_fso_variable_compute_eqs
    (map SPEC_ALL
      [candle_cv_lc_num_canonical_compute;
       candle_cv_lc_z_canonical_compute;
       candle_cv_q_canonical_compute;
       candle_cv_q_interval_canonical_compute;
       candle_cv_q_interval_list_canonical_compute;
       candle_cv_fso_variable_jobs_canonical_compute;
       candle_cv_fso_variable_job_canonical_def;
       candle_cv_fso_variable_raw_jobs_check_def]);;

end;;
