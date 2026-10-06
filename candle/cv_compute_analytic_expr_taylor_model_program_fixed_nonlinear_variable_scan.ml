(* ========================================================================== *)
(* Untrusted per-job discovery scan for fixed-nonlinear certificates.         *)
(*                                                                            *)
(* This utility reports every numerical verdict instead of stopping at the   *)
(* first rejection.  It is used only to choose subdivision work.  Final      *)
(* theorem production still goes through the proved complete checker, so an  *)
(* incorrect discovery result can only make that later checker reject.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_scan.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_scan = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_scan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;

let candle_cv_fsn_variable_jobs_scan_def = define
 `(candle_cv_fsn_variable_jobs_scan source_program (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fsn_variable_jobs_scan source_program
      (Cexp_pair job jobs) =
     Cexp_pair
       (candle_cv_fsn_variable_raw_jobs_check source_program
         (Cexp_pair job (Cexp_num 0)))
       (candle_cv_fsn_variable_jobs_scan source_program jobs))`;;

let candle_cv_fsn_variable_jobs_scan_compute = prove
 (`!source_program jobs.
     candle_cv_fsn_variable_jobs_scan source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (candle_cv_fsn_variable_raw_jobs_check source_program
           (Cexp_pair (Cexp_fst jobs) (Cexp_num 0)))
         (candle_cv_fsn_variable_jobs_scan source_program
           (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fsn_variable_jobs_scan_def;
     cexp_ispair_def;cexp_if_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_fsn_variable_jobs_scan_compute_eqs =
  union candle_cv_fixed_nonlinear_compute_eqs
    [SPEC_ALL candle_cv_fsn_variable_jobs_scan_compute];;

let candle_q_dim_taylor_model_fixed_nonlinear_variable_scan_six
    label prepared cells =
  if cells = [] then 0,[]
  else
    let expected = length cells in
    candle_q_dim_analytic_jet_profile_event (label ^ "-encoding-begin");
    let encoded_jobs =
      candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
        cells in
    candle_q_dim_analytic_jet_profile_event (label ^ "-encoding-end");
    let call =
      list_mk_comb
        (`candle_cv_fsn_variable_jobs_scan`,
         [prepared.program_representation_term;encoded_jobs]) in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-begin");
    let theorem =
      candle_q_dim_analytic_jet_compute
        candle_cv_fsn_variable_jobs_scan_compute_eqs call in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-end");
    let count,failures =
      candle_cv_fso_variable_jobs_scan_decode label (rand (concl theorem)) in
    if count <> expected || hyp theorem <> [] ||
       not (aconv (lhand (concl theorem)) call) then
      failwith (label ^ ": fixed nonlinear scan validation failed");
    count,failures;;

print_endline
  "CANDLE_CV_FIXED_NONLINEAR_VARIABLE_SCAN_OK DEVELOPMENT_NON_RELEASE";;

end;;
