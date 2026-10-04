(* ========================================================================== *)
(* Untrusted per-job discovery scan for fixed-outer variable certificates.   *)
(*                                                                            *)
(* The scan reports the ordinary raw verdict for every encoded job instead  *)
(* of short-circuiting at the first rejection.  It is plan-discovery data    *)
(* only: final acceptance still goes through the proved compact checker.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_scan = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;

let candle_cv_fso_variable_jobs_scan_def = define
 `(candle_cv_fso_variable_jobs_scan source_program (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fso_variable_jobs_scan source_program
      (Cexp_pair job jobs) =
     Cexp_pair
       (candle_cv_fso_variable_raw_jobs_check source_program
         (Cexp_pair job (Cexp_num 0)))
       (candle_cv_fso_variable_jobs_scan source_program jobs))`;;

let candle_cv_fso_variable_jobs_scan_compute = prove
 (`!source_program jobs.
     candle_cv_fso_variable_jobs_scan source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (candle_cv_fso_variable_raw_jobs_check source_program
           (Cexp_pair (Cexp_fst jobs) (Cexp_num 0)))
         (candle_cv_fso_variable_jobs_scan source_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fso_variable_jobs_scan_def;cexp_ispair_def;cexp_if_def;
     cexp_fst_def;cexp_snd_def]);;

let candle_cv_fso_variable_jobs_scan_compute_eqs =
  union candle_cv_fso_variable_raw_compute_eqs
    [SPEC_ALL candle_cv_fso_variable_jobs_scan_compute];;

let candle_cv_fso_variable_jobs_scan_dest_pair context tm =
  match strip_comb tm with
  | constructor,[head;tail] when aconv constructor `Cexp_pair` -> head,tail
  | _ -> failwith (context ^ ": malformed result pair");;

let candle_cv_fso_variable_jobs_scan_decode context encoded =
  let rec decode index encoded =
    if aconv encoded `Cexp_num 0` then index,[]
    else
      let head,tail =
        candle_cv_fso_variable_jobs_scan_dest_pair context encoded in
      let after,failures = decode (index + 1) tail in
      if aconv head `Cexp_num 0` then after,index::failures
      else if aconv head `Cexp_num 1` then after,failures
      else failwith (context ^ ": malformed job verdict") in
  decode 0 encoded;;

let rec candle_cv_fso_variable_jobs_scan_indices_string = function
  | [] -> ""
  | [index] -> string_of_int index
  | index::remaining ->
      string_of_int index ^ "," ^
      candle_cv_fso_variable_jobs_scan_indices_string remaining;;

end;;
