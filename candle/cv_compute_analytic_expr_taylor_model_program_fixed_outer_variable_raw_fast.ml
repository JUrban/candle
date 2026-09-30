(* Direct well-formedness checking for canonical raw variable batches.       *)
(* The predicate is proved equivalent to rebuild-and-compare canonicality,  *)
(* but does not allocate a duplicate certificate during Kernel.compute.      *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_fast = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;

let candle_cv_lc_num_well_formed_def = new_definition
 `candle_cv_lc_num_well_formed encoded =
    Cexp_if (Cexp_ispair encoded) (Cexp_num 0) (Cexp_num 1)`;;

let candle_cv_lc_z_well_formed_def = new_definition
 `candle_cv_lc_z_well_formed encoded =
    Cexp_if (Cexp_ispair encoded)
      (candle_cv_bool_and
        (candle_cv_lc_num_well_formed (Cexp_fst encoded))
        (candle_cv_lc_num_well_formed (Cexp_snd encoded)))
      (Cexp_num 0)`;;

let candle_cv_q_well_formed_def = new_definition
 `candle_cv_q_well_formed encoded =
    Cexp_if (Cexp_ispair encoded)
      (candle_cv_bool_and
        (candle_cv_lc_z_well_formed (Cexp_fst encoded))
        (candle_cv_lc_num_well_formed (Cexp_snd encoded)))
      (Cexp_num 0)`;;

let candle_cv_q_interval_well_formed_def = new_definition
 `candle_cv_q_interval_well_formed encoded =
    Cexp_if (Cexp_ispair encoded)
      (candle_cv_bool_and
        (candle_cv_q_well_formed (Cexp_fst encoded))
        (candle_cv_q_well_formed (Cexp_snd encoded)))
      (Cexp_num 0)`;;

let candle_cv_q_interval_list_well_formed_def = define
 `(candle_cv_q_interval_list_well_formed (Cexp_num n) =
     Cexp_eq (Cexp_num n) (Cexp_num 0)) /\
  (candle_cv_q_interval_list_well_formed (Cexp_pair h t) =
     candle_cv_bool_and
       (candle_cv_q_interval_well_formed h)
       (candle_cv_q_interval_list_well_formed t))`;;

let candle_cv_fso_variable_job_well_formed_def = new_definition
 `candle_cv_fso_variable_job_well_formed encoded =
    Cexp_if (Cexp_ispair encoded)
      (Cexp_if (Cexp_ispair (Cexp_snd encoded))
        (candle_cv_bool_and
          (candle_cv_q_interval_list_well_formed (Cexp_fst encoded))
          (candle_cv_bool_and
            (candle_cv_q_interval_list_well_formed
              (Cexp_fst (Cexp_snd encoded)))
            (candle_cv_q_interval_list_well_formed
              (Cexp_snd (Cexp_snd encoded)))))
        (Cexp_num 0))
      (Cexp_num 0)`;;

let candle_cv_fso_variable_jobs_well_formed_def = define
 `(candle_cv_fso_variable_jobs_well_formed (Cexp_num n) =
     Cexp_eq (Cexp_num n) (Cexp_num 0)) /\
  (candle_cv_fso_variable_jobs_well_formed (Cexp_pair job jobs) =
     candle_cv_bool_and
       (candle_cv_fso_variable_job_well_formed job)
       (candle_cv_fso_variable_jobs_well_formed jobs))`;;

let candle_cv_fso_variable_raw_jobs_check_fast_def = new_definition
 `candle_cv_fso_variable_raw_jobs_check_fast source_program encoded_jobs =
    candle_cv_bool_and
      (candle_cv_fso_variable_jobs_well_formed encoded_jobs)
      (candle_cv_fso_variable_jobs_check source_program encoded_jobs)`;;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF equal";;
let candle_cv_equal_correct = prove
 (`!left right.
     Cexp_eq left right = candle_cv_bool (left = right)`,
  REWRITE_TAC[cexp_eq_def;candle_cv_bool_def]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF num";;
let candle_cv_lc_num_well_formed_canonical = prove
 (`!encoded.
     candle_cv_lc_num_well_formed encoded =
     Cexp_eq (candle_cv_lc_num_canonical encoded) encoded`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_lc_num_well_formed_def;candle_cv_lc_num_canonical_def;
     cexp_ispair_def;cexp_if_def;cexp_eq_def;injectivity "cval";
     distinctness "cval";ONE]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF z";;
let candle_cv_lc_z_well_formed_canonical = prove
 (`!encoded.
     candle_cv_lc_z_well_formed encoded =
     Cexp_eq (candle_cv_lc_z_canonical encoded) encoded`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_lc_z_well_formed_def;candle_cv_lc_z_canonical_def;
     cexp_ispair_def;cexp_if_def;cexp_fst_def;cexp_snd_def;
     candle_cv_lc_num_well_formed_canonical;candle_cv_equal_correct;
     candle_cv_bool_and_correct;
     injectivity "cval";distinctness "cval";ONE] THEN
  REWRITE_TAC[candle_cv_bool_and_correct;candle_cv_bool_def]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF q";;
let candle_cv_q_well_formed_canonical = prove
 (`!encoded.
     candle_cv_q_well_formed encoded =
     Cexp_eq (candle_cv_q_canonical encoded) encoded`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_well_formed_def;candle_cv_q_canonical_def;
     cexp_ispair_def;cexp_if_def;cexp_fst_def;cexp_snd_def;
     candle_cv_lc_z_well_formed_canonical;
     candle_cv_lc_num_well_formed_canonical;candle_cv_equal_correct;
     candle_cv_bool_and_correct;
     injectivity "cval";distinctness "cval";ONE] THEN
  REWRITE_TAC[candle_cv_bool_and_correct;candle_cv_bool_def]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF interval";;
let candle_cv_q_interval_well_formed_canonical = prove
 (`!encoded.
     candle_cv_q_interval_well_formed encoded =
     Cexp_eq (candle_cv_q_interval_canonical encoded) encoded`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_interval_well_formed_def;
     candle_cv_q_interval_canonical_def;
     cexp_ispair_def;cexp_if_def;cexp_fst_def;cexp_snd_def;
     candle_cv_q_well_formed_canonical;candle_cv_equal_correct;
     candle_cv_bool_and_correct;
     injectivity "cval";distinctness "cval";ONE] THEN
  REWRITE_TAC[candle_cv_bool_and_correct;candle_cv_bool_def]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF interval-list";;
let candle_cv_q_interval_list_well_formed_canonical = prove
 (`!encoded.
     candle_cv_q_interval_list_well_formed encoded =
     Cexp_eq (candle_cv_q_interval_list_canonical encoded) encoded`,
  MATCH_MP_TAC cval_INDUCT THEN CONJ_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_q_interval_list_well_formed_def;
       candle_cv_q_interval_list_canonical_def;cexp_eq_def;EQ_SYM_EQ];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC
      [candle_cv_q_interval_list_well_formed_def;
       candle_cv_q_interval_list_canonical_def;
       candle_cv_q_interval_well_formed_canonical;
       candle_cv_equal_correct;candle_cv_bool_and_correct;
       injectivity "cval";ONE] THEN
    REWRITE_TAC[candle_cv_bool_and_correct;candle_cv_bool_def]]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF job";;
let candle_cv_fso_variable_job_well_formed_canonical = prove
 (`!encoded.
     candle_cv_fso_variable_job_well_formed encoded =
     Cexp_eq (candle_cv_fso_variable_job_canonical encoded) encoded`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THENL
   [REWRITE_TAC
      [candle_cv_fso_variable_job_well_formed_def;
       candle_cv_fso_variable_job_canonical_def;
       candle_cv_q_interval_list_canonical_def;
       cexp_ispair_def;cexp_if_def;cexp_fst_def;cexp_snd_def;cexp_eq_def;
       distinctness "cval"];
    STRUCT_CASES_TAC (SPEC `a1:cval` (cases "cval")) THEN
    REWRITE_TAC
      [candle_cv_fso_variable_job_well_formed_def;
       candle_cv_fso_variable_job_canonical_def;
       cexp_ispair_def;cexp_if_def;cexp_fst_def;cexp_snd_def;
       candle_cv_q_interval_list_well_formed_canonical;
       candle_cv_equal_correct;candle_cv_bool_and_correct;
       injectivity "cval";distinctness "cval";ONE] THEN
    REWRITE_TAC[candle_cv_bool_and_correct;candle_cv_bool_def]]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF jobs";;
let candle_cv_fso_variable_jobs_well_formed_canonical = prove
 (`!encoded.
     candle_cv_fso_variable_jobs_well_formed encoded =
     Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded) encoded`,
  MATCH_MP_TAC cval_INDUCT THEN CONJ_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_fso_variable_jobs_well_formed_def;
       candle_cv_fso_variable_jobs_canonical_def;cexp_eq_def;EQ_SYM_EQ];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC
      [candle_cv_fso_variable_jobs_well_formed_def;
       candle_cv_fso_variable_jobs_canonical_def;
       candle_cv_fso_variable_job_well_formed_canonical;
       candle_cv_equal_correct;candle_cv_bool_and_correct;
       injectivity "cval";ONE] THEN
    REWRITE_TAC[candle_cv_bool_and_correct;candle_cv_bool_def]]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF checker-eq";;
let candle_cv_fso_variable_raw_jobs_check_fast_eq = prove
 (`!source_program encoded_jobs.
     candle_cv_fso_variable_raw_jobs_check_fast source_program encoded_jobs =
     candle_cv_fso_variable_raw_jobs_check source_program encoded_jobs`,
  REWRITE_TAC
    [candle_cv_fso_variable_raw_jobs_check_fast_def;
     candle_cv_fso_variable_raw_jobs_check_def;
     candle_cv_fso_variable_jobs_well_formed_canonical]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF checker-correct";;
let candle_cv_fso_variable_raw_jobs_check_fast_correct = prove
 (`!encoded source_e.
     candle_cv_fso_variable_raw_jobs_check_fast
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e)) encoded =
     candle_cv_bool
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
          (candle_cv_fso_variable_jobs_decode encoded) = encoded /\
        candle_q_dim_taylor_model_fixed_outer_variable_jobs_numerical_accept
          source_e (candle_cv_fso_variable_jobs_decode encoded))`,
  REWRITE_TAC
    [candle_cv_fso_variable_raw_jobs_check_fast_eq;
     candle_cv_fso_variable_raw_jobs_check_correct]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF checker-accept";;
let candle_cv_fso_variable_raw_jobs_check_fast_accept = prove
 (`!encoded source_e.
     candle_cv_fso_variable_raw_jobs_check_fast
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e)) encoded = Cexp_num 1
     ==>
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
       source_e (candle_cv_fso_variable_jobs_decode encoded)`,
  REWRITE_TAC
    [candle_cv_fso_variable_raw_jobs_check_fast_eq] THEN
  MESON_TAC[candle_cv_fso_variable_raw_jobs_check_accept]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF interval-list-compute";;
let candle_cv_q_interval_list_well_formed_compute = prove
 (`!encoded.
     candle_cv_q_interval_list_well_formed encoded =
     Cexp_if (Cexp_ispair encoded)
       (candle_cv_bool_and
         (candle_cv_q_interval_well_formed (Cexp_fst encoded))
         (candle_cv_q_interval_list_well_formed (Cexp_snd encoded)))
       (Cexp_eq encoded (Cexp_num 0))`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_interval_list_well_formed_def;
     cexp_ispair_def;cexp_if_def;cexp_fst_def;cexp_snd_def]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF jobs-compute";;
let candle_cv_fso_variable_jobs_well_formed_compute = prove
 (`!encoded.
     candle_cv_fso_variable_jobs_well_formed encoded =
     Cexp_if (Cexp_ispair encoded)
       (candle_cv_bool_and
         (candle_cv_fso_variable_job_well_formed (Cexp_fst encoded))
         (candle_cv_fso_variable_jobs_well_formed (Cexp_snd encoded)))
       (Cexp_eq encoded (Cexp_num 0))`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fso_variable_jobs_well_formed_def;
     cexp_ispair_def;cexp_if_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_fso_variable_raw_fast_compute_eqs =
  union candle_cv_fso_variable_compute_eqs
    (map SPEC_ALL
      [candle_cv_lc_num_well_formed_def;
       candle_cv_lc_z_well_formed_def;
       candle_cv_q_well_formed_def;
       candle_cv_q_interval_well_formed_def;
       candle_cv_q_interval_list_well_formed_compute;
       candle_cv_fso_variable_job_well_formed_def;
       candle_cv_fso_variable_jobs_well_formed_compute;
       candle_cv_fso_variable_raw_jobs_check_fast_def]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_FAST_PROOF complete";;

end;;
