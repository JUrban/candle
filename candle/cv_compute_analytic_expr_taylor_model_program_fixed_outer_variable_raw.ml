(* ========================================================================== *)
(* Canonical raw-data boundary for variable-certificate Taylor batches.      *)
(*                                                                            *)
(* Certificate jobs arrive as cval data.  The executable canonicalizer below *)
(* accepts exactly the image of the existing logical encoder.  Its general   *)
(* decoder theorem lets the numerical checker authenticate a large raw batch *)
(* with one computed verdict, without constructing a host-side theorem for   *)
(* every rational endpoint and list constructor.                             *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_batch.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;

(* Canonical cval representations of the nested exact-rational data. *)
let candle_cv_lc_num_canonical_def = define
 `(candle_cv_lc_num_canonical (Cexp_num n) = Cexp_num n) /\
  (candle_cv_lc_num_canonical (Cexp_pair x y) = Cexp_num 0)`;;

let candle_cv_lc_z_canonical_def = define
 `(candle_cv_lc_z_canonical (Cexp_num n) =
     Cexp_pair (Cexp_num 0) (Cexp_num 0)) /\
  (candle_cv_lc_z_canonical (Cexp_pair x y) =
     Cexp_pair (candle_cv_lc_num_canonical x)
       (candle_cv_lc_num_canonical y))`;;

let candle_cv_q_canonical_def = define
 `(candle_cv_q_canonical (Cexp_num n) =
     Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0)) /\
  (candle_cv_q_canonical (Cexp_pair z d) =
     Cexp_pair (candle_cv_lc_z_canonical z)
       (candle_cv_lc_num_canonical d))`;;

let candle_cv_q_interval_canonical_def = define
 `(candle_cv_q_interval_canonical (Cexp_num n) =
     Cexp_pair
       (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0))
       (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0))) /\
  (candle_cv_q_interval_canonical (Cexp_pair lo hi) =
     Cexp_pair (candle_cv_q_canonical lo) (candle_cv_q_canonical hi))`;;

let candle_cv_q_interval_list_canonical_def = define
 `(candle_cv_q_interval_list_canonical (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_interval_list_canonical (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_interval_canonical h)
       (candle_cv_q_interval_list_canonical t))`;;

(* A decoded logical job is (whole-box hints,(center hints,box)). *)
let candle_cv_fso_variable_job_decode_def = new_definition
 `candle_cv_fso_variable_job_decode encoded =
    (candle_cv_q_interval_list_decode (Cexp_fst encoded),
     (candle_cv_q_interval_list_decode (Cexp_fst (Cexp_snd encoded)),
      candle_cv_q_interval_list_decode (Cexp_snd (Cexp_snd encoded))))`;;

let candle_cv_fso_variable_jobs_decode_def = define
 `(candle_cv_fso_variable_jobs_decode (Cexp_num n) =
     ([]:((((num#num)#num)#((num#num)#num))list#
          ((((num#num)#num)#((num#num)#num))list#
           (((num#num)#num)#((num#num)#num))list))list)) /\
  (candle_cv_fso_variable_jobs_decode (Cexp_pair job jobs) =
     CONS (candle_cv_fso_variable_job_decode job)
       (candle_cv_fso_variable_jobs_decode jobs))`;;

let candle_cv_fso_variable_job_canonical_def = new_definition
 `candle_cv_fso_variable_job_canonical encoded =
    Cexp_pair
      (candle_cv_q_interval_list_canonical (Cexp_fst encoded))
      (Cexp_pair
        (candle_cv_q_interval_list_canonical (Cexp_fst (Cexp_snd encoded)))
        (candle_cv_q_interval_list_canonical (Cexp_snd (Cexp_snd encoded))))`;;

let candle_cv_fso_variable_jobs_canonical_def = define
 `(candle_cv_fso_variable_jobs_canonical (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fso_variable_jobs_canonical (Cexp_pair job jobs) =
     Cexp_pair (candle_cv_fso_variable_job_canonical job)
       (candle_cv_fso_variable_jobs_canonical jobs))`;;

let candle_cv_fso_variable_raw_jobs_check_def = new_definition
 `candle_cv_fso_variable_raw_jobs_check source_program encoded_jobs =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_fso_variable_jobs_check source_program encoded_jobs)`;;

(* The canonicalizer is exactly encode after decode, for every raw cval. *)
let _ = print_endline "CANDLE_VARIABLE_RAW_PROOF lc-num";;
let candle_cv_lc_num_canonical_decode = prove
 (`!encoded.
     candle_cv_lc_num_canonical encoded =
     Cexp_num (candle_cv_lc_num_decode encoded)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_lc_num_canonical_def;candle_cv_lc_num_decode_def]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_PROOF lc-z";;
let candle_cv_lc_z_canonical_decode = prove
 (`!encoded.
     candle_cv_lc_z_canonical encoded =
     candle_cv_lc_z (candle_cv_lc_z_decode encoded)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_lc_z_canonical_def;candle_cv_lc_z_decode_def;
     candle_cv_lc_z_def;candle_cv_lc_num_canonical_decode;FST;SND]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_PROOF q";;
let candle_cv_q_canonical_decode = prove
 (`!encoded.
     candle_cv_q_canonical encoded =
     candle_cv_q (candle_cv_q_decode encoded)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_canonical_def;candle_cv_q_decode_def;candle_cv_q_def;
     candle_cv_lc_z_canonical_decode;candle_cv_lc_num_canonical_decode;
     candle_cv_lc_z_def;FST;SND]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_PROOF interval";;
let candle_cv_q_interval_canonical_decode = prove
 (`!encoded.
     candle_cv_q_interval_canonical encoded =
     candle_cv_q_interval (candle_cv_q_interval_decode encoded)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_q_interval_canonical_def;candle_cv_q_interval_decode_def;
     candle_cv_q_interval_def;candle_cv_q_canonical_decode;
     candle_cv_q_def;candle_cv_lc_z_def;FST;SND]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_PROOF interval-list";;
let candle_cv_q_interval_list_canonical_decode = prove
 (`!encoded.
     candle_cv_q_interval_list_canonical encoded =
     candle_cv_q_interval_list
       (candle_cv_q_interval_list_decode encoded)`,
  MATCH_MP_TAC cval_INDUCT THEN CONJ_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_q_interval_list_canonical_def;
       candle_cv_q_interval_list_decode_def;candle_cv_q_interval_list_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC
      [candle_cv_q_interval_list_canonical_def;
       candle_cv_q_interval_list_decode_def;candle_cv_q_interval_list_def;
       candle_cv_q_interval_canonical_decode]]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_PROOF job";;
let candle_cv_fso_variable_job_canonical_decode = prove
 (`!encoded.
     candle_cv_fso_variable_job_canonical encoded =
     Cexp_pair
       (candle_cv_q_interval_list
         (FST (candle_cv_fso_variable_job_decode encoded)))
       (Cexp_pair
         (candle_cv_q_interval_list
           (FST (SND (candle_cv_fso_variable_job_decode encoded))))
         (candle_cv_q_interval_list
           (SND (SND (candle_cv_fso_variable_job_decode encoded)))))`,
  REWRITE_TAC
    [candle_cv_fso_variable_job_canonical_def;
     candle_cv_fso_variable_job_decode_def;
     candle_cv_q_interval_list_canonical_decode;FST;SND]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_PROOF jobs";;
let candle_cv_fso_variable_jobs_canonical_decode = prove
 (`!encoded.
     candle_cv_fso_variable_jobs_canonical encoded =
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
       (candle_cv_fso_variable_jobs_decode encoded)`,
  MATCH_MP_TAC cval_INDUCT THEN CONJ_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_fso_variable_jobs_canonical_def;
       candle_cv_fso_variable_jobs_decode_def;
       candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC
      [candle_cv_fso_variable_jobs_canonical_def;
       candle_cv_fso_variable_jobs_decode_def;
       candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
       candle_cv_fso_variable_job_canonical_decode]]);;

let candle_cv_fso_variable_job_decode_roundtrip = prove
 (`!job.
     candle_cv_fso_variable_job_decode
       (Cexp_pair
         (candle_cv_q_interval_list (FST job))
         (Cexp_pair
           (candle_cv_q_interval_list (FST (SND job)))
           (candle_cv_q_interval_list (SND (SND job))))) = job`,
  REWRITE_TAC
    [candle_cv_fso_variable_job_decode_def;cexp_fst_def;cexp_snd_def;
     candle_cv_q_interval_list_roundtrip;PAIR_EQ;FST;SND]);;

let candle_cv_fso_variable_jobs_decode_roundtrip = prove
 (`!jobs.
     candle_cv_fso_variable_jobs_decode
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs) = jobs`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_fso_variable_jobs_decode_def;
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
     candle_cv_fso_variable_job_decode_roundtrip]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_PROOF canonical-equal";;
let candle_cv_fso_variable_jobs_canonical_equal = prove
 (`!encoded.
     Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded) encoded =
     candle_cv_bool
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
          (candle_cv_fso_variable_jobs_decode encoded) = encoded)`,
  REWRITE_TAC
    [candle_cv_fso_variable_jobs_canonical_decode;
     cexp_eq_def;candle_cv_bool_def]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_PROOF checker-correct";;
let candle_cv_fso_variable_raw_jobs_check_correct = prove
 (`!encoded source_e.
     candle_cv_fso_variable_raw_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e)) encoded =
     candle_cv_bool
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
          (candle_cv_fso_variable_jobs_decode encoded) = encoded /\
        candle_q_dim_taylor_model_fixed_outer_variable_jobs_numerical_accept
          source_e (candle_cv_fso_variable_jobs_decode encoded))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_fso_variable_raw_jobs_check_def;
     candle_cv_fso_variable_jobs_canonical_equal] THEN
  ASM_CASES_TAC
    `candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
       (candle_cv_fso_variable_jobs_decode encoded) = encoded` THENL
   [FIRST_ASSUM
      (fun representation ->
        ASSUME_TAC
          (REWRITE_RULE
            [candle_cv_fso_variable_jobs_check_correct]
            (AP_TERM
              `\jobs:cval.
                 candle_cv_fso_variable_jobs_check
                   (candle_cv_analytic_instruction_list
                     (candle_analytic_compile source_e)) jobs`
              (SYM representation)))) THEN
    ASM_REWRITE_TAC
      [candle_cv_bool_and_def;candle_cv_bool_def;cexp_if_def];
    ASM_REWRITE_TAC
      [candle_cv_bool_and_def;candle_cv_bool_def;cexp_if_def]]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_PROOF checker-accept";;
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

let candle_cv_fso_variable_raw_jobs_check_accept = prove
 (`!encoded source_e.
     candle_cv_fso_variable_raw_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e)) encoded = Cexp_num 1
     ==>
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
       source_e (candle_cv_fso_variable_jobs_decode encoded)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_fso_variable_raw_jobs_check_correct;candle_cv_bool_def] THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[injectivity "cval"] THEN CONV_TAC NUM_REDUCE_CONV]);;

let _ = print_endline "CANDLE_VARIABLE_RAW_PROOF complete";;

end;;
