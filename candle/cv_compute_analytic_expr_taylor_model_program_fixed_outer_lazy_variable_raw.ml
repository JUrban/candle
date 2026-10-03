(* ========================================================================== *)
(* Lazy fixed-outer evaluation at the authenticated raw batch boundary.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The raw certificate representation and its    *)
(* canonicality guard are unchanged.  Only the certified numerical leaf      *)
(* evaluator is replaced, and the replacement is proved equal to the         *)
(* established raw checker for every compiler-produced source program.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_lazy_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_lazy_variable_raw = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_certificate_patch_exact;;
open Candle_cv_analytic_expr_stable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_lazy;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_lazy_sound;;

let candle_cv_fsol_variable_jobs_check_def = define
 `(candle_cv_fsol_variable_jobs_check source_program (Cexp_num n) =
     Cexp_num 1) /\
  (candle_cv_fsol_variable_jobs_check source_program
      (Cexp_pair job jobs) =
     Cexp_if
       (candle_cv_analytic_program_sqrt_data_exact
         (Cexp_fst job) source_program)
       (let box_patched =
          candle_cv_analytic_program_patch_sqrt
            (Cexp_fst job) source_program in
        Cexp_if
          (candle_cv_analytic_program_sqrt_data_exact
            (Cexp_fst (Cexp_snd job)) source_program)
          (let center_patched =
             candle_cv_analytic_program_patch_sqrt
               (Cexp_fst (Cexp_snd job)) source_program in
           Cexp_if
             (Cexp_fst
               (candle_cv_fsol_certified_check
                 (Cexp_snd center_patched) (Cexp_snd box_patched)
                 (Cexp_snd (Cexp_snd job))))
             (candle_cv_fsol_variable_jobs_check source_program jobs)
             (Cexp_num 0))
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_fsol_variable_jobs_check_compute = prove
 (`!source_program jobs.
     candle_cv_fsol_variable_jobs_check source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if
         (candle_cv_analytic_program_sqrt_data_exact
           (Cexp_fst (Cexp_fst jobs)) source_program)
         (let box_patched =
            candle_cv_analytic_program_patch_sqrt
              (Cexp_fst (Cexp_fst jobs)) source_program in
          Cexp_if
            (candle_cv_analytic_program_sqrt_data_exact
              (Cexp_fst (Cexp_snd (Cexp_fst jobs))) source_program)
            (let center_patched =
               candle_cv_analytic_program_patch_sqrt
                 (Cexp_fst (Cexp_snd (Cexp_fst jobs))) source_program in
             Cexp_if
               (Cexp_fst
                 (candle_cv_fsol_certified_check
                   (Cexp_snd center_patched) (Cexp_snd box_patched)
                   (Cexp_snd (Cexp_snd (Cexp_fst jobs)))))
               (candle_cv_fsol_variable_jobs_check
                 source_program (Cexp_snd jobs))
               (Cexp_num 0))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsol_variable_jobs_check_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsol_variable_raw_jobs_check_def = new_definition
 `candle_cv_fsol_variable_raw_jobs_check source_program encoded_jobs =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_fsol_variable_jobs_check source_program encoded_jobs)`;;

let candle_cv_fsol_variable_jobs_check_correct = prove
 (`!jobs source_e.
     candle_cv_fsol_variable_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e))
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs) =
     Cexp_num
       (if candle_q_dim_taylor_model_fixed_outer_variable_jobs_numerical_accept
             source_e jobs
        then SUC 0 else 0)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
     candle_cv_fsol_variable_jobs_check_def;
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_numerical_accept_def;
     candle_cv_analytic_program_sqrt_data_exact_correct;
     candle_cv_analytic_compile_patch_sqrt_correct;
     candle_cv_fsol_certified_check_correct;
     cexp_fst_def; cexp_snd_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[candle_cv_fsa_batch_bool_and; CONJ_ASSOC;
              ARITH_RULE `1 = SUC 0`]);;

let candle_cv_fsol_variable_raw_jobs_check_correct = prove
 (`!encoded source_e.
     candle_cv_fsol_variable_raw_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e)) encoded =
     candle_cv_bool
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
          (candle_cv_fso_variable_jobs_decode encoded) = encoded /\
        candle_q_dim_taylor_model_fixed_outer_variable_jobs_numerical_accept
          source_e (candle_cv_fso_variable_jobs_decode encoded))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_fsol_variable_raw_jobs_check_def;
     candle_cv_fso_variable_jobs_canonical_equal] THEN
  ASM_CASES_TAC
    `candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
       (candle_cv_fso_variable_jobs_decode encoded) = encoded` THENL
   [FIRST_ASSUM
      (fun representation ->
        ASSUME_TAC
          (REWRITE_RULE
            [candle_cv_fsol_variable_jobs_check_correct]
            (AP_TERM
              `\jobs:cval.
                 candle_cv_fsol_variable_jobs_check
                   (candle_cv_analytic_instruction_list
                     (candle_analytic_compile source_e)) jobs`
              (SYM representation)))) THEN
    ASM_REWRITE_TAC
      [candle_cv_bool_and_def;candle_cv_bool_def;cexp_if_def];
    ASM_REWRITE_TAC
      [candle_cv_bool_and_def;candle_cv_bool_def;cexp_if_def]]);;

let candle_cv_fsol_variable_raw_jobs_check_compiled_exact = prove
 (`!encoded source_e.
     candle_cv_fsol_variable_raw_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e)) encoded =
     candle_cv_fso_variable_raw_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e)) encoded`,
  REWRITE_TAC[candle_cv_fsol_variable_raw_jobs_check_correct;
              candle_cv_fso_variable_raw_jobs_check_correct]);;

let candle_cv_fsol_variable_raw_compute_eqs =
  map (REWRITE_RULE[LET_END_DEF])
    (union candle_cv_fso_variable_raw_compute_eqs
      (union candle_cv_fsol_compute_eqs
        (map SPEC_ALL
          [candle_cv_fsol_variable_jobs_check_compute;
           candle_cv_fsol_variable_raw_jobs_check_def])));;

print_endline
  "CANDLE_CV_FIXED_OUTER_LAZY_VARIABLE_RAW_OK DEVELOPMENT_NON_RELEASE";;

end;;
