(* ========================================================================== *)
(* Data-only fixed-outer verdict vectors for untrusted policy discovery.     *)
(*                                                                            *)
(* The proof-producing replay remains authoritative.  This evaluator exposes *)
(* individual job verdicts and batches independent outer-box tasks into one   *)
(* Kernel.compute call so policy discovery does not rebuild source programs.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_flags = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;

let candle_cv_fso_stable_jobs_flags_def = define
 `(candle_cv_fso_stable_jobs_flags
      source_program box_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fso_stable_jobs_flags
      source_program box_program (Cexp_pair job jobs) =
     Cexp_pair
       (Cexp_if
         (candle_cv_analytic_program_sqrt_data_exact
           (Cexp_fst job) source_program)
         (let center_patched =
            candle_cv_analytic_program_patch_sqrt
              (Cexp_fst job) source_program in
          Cexp_fst
            (candle_cv_fso_certified_check
              (Cexp_snd center_patched) box_program (Cexp_snd job)))
         (Cexp_num 0))
       (candle_cv_fso_stable_jobs_flags
         source_program box_program jobs))`;;

let candle_cv_fso_stable_jobs_flags_compute = prove
 (`!source_program box_program jobs.
     candle_cv_fso_stable_jobs_flags source_program box_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (Cexp_if
           (candle_cv_analytic_program_sqrt_data_exact
             (Cexp_fst (Cexp_fst jobs)) source_program)
           (let center_patched =
              candle_cv_analytic_program_patch_sqrt
                (Cexp_fst (Cexp_fst jobs)) source_program in
            Cexp_fst
              (candle_cv_fso_certified_check
                (Cexp_snd center_patched) box_program
                (Cexp_snd (Cexp_fst jobs))))
           (Cexp_num 0))
         (candle_cv_fso_stable_jobs_flags
           source_program box_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fso_stable_jobs_flags_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fso_stable_batch_flags_def = new_definition
 `candle_cv_fso_stable_batch_flags source_program box_intervals jobs =
    Cexp_if
      (candle_cv_analytic_program_sqrt_data_exact
        box_intervals source_program)
      (let box_patched =
         candle_cv_analytic_program_patch_sqrt
           box_intervals source_program in
       candle_cv_fso_stable_jobs_flags
         source_program (Cexp_snd box_patched) jobs)
      (Cexp_num 0)`;;

let candle_cv_fso_stable_task_flags_def = define
 `(candle_cv_fso_stable_task_flags
      source_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fso_stable_task_flags
      source_program (Cexp_pair task tasks) =
     Cexp_pair
       (candle_cv_fso_stable_batch_flags
         source_program (Cexp_fst task) (Cexp_snd task))
       (candle_cv_fso_stable_task_flags source_program tasks))`;;

let candle_cv_fso_stable_task_flags_compute = prove
 (`!source_program tasks.
     candle_cv_fso_stable_task_flags source_program tasks =
     Cexp_if (Cexp_ispair tasks)
       (Cexp_pair
         (candle_cv_fso_stable_batch_flags source_program
           (Cexp_fst (Cexp_fst tasks)) (Cexp_snd (Cexp_fst tasks)))
         (candle_cv_fso_stable_task_flags
           source_program (Cexp_snd tasks)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `tasks:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fso_stable_task_flags_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fso_flags_compute_eqs =
  map (REWRITE_RULE[LET_END_DEF])
    (union candle_cv_fso_compute_eqs
      [SPEC_ALL candle_cv_fso_stable_jobs_flags_compute;
       SPEC_ALL candle_cv_fso_stable_batch_flags_def;
       SPEC_ALL candle_cv_fso_stable_task_flags_compute]);;

end;;
