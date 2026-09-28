(* ========================================================================== *)
(* Source-shape scheduling discriminator for the fixed-algebraic evaluator.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The established evaluator scans the complete  *)
(* remaining instruction suffix at every program step to decide whether the  *)
(* fixed representation may be retained.  This prototype computes the same  *)
(* Boolean schedule once from the authenticated stable source program and    *)
(* reuses it across all cells in a batch.  It has no theorem authority until  *)
(* the general equivalence and analytic bridge are proved.                    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_stable_batch.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_schedule = struct

open Candle_cv_analytic_expr_certificate_patch_compute;;
open Candle_cv_analytic_expr_certificate_patch_exact;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch;;
open Candle_cv_analytic_expr_stable_batch;;

(* Return [(suffix contains a nonlinear instruction), per-step flags].  The *)
(* flag stored for the current instruction is true exactly when its tail has *)
(* no nonlinear instruction, matching the established scheduler.             *)

let candle_cv_fsa_schedule_state_def = define
 `(candle_cv_fsa_schedule_state (Cexp_num n) =
     Cexp_pair (Cexp_num 0) (Cexp_num 0)) /\
  (candle_cv_fsa_schedule_state (Cexp_pair instruction program) =
     let tail = candle_cv_fsa_schedule_state program in
     let tail_nonlinear = Cexp_fst tail in
     Cexp_pair
       (Cexp_if (candle_cv_fsa_instruction_is_nonlinear instruction)
         (Cexp_num 1) tail_nonlinear)
       (Cexp_pair
         (Cexp_if tail_nonlinear (Cexp_num 0) (Cexp_num 1))
         (Cexp_snd tail)))`;;

let candle_cv_fsa_schedule_state_compute = prove
 (`!program.
     candle_cv_fsa_schedule_state program =
     Cexp_if (Cexp_ispair program)
       (let tail = candle_cv_fsa_schedule_state (Cexp_snd program) in
        let tail_nonlinear = Cexp_fst tail in
        Cexp_pair
          (Cexp_if
            (candle_cv_fsa_instruction_is_nonlinear (Cexp_fst program))
            (Cexp_num 1) tail_nonlinear)
          (Cexp_pair
            (Cexp_if tail_nonlinear (Cexp_num 0) (Cexp_num 1))
            (Cexp_snd tail)))
       (Cexp_pair (Cexp_num 0) (Cexp_num 0))`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsa_schedule_state_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsa_program_run_scheduled_def = define
 `(candle_cv_fsa_program_run_scheduled
     center_boxes boxes radii (Cexp_num n) box_program schedule stack =
     stack) /\
  (candle_cv_fsa_program_run_scheduled
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_num n) schedule stack =
     stack) /\
  (candle_cv_fsa_program_run_scheduled
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_pair bh bt)
       (Cexp_num n) stack =
     stack) /\
  (candle_cv_fsa_program_run_scheduled
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_pair bh bt)
       (Cexp_pair use_fixed schedule) stack =
     candle_cv_fsa_program_run_scheduled center_boxes boxes radii ct bt
       schedule
       (candle_cv_fsa_program_step
         center_boxes boxes radii use_fixed ch bh stack))`;;

let candle_cv_fsa_program_run_scheduled_compute = prove
 (`!center_boxes boxes radii center_program box_program schedule stack.
     candle_cv_fsa_program_run_scheduled
       center_boxes boxes radii center_program box_program schedule stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (Cexp_if (Cexp_ispair schedule)
           (candle_cv_fsa_program_run_scheduled
             center_boxes boxes radii
             (Cexp_snd center_program) (Cexp_snd box_program)
             (Cexp_snd schedule)
             (candle_cv_fsa_program_step
               center_boxes boxes radii (Cexp_fst schedule)
               (Cexp_fst center_program) (Cexp_fst box_program) stack))
           stack)
         stack)
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `schedule:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsa_program_run_scheduled_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsa_program_scheduled_def = new_definition
 `candle_cv_fsa_program_scheduled
      center_program box_program schedule boxes =
    candle_cv_fsa_item_to_q
      (candle_cv_fsa_item_head
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_fsa_program_run_scheduled
          (candle_cv_q_center_environment_list boxes) boxes
          (candle_cv_q_fixed_list_round_upper
            (candle_cv_q_radius_list boxes))
          center_program box_program schedule (Cexp_num 0)))`;;

let candle_cv_fsa_certified_check_scheduled_def = new_definition
 `candle_cv_fsa_certified_check_scheduled
      center_program box_program schedule boxes =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_fsa_program_scheduled
        center_program box_program schedule boxes)`;;

let candle_cv_fsa_stable_jobs_check_scheduled_def = define
 `(candle_cv_fsa_stable_jobs_check_scheduled
      source_program box_program schedule (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fsa_stable_jobs_check_scheduled
      source_program box_program schedule (Cexp_pair job jobs) =
     Cexp_if
       (candle_cv_analytic_program_sqrt_data_exact
         (Cexp_fst job) source_program)
       (let center_patched =
          candle_cv_analytic_program_patch_sqrt
            (Cexp_fst job) source_program in
        Cexp_if
          (Cexp_fst
            (candle_cv_fsa_certified_check_scheduled
              (Cexp_snd center_patched) box_program schedule
              (Cexp_snd job)))
          (candle_cv_fsa_stable_jobs_check_scheduled
            source_program box_program schedule jobs)
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_fsa_stable_jobs_check_scheduled_compute = prove
 (`!source_program box_program schedule jobs.
     candle_cv_fsa_stable_jobs_check_scheduled
       source_program box_program schedule jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if
         (candle_cv_analytic_program_sqrt_data_exact
           (Cexp_fst (Cexp_fst jobs)) source_program)
         (let center_patched =
            candle_cv_analytic_program_patch_sqrt
              (Cexp_fst (Cexp_fst jobs)) source_program in
          Cexp_if
            (Cexp_fst
              (candle_cv_fsa_certified_check_scheduled
                (Cexp_snd center_patched) box_program schedule
                (Cexp_snd (Cexp_fst jobs))))
            (candle_cv_fsa_stable_jobs_check_scheduled
              source_program box_program schedule (Cexp_snd jobs))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsa_stable_jobs_check_scheduled_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsa_stable_batch_check_scheduled_def = new_definition
 `candle_cv_fsa_stable_batch_check_scheduled
      source_program box_intervals jobs =
    Cexp_if
      (candle_cv_analytic_program_sqrt_data_exact
        box_intervals source_program)
      (let box_patched =
         candle_cv_analytic_program_patch_sqrt
           box_intervals source_program in
       let schedule_state = candle_cv_fsa_schedule_state source_program in
       candle_cv_fsa_stable_jobs_check_scheduled
         source_program (Cexp_snd box_patched)
         (Cexp_snd schedule_state) jobs)
      (Cexp_num 0)`;;

(* Deep concrete equality is diagnostic only.  It lets the benchmark compare *)
(* every scheduled Taylor result with the established evaluator internally,  *)
(* without returning or printing the large intermediate values.               *)

let candle_cv_fsa_deep_equal_def = define
 `(candle_cv_fsa_deep_equal (Cexp_num n) (Cexp_num m) =
     Cexp_eq (Cexp_num n) (Cexp_num m)) /\
  (candle_cv_fsa_deep_equal (Cexp_num n) (Cexp_pair left right) =
     Cexp_num 0) /\
  (candle_cv_fsa_deep_equal (Cexp_pair left right) (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fsa_deep_equal (Cexp_pair left right)
      (Cexp_pair other_left other_right) =
     Cexp_if (candle_cv_fsa_deep_equal left other_left)
       (candle_cv_fsa_deep_equal right other_right) (Cexp_num 0))`;;

(* Kernel.compute equations must have variables, rather than constructor       *)
(* patterns, as their left-hand arguments.  Keep the pattern definition for   *)
(* the recursive function, but expose one general equation to the evaluator.  *)

let candle_cv_fsa_deep_equal_compute = prove
 (`!left right.
     candle_cv_fsa_deep_equal left right =
     Cexp_if (Cexp_ispair left)
       (Cexp_if (Cexp_ispair right)
         (Cexp_if
           (candle_cv_fsa_deep_equal
             (Cexp_fst left) (Cexp_fst right))
           (candle_cv_fsa_deep_equal
             (Cexp_snd left) (Cexp_snd right))
           (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_if (Cexp_ispair right)
         (Cexp_num 0) (Cexp_eq left right))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `left:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `right:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsa_deep_equal_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsa_stable_jobs_schedule_equal_def = define
 `(candle_cv_fsa_stable_jobs_schedule_equal
      source_program box_program schedule (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fsa_stable_jobs_schedule_equal
      source_program box_program schedule (Cexp_pair job jobs) =
     let center_patched =
       candle_cv_analytic_program_patch_sqrt
         (Cexp_fst job) source_program in
     Cexp_if
       (candle_cv_fsa_deep_equal
         (candle_cv_fsa_program
           (Cexp_snd center_patched) box_program (Cexp_snd job))
         (candle_cv_fsa_program_scheduled
           (Cexp_snd center_patched) box_program schedule (Cexp_snd job)))
       (candle_cv_fsa_stable_jobs_schedule_equal
         source_program box_program schedule jobs)
       (Cexp_num 0))`;;

let candle_cv_fsa_stable_jobs_schedule_equal_compute = prove
 (`!source_program box_program schedule jobs.
     candle_cv_fsa_stable_jobs_schedule_equal
       source_program box_program schedule jobs =
     Cexp_if (Cexp_ispair jobs)
       (let center_patched =
          candle_cv_analytic_program_patch_sqrt
            (Cexp_fst (Cexp_fst jobs)) source_program in
        Cexp_if
          (candle_cv_fsa_deep_equal
            (candle_cv_fsa_program
              (Cexp_snd center_patched) box_program
              (Cexp_snd (Cexp_fst jobs)))
            (candle_cv_fsa_program_scheduled
              (Cexp_snd center_patched) box_program schedule
              (Cexp_snd (Cexp_fst jobs))))
          (candle_cv_fsa_stable_jobs_schedule_equal
            source_program box_program schedule (Cexp_snd jobs))
          (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsa_stable_jobs_schedule_equal_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsa_stable_batch_schedule_equal_def = new_definition
 `candle_cv_fsa_stable_batch_schedule_equal
      source_program box_intervals jobs =
    let box_patched =
      candle_cv_analytic_program_patch_sqrt box_intervals source_program in
    let schedule_state = candle_cv_fsa_schedule_state source_program in
    candle_cv_fsa_stable_jobs_schedule_equal
      source_program (Cexp_snd box_patched)
      (Cexp_snd schedule_state) jobs`;;

let candle_cv_fsa_scheduled_compute_eqs =
  map (REWRITE_RULE[LET_END_DEF])
    (union candle_cv_fsa_stable_batch_compute_eqs
      [SPEC_ALL candle_cv_fsa_deep_equal_compute;
        SPEC_ALL candle_cv_fsa_schedule_state_compute;
        SPEC_ALL candle_cv_fsa_program_run_scheduled_compute;
        SPEC_ALL candle_cv_fsa_program_scheduled_def;
        SPEC_ALL candle_cv_fsa_certified_check_scheduled_def;
        SPEC_ALL candle_cv_fsa_stable_jobs_check_scheduled_compute;
        SPEC_ALL candle_cv_fsa_stable_batch_check_scheduled_def;
        SPEC_ALL candle_cv_fsa_stable_jobs_schedule_equal_compute;
        SPEC_ALL candle_cv_fsa_stable_batch_schedule_equal_def]);;

end;;
