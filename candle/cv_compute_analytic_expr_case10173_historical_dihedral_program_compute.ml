(* ========================================================================== *)
(* Case-10173 historical-dihedral program splice.                            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  This executable           *)
(* discriminator replaces authenticated outer instructions 31--38 with one  *)
(* fixed-scale historical dihedral operation.  It retains the existing       *)
(* source-program and square-root-certificate checks; four additional sealed *)
(* root intervals are supplied per job for this bounded performance test.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_compute.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_program_compute = struct

open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;

let candle_cv_case10173_hist_item_def = new_definition
 `candle_cv_case10173_hist_item center_boxes boxes radii roots =
    let center_environment =
      candle_cv_fs_interval_list_of_q center_boxes in
    let box_environment = candle_cv_fs_interval_list_of_q boxes in
    let center_first = candle_cv_fs_hist_first_order center_environment
      (candle_cv_fs_interval_lookup (Cexp_num 0) roots)
      (candle_cv_fs_interval_lookup (Cexp_num 1) roots) in
    let box_second = candle_cv_fs_hist_second_order box_environment
      (candle_cv_fs_interval_lookup (Cexp_num 2) roots)
      (candle_cv_fs_interval_lookup (Cexp_num 3) roots) in
    candle_cv_fsa_item_fixed
      (candle_cv_fs_result_complete_rounded
        (candle_cv_fs_list_of_q radii) (Cexp_num 1) center_first
        (candle_cv_fs_hist_second_hessian box_second))`;;

let candle_cv_case10173_hist_drop_eight_def = new_definition
 `candle_cv_case10173_hist_drop_eight program =
    Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd
      (Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd program)))))))`;;

let candle_cv_case10173_hist_splice_aux_def = define
 `(candle_cv_case10173_hist_splice_aux
      (Cexp_pair x y) program = Cexp_num 0) /\
  (candle_cv_case10173_hist_splice_aux
      (Cexp_num 0) program =
     Cexp_pair (Cexp_num 9)
       (candle_cv_case10173_hist_drop_eight program)) /\
  (candle_cv_case10173_hist_splice_aux
      (Cexp_num (SUC n)) (Cexp_num m) = Cexp_num 0) /\
  (candle_cv_case10173_hist_splice_aux
      (Cexp_num (SUC n)) (Cexp_pair h t) =
     Cexp_pair h
       (candle_cv_case10173_hist_splice_aux (Cexp_num n) t))`;;

let candle_cv_case10173_hist_splice_aux_compute = prove
 (`!splice_count program.
     candle_cv_case10173_hist_splice_aux splice_count program =
     Cexp_if (Cexp_ispair splice_count) (Cexp_num 0)
       (Cexp_if (Cexp_eq splice_count (Cexp_num 0))
         (Cexp_pair (Cexp_num 9)
           (candle_cv_case10173_hist_drop_eight program))
         (Cexp_if (Cexp_ispair program)
           (Cexp_pair (Cexp_fst program)
             (candle_cv_case10173_hist_splice_aux
               (Cexp_sub splice_count (Cexp_num 1))
               (Cexp_snd program)))
           (Cexp_num 0)))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `splice_count:cval` (cases "cval")) THENL
   [MP_TAC (SPEC `a:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
    STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
    REWRITE_TAC
      [candle_cv_case10173_hist_splice_aux_def;cexp_if_def;
       cexp_ispair_def;cexp_fst_def;cexp_snd_def;cexp_eq_def;
       cexp_sub_def;injectivity "cval";injectivity "num";NOT_SUC;
       ARITH_RULE `SUC n - 1 = n`];
    REWRITE_TAC
      [candle_cv_case10173_hist_splice_aux_def;cexp_if_def;
       cexp_ispair_def]]);;

let candle_cv_case10173_hist_step_def = new_definition
 `candle_cv_case10173_hist_step center_boxes boxes radii roots
      center_instruction box_instruction stack =
    Cexp_if (Cexp_eq center_instruction (Cexp_num 9))
      (Cexp_if (Cexp_eq box_instruction (Cexp_num 9))
        (Cexp_pair
          (candle_cv_case10173_hist_item center_boxes boxes radii roots)
          stack)
        (Cexp_pair
          (candle_cv_fsa_item_default center_boxes boxes) stack))
      (Cexp_if (Cexp_eq box_instruction (Cexp_num 9))
        (Cexp_pair
          (candle_cv_fsa_item_default center_boxes boxes) stack)
        (candle_cv_fso_program_step_fixed_nonlinear
          center_boxes boxes radii center_instruction box_instruction
          stack))`;;

let candle_cv_case10173_hist_program_run_def = define
 `(candle_cv_case10173_hist_program_run center_boxes boxes radii roots
      (Cexp_num n) box_program stack = stack) /\
  (candle_cv_case10173_hist_program_run center_boxes boxes radii roots
      (Cexp_pair ch ct) (Cexp_num n) stack = stack) /\
  (candle_cv_case10173_hist_program_run center_boxes boxes radii roots
      (Cexp_pair ch ct) (Cexp_pair bh bt) stack =
     candle_cv_case10173_hist_program_run center_boxes boxes radii roots
       ct bt (candle_cv_case10173_hist_step
         center_boxes boxes radii roots ch bh stack))`;;

let candle_cv_case10173_hist_program_run_compute = prove
 (`!center_boxes boxes radii roots center_program box_program stack.
     candle_cv_case10173_hist_program_run center_boxes boxes radii roots
       center_program box_program stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (candle_cv_case10173_hist_program_run
           center_boxes boxes radii roots
           (Cexp_snd center_program) (Cexp_snd box_program)
           (candle_cv_case10173_hist_step
             center_boxes boxes radii roots
             (Cexp_fst center_program) (Cexp_fst box_program) stack))
         stack)
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_hist_program_run_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_case10173_hist_program_def = new_definition
 `candle_cv_case10173_hist_program center_program box_program boxes roots =
    let center_boxes = candle_cv_q_center_environment_list boxes in
    let radii = candle_cv_q_fixed_list_round_upper
      (candle_cv_q_radius_list boxes) in
    candle_cv_fsa_item_to_q
      (candle_cv_fsa_item_head center_boxes boxes
        (candle_cv_case10173_hist_program_run center_boxes boxes radii roots
          (candle_cv_case10173_hist_splice_aux
            (Cexp_num 31) center_program)
          (candle_cv_case10173_hist_splice_aux
            (Cexp_num 31) box_program)
          (Cexp_num 0)))`;;

let candle_cv_case10173_hist_certified_check_def = new_definition
 `candle_cv_case10173_hist_certified_check
      center_program box_program boxes roots =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_case10173_hist_program
        center_program box_program boxes roots)`;;

let candle_cv_case10173_hist_jobs_check_def = define
 `(candle_cv_case10173_hist_jobs_check source_program
      (Cexp_num n) (Cexp_num m) = Cexp_num 1) /\
  (candle_cv_case10173_hist_jobs_check source_program
      (Cexp_num n) (Cexp_pair root_record roots) = Cexp_num 0) /\
  (candle_cv_case10173_hist_jobs_check source_program
      (Cexp_pair job jobs) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_case10173_hist_jobs_check source_program
      (Cexp_pair job jobs) (Cexp_pair root_record roots) =
     Cexp_if
       (candle_cv_analytic_program_sqrt_data_exact
         (Cexp_fst job) source_program)
       (let box_patched = candle_cv_analytic_program_patch_sqrt
          (Cexp_fst job) source_program in
        Cexp_if
          (candle_cv_analytic_program_sqrt_data_exact
            (Cexp_fst (Cexp_snd job)) source_program)
          (let center_patched = candle_cv_analytic_program_patch_sqrt
             (Cexp_fst (Cexp_snd job)) source_program in
           Cexp_if
             (Cexp_fst
               (candle_cv_case10173_hist_certified_check
                 (Cexp_snd center_patched) (Cexp_snd box_patched)
                 (Cexp_snd (Cexp_snd job)) root_record))
             (candle_cv_case10173_hist_jobs_check
               source_program jobs roots)
             (Cexp_num 0))
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_case10173_hist_jobs_check_compute = prove
 (`!source_program jobs roots.
     candle_cv_case10173_hist_jobs_check source_program jobs roots =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if (Cexp_ispair roots)
         (Cexp_if
           (candle_cv_analytic_program_sqrt_data_exact
             (Cexp_fst (Cexp_fst jobs)) source_program)
           (let box_patched = candle_cv_analytic_program_patch_sqrt
              (Cexp_fst (Cexp_fst jobs)) source_program in
            Cexp_if
              (candle_cv_analytic_program_sqrt_data_exact
                (Cexp_fst (Cexp_snd (Cexp_fst jobs))) source_program)
              (let center_patched = candle_cv_analytic_program_patch_sqrt
                 (Cexp_fst (Cexp_snd (Cexp_fst jobs))) source_program in
               Cexp_if
                 (Cexp_fst
                   (candle_cv_case10173_hist_certified_check
                     (Cexp_snd center_patched) (Cexp_snd box_patched)
                     (Cexp_snd (Cexp_snd (Cexp_fst jobs)))
                     (Cexp_fst roots)))
                 (candle_cv_case10173_hist_jobs_check
                   source_program (Cexp_snd jobs) (Cexp_snd roots))
                 (Cexp_num 0))
              (Cexp_num 0))
           (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_if (Cexp_ispair roots) (Cexp_num 0) (Cexp_num 1))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `roots:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_hist_jobs_check_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def;
     LET_DEF;LET_END_DEF]);;

let candle_cv_case10173_hist_raw_jobs_check_def = new_definition
 `candle_cv_case10173_hist_raw_jobs_check source_program encoded_jobs roots =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_case10173_hist_jobs_check
        source_program encoded_jobs roots)`;;

let candle_cv_case10173_hist_program_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fso_variable_raw_compute_eqs
      (union candle_cv_fixed_nonlinear_compute_eqs
        (union candle_cv_fs_hist_first_compute_eqs
          (map SPEC_ALL
            [candle_cv_case10173_hist_item_def;
             candle_cv_case10173_hist_drop_eight_def;
             candle_cv_case10173_hist_splice_aux_compute;
             candle_cv_case10173_hist_step_def;
             candle_cv_case10173_hist_program_run_compute;
             candle_cv_case10173_hist_program_def;
             candle_cv_case10173_hist_certified_check_def;
             candle_cv_case10173_hist_jobs_check_compute;
             candle_cv_case10173_hist_raw_jobs_check_def]))));;

end;;
