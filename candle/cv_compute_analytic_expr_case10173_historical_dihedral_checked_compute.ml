(* ========================================================================== *)
(* Case-10173 historical splice: checked auxiliary roots and job wrapper.    *)
(*                                                                            *)
(* The historical program consumes four supplied square-root intervals.      *)
(* This layer recomputes their four radicand intervals from the authenticated *)
(* job box, checks exact list shape, and validates every root enclosure before*)
(* allowing the numerical Taylor verdict to contribute to acceptance.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_program_compute.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_historical_root_certificate_compute.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute = struct

open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_compute;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_certificate_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_compute;;

(* Unlike the underlying certificate checker, this wrapper also authenticates
   the two sign components of the internally computed radicand interval. *)

let candle_cv_fs_hist_positive_root_certificate_def = new_definition
 `candle_cv_fs_hist_positive_root_certificate input root_value =
    candle_cv_fs_hist_bool_and
      (Cexp_eq (Cexp_snd (Cexp_fst input)) (Cexp_num 0))
      (candle_cv_fs_hist_bool_and
        (Cexp_eq (Cexp_snd (Cexp_snd input)) (Cexp_num 0))
        (candle_cv_fs_hist_root_certificate input root_value))`;;

(* Both lists must have exactly the same proper-list shape.  Thus a fifth root,
   a missing root, or an improper tail fails closed. *)

let candle_cv_fs_hist_root_list_check_def = define
 `(candle_cv_fs_hist_root_list_check
      (Cexp_num n) (Cexp_num m) =
      candle_cv_fs_hist_bool_and
        (Cexp_eq (Cexp_num n) (Cexp_num 0))
        (Cexp_eq (Cexp_num m) (Cexp_num 0))) /\
  (candle_cv_fs_hist_root_list_check
      (Cexp_num n) (Cexp_pair root_value roots) = Cexp_num 0) /\
  (candle_cv_fs_hist_root_list_check
      (Cexp_pair input inputs) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_hist_root_list_check
      (Cexp_pair input inputs) (Cexp_pair root_value roots) =
      candle_cv_fs_hist_bool_and
        (candle_cv_fs_hist_positive_root_certificate input root_value)
        (candle_cv_fs_hist_root_list_check inputs roots))`;;

let candle_cv_fs_hist_root_list_check_compute = prove
 (`!inputs roots.
     candle_cv_fs_hist_root_list_check inputs roots =
     Cexp_if (Cexp_ispair inputs)
       (Cexp_if (Cexp_ispair roots)
         (candle_cv_fs_hist_bool_and
           (candle_cv_fs_hist_positive_root_certificate
             (Cexp_fst inputs) (Cexp_fst roots))
           (candle_cv_fs_hist_root_list_check
             (Cexp_snd inputs) (Cexp_snd roots)))
         (Cexp_num 0))
       (Cexp_if (Cexp_ispair roots) (Cexp_num 0)
         (candle_cv_fs_hist_bool_and
           (Cexp_eq inputs (Cexp_num 0))
           (Cexp_eq roots (Cexp_num 0))))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `inputs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `roots:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fs_hist_root_list_check_def;
     candle_cv_fs_hist_bool_and_def;
     cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_case10173_hist_root_inputs_def = new_definition
 `candle_cv_case10173_hist_root_inputs boxes =
    let center_boxes = candle_cv_q_center_environment_list boxes in
    let center_environment = candle_cv_fs_interval_list_of_q center_boxes in
    let box_environment = candle_cv_fs_interval_list_of_q boxes in
    Cexp_pair
      (candle_cv_fs_angle_delta_value center_environment)
      (Cexp_pair
        (candle_cv_fs_angle_interval_scale (Cexp_num 4)
          (candle_cv_fs_interval_lookup (Cexp_num 0) center_environment))
        (Cexp_pair
          (candle_cv_fs_hist_second_value
            (candle_cv_fs_hist_delta_second box_environment))
          (Cexp_pair
            (candle_cv_fs_angle_interval_scale (Cexp_num 4)
              (candle_cv_fs_interval_lookup (Cexp_num 0) box_environment))
            (Cexp_num 0))))`;;

let candle_cv_case10173_hist_root_record_check_def = new_definition
 `candle_cv_case10173_hist_root_record_check boxes roots =
    candle_cv_fs_hist_root_list_check
      (candle_cv_case10173_hist_root_inputs boxes) roots`;;

let candle_cv_case10173_hist_checked_jobs_check_def = define
 `(candle_cv_case10173_hist_checked_jobs_check source_program
      (Cexp_num n) (Cexp_num m) = Cexp_num 1) /\
  (candle_cv_case10173_hist_checked_jobs_check source_program
      (Cexp_num n) (Cexp_pair root_record roots) = Cexp_num 0) /\
  (candle_cv_case10173_hist_checked_jobs_check source_program
      (Cexp_pair job jobs) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_case10173_hist_checked_jobs_check source_program
      (Cexp_pair job jobs) (Cexp_pair root_record roots) =
     Cexp_if
       (candle_cv_case10173_hist_root_record_check
         (Cexp_snd (Cexp_snd job)) root_record)
       (Cexp_if
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
               (candle_cv_case10173_hist_checked_jobs_check
                 source_program jobs roots)
               (Cexp_num 0))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_case10173_hist_checked_jobs_check_compute = prove
 (`!source_program jobs roots.
     candle_cv_case10173_hist_checked_jobs_check source_program jobs roots =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if (Cexp_ispair roots)
         (Cexp_if
           (candle_cv_case10173_hist_root_record_check
             (Cexp_snd (Cexp_snd (Cexp_fst jobs))) (Cexp_fst roots))
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
                   (candle_cv_case10173_hist_checked_jobs_check
                     source_program (Cexp_snd jobs) (Cexp_snd roots))
                   (Cexp_num 0))
                (Cexp_num 0))
             (Cexp_num 0))
           (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_if (Cexp_ispair roots) (Cexp_num 0) (Cexp_num 1))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `roots:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_hist_checked_jobs_check_def;
     cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def;
     LET_DEF; LET_END_DEF]);;

let candle_cv_case10173_hist_checked_raw_jobs_check_def = new_definition
 `candle_cv_case10173_hist_checked_raw_jobs_check
      source_program encoded_jobs roots =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_case10173_hist_checked_jobs_check
        source_program encoded_jobs roots)`;;

let candle_cv_case10173_hist_checked_program_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_case10173_hist_program_compute_eqs
      (map SPEC_ALL
        [candle_cv_fs_hist_bool_not_def;
         candle_cv_fs_hist_bool_and_def;
         candle_cv_fs_hist_num_le_def;
         candle_cv_fs_hist_root_certificate_def;
         candle_cv_fs_hist_positive_root_certificate_def;
         candle_cv_fs_hist_root_list_check_compute;
         candle_cv_case10173_hist_root_inputs_def;
         candle_cv_case10173_hist_root_record_check_def;
         candle_cv_case10173_hist_checked_jobs_check_compute;
         candle_cv_case10173_hist_checked_raw_jobs_check_def]));;

end;;
