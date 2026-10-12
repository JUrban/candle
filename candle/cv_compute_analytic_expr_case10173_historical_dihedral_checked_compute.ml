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

(* Finite side conditions required by the historical low-work arithmetic.
   Root certificates cover the two square roots; this guard additionally
   authenticates the positive reciprocal inputs and the restricted atan
   approximation range.  All quantities are recomputed from the job box. *)

let candle_fs_hist_positive_interval_def = new_definition
 `candle_fs_hist_positive_interval
      (value:((num#num)#(num#num))) <=>
    SND (FST value) = 0 /\ SND (SND value) = 0 /\
    0 < FST (FST value) /\ FST (FST value) <= FST (SND value)`;;

let candle_cv_fs_hist_positive_interval_def = new_definition
 `candle_cv_fs_hist_positive_interval value =
    candle_cv_fs_hist_bool_and
      (Cexp_eq (Cexp_snd (Cexp_fst value)) (Cexp_num 0))
      (candle_cv_fs_hist_bool_and
        (Cexp_eq (Cexp_snd (Cexp_snd value)) (Cexp_num 0))
        (candle_cv_fs_hist_bool_and
          (Cexp_less (Cexp_num 0) (Cexp_fst (Cexp_fst value)))
          (candle_cv_fs_hist_num_le
            (Cexp_fst (Cexp_fst value))
            (Cexp_fst (Cexp_snd value)))))`;;

let candle_fs_hist_positive_product_def = new_definition
 `candle_fs_hist_positive_product
      (left:((num#num)#(num#num))) right <=>
    0 < (FST (FST left) * FST (FST right)) DIV candle_fs_scale`;;

let candle_cv_fs_hist_positive_product_def = new_definition
 `candle_cv_fs_hist_positive_product left right =
    Cexp_less (Cexp_num 0)
      (Cexp_div
        (Cexp_mul (Cexp_fst (Cexp_fst left))
          (Cexp_fst (Cexp_fst right)))
        candle_cv_fs_scale)`;;

let candle_fs_hist_unit_interval_def = new_definition
 `candle_fs_hist_unit_interval (value:((num#num)#(num#num))) <=>
    -- &1 < candle_fs_real (FST value) /\
    candle_fs_real (SND value) < &1`;;

let candle_cv_fs_hist_unit_interval_def = new_definition
 `candle_cv_fs_hist_unit_interval value =
    candle_cv_fs_hist_bool_and
      (candle_cv_fs_hist_bool_not
        (candle_cv_fs_raw_le (Cexp_fst value)
          (candle_cv_fs_raw_neg candle_cv_fs_one)))
      (candle_cv_fs_hist_bool_not
        (candle_cv_fs_raw_le candle_cv_fs_one (Cexp_snd value)))`;;

let candle_cv_fs_hist_quotient_def = new_definition
 `candle_cv_fs_hist_quotient delta_x4_interval root_delta root_four_x0 =
    candle_cv_fs_angle_interval_mul
      (candle_cv_fs_interval_neg delta_x4_interval)
      (candle_cv_fs_hist_positive_inv
        (candle_cv_fs_angle_interval_mul root_delta root_four_x0))`;;

let candle_fs_hist_environment_nonnegative_def = new_definition
 `candle_fs_hist_environment_nonnegative environment <=>
    candle_fs_raw_le (0,0)
      (FST (candle_fs_interval_lookup 0 environment)) /\
    candle_fs_raw_le (0,0)
      (FST (candle_fs_interval_lookup 1 environment)) /\
    candle_fs_raw_le (0,0)
      (FST (candle_fs_interval_lookup 2 environment)) /\
    candle_fs_raw_le (0,0)
      (FST (candle_fs_interval_lookup 4 environment)) /\
    candle_fs_raw_le (0,0)
      (FST (candle_fs_interval_lookup 5 environment))`;;

let candle_cv_fs_hist_environment_nonnegative_def = new_definition
 `candle_cv_fs_hist_environment_nonnegative environment =
    candle_cv_fs_hist_bool_and
      (candle_cv_fs_raw_le candle_cv_fs_zero
        (Cexp_fst (candle_cv_fs_interval_lookup
          (Cexp_num 0) environment)))
      (candle_cv_fs_hist_bool_and
        (candle_cv_fs_raw_le candle_cv_fs_zero
          (Cexp_fst (candle_cv_fs_interval_lookup
            (Cexp_num 1) environment)))
        (candle_cv_fs_hist_bool_and
          (candle_cv_fs_raw_le candle_cv_fs_zero
            (Cexp_fst (candle_cv_fs_interval_lookup
              (Cexp_num 2) environment)))
          (candle_cv_fs_hist_bool_and
            (candle_cv_fs_raw_le candle_cv_fs_zero
              (Cexp_fst (candle_cv_fs_interval_lookup
                (Cexp_num 4) environment)))
            (candle_cv_fs_raw_le candle_cv_fs_zero
              (Cexp_fst (candle_cv_fs_interval_lookup
                (Cexp_num 5) environment))))))`;;

let candle_cv_case10173_hist_production_guard_def = new_definition
 `candle_cv_case10173_hist_production_guard boxes roots =
    let center_environment = candle_cv_fs_interval_list_of_q
      (candle_cv_q_center_environment_list boxes) in
    let box_environment = candle_cv_fs_interval_list_of_q boxes in
    let center_root_delta = candle_cv_fs_interval_lookup (Cexp_num 0) roots in
    let center_root_four_x0 = candle_cv_fs_interval_lookup (Cexp_num 1) roots in
    let box_root_delta = candle_cv_fs_interval_lookup (Cexp_num 2) roots in
    let box_root_four_x0 = candle_cv_fs_interval_lookup (Cexp_num 3) roots in
    let center_u126 = Cexp_fst (candle_cv_fs_hist_u126 center_environment) in
    let center_u135 = Cexp_fst (candle_cv_fs_hist_u135 center_environment) in
    let box_u126 = Cexp_fst (candle_cv_fs_hist_u126 box_environment) in
    let box_u135 = Cexp_fst (candle_cv_fs_hist_u135 box_environment) in
    let center_quotient = candle_cv_fs_hist_quotient
      (candle_cv_fs_hist_delta_x4_value center_environment)
      center_root_delta center_root_four_x0 in
    let box_quotient = candle_cv_fs_hist_quotient
      (candle_cv_fs_hist_second_value
        (candle_cv_fs_hist_delta_x4_second box_environment))
      box_root_delta box_root_four_x0 in
    candle_cv_fs_hist_bool_and
      (candle_cv_fs_hist_positive_product
        center_root_delta center_root_four_x0)
      (candle_cv_fs_hist_bool_and
        (candle_cv_fs_hist_positive_product
          box_root_delta box_root_four_x0)
        (candle_cv_fs_hist_bool_and
          (candle_cv_fs_hist_positive_interval center_u126)
          (candle_cv_fs_hist_bool_and
            (candle_cv_fs_hist_positive_interval center_u135)
            (candle_cv_fs_hist_bool_and
              (candle_cv_fs_hist_positive_product center_u126 center_u135)
              (candle_cv_fs_hist_bool_and
                (candle_cv_fs_hist_positive_interval box_u126)
                (candle_cv_fs_hist_bool_and
                  (candle_cv_fs_hist_positive_interval box_u135)
                  (candle_cv_fs_hist_bool_and
                    (candle_cv_fs_hist_positive_product box_u126 box_u135)
                    (candle_cv_fs_hist_bool_and
                      (candle_cv_fs_hist_unit_interval center_quotient)
                      (candle_cv_fs_hist_bool_and
                        (candle_cv_fs_hist_unit_interval box_quotient)
                        (candle_cv_fs_hist_bool_and
                          (candle_cv_fs_hist_environment_nonnegative
                            center_environment)
                          (candle_cv_fs_hist_environment_nonnegative
                            box_environment)))))))))))`;;

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
         (candle_cv_case10173_hist_production_guard
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
             (candle_cv_case10173_hist_production_guard
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
         candle_cv_fs_hist_positive_interval_def;
         candle_cv_fs_hist_positive_product_def;
         candle_cv_fs_hist_unit_interval_def;
         candle_cv_fs_hist_quotient_def;
         candle_cv_fs_hist_environment_nonnegative_def;
         candle_cv_case10173_hist_production_guard_def;
         candle_cv_case10173_hist_checked_jobs_check_compute;
         candle_cv_case10173_hist_checked_raw_jobs_check_def]));;

end;;
