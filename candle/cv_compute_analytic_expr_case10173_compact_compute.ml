(* ========================================================================== *)
(* Compact complete case-10173 numerical plan.                               *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The caller supplies a     *)
(* source-derived plan containing the seven additive constants, six          *)
(* coordinate inputs and coefficients, and the angle coefficient.  This      *)
(* discriminator removes the generic outer postfix traversal and performs    *)
(* one final Taylor completion.  A plan/source correspondence theorem and    *)
(* validation of the four historical auxiliary roots are still required.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_compute.ml";;

module Candle_cv_analytic_expr_case10173_compact_compute = struct

open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;

let candle_cv_case10173_compact_list_length_def = define
 `(candle_cv_case10173_compact_list_length (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_case10173_compact_list_length (Cexp_pair h t) =
     Cexp_add (Cexp_num 1)
       (candle_cv_case10173_compact_list_length t))`;;

let candle_cv_case10173_compact_list_length_compute = prove
 (`!items.
     candle_cv_case10173_compact_list_length items =
     Cexp_if (Cexp_ispair items)
       (Cexp_add (Cexp_num 1)
         (candle_cv_case10173_compact_list_length (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_compact_list_length_def;
     cexp_if_def;cexp_ispair_def;cexp_snd_def]);;

(* An accumulator is [domain,[center,hessian]].  It deliberately omits the   *)
(* repeatedly reconstructed value and gradient bounds.                       *)

let candle_cv_case10173_compact_acc_make_def = new_definition
 `candle_cv_case10173_compact_acc_make domain center hessian =
    Cexp_pair domain (Cexp_pair center hessian)`;;

let candle_cv_case10173_compact_acc_domain_def = new_definition
 `candle_cv_case10173_compact_acc_domain acc = Cexp_fst acc`;;

let candle_cv_case10173_compact_acc_center_def = new_definition
 `candle_cv_case10173_compact_acc_center acc =
    Cexp_fst (Cexp_snd acc)`;;

let candle_cv_case10173_compact_acc_hessian_def = new_definition
 `candle_cv_case10173_compact_acc_hessian acc =
    Cexp_snd (Cexp_snd acc)`;;

let candle_cv_case10173_compact_acc_zero_def = new_definition
 `candle_cv_case10173_compact_acc_zero dimensions =
    candle_cv_case10173_compact_acc_make (Cexp_num 1)
      (candle_cv_fs_first_make candle_cv_fs_interval_zero
        (candle_cv_fs_interval_zeros dimensions))
      (candle_cv_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_cv_case10173_compact_acc_add_result_def = new_definition
 `candle_cv_case10173_compact_acc_add_result acc result =
    candle_cv_case10173_compact_acc_make
      (candle_cv_bool_and
        (candle_cv_case10173_compact_acc_domain acc)
        (candle_cv_fs_result_domain result))
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_add
          (candle_cv_fs_first_value
            (candle_cv_case10173_compact_acc_center acc))
          (candle_cv_fs_first_value
            (candle_cv_fs_result_center result)))
        (candle_cv_fs_interval_list_add
          (candle_cv_fs_first_gradient
            (candle_cv_case10173_compact_acc_center acc))
          (candle_cv_fs_first_gradient
            (candle_cv_fs_result_center result))))
      (candle_cv_fs_interval_matrix_add
        (candle_cv_case10173_compact_acc_hessian acc)
        (candle_cv_fs_result_hessian result))`;;

let candle_cv_case10173_compact_constants_def = define
 `(candle_cv_case10173_compact_constants dimensions radii
      (Cexp_num n) acc = acc) /\
  (candle_cv_case10173_compact_constants dimensions radii
      (Cexp_pair program programs) acc =
     candle_cv_case10173_compact_constants dimensions radii programs
       (candle_cv_case10173_compact_acc_add_result acc
         (candle_cv_fs_poly_program_fixed dimensions radii program)))`;;

let candle_cv_case10173_compact_constants_compute = prove
 (`!dimensions radii programs acc.
     candle_cv_case10173_compact_constants dimensions radii programs acc =
     Cexp_if (Cexp_ispair programs)
       (candle_cv_case10173_compact_constants dimensions radii
         (Cexp_snd programs)
         (candle_cv_case10173_compact_acc_add_result acc
           (candle_cv_fs_poly_program_fixed dimensions radii
             (Cexp_fst programs))))
       acc`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `programs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_compact_constants_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_case10173_compact_coordinates_def = define
 `(candle_cv_case10173_compact_coordinates dimensions radii
      (Cexp_num n) coefficient_programs center_certificates
      box_certificates acc = acc) /\
  (candle_cv_case10173_compact_coordinates dimensions radii
      (Cexp_pair input_program input_programs) coefficient_programs
      center_certificates box_certificates acc =
     let input_result =
       candle_cv_fs_poly_program_fixed dimensions radii input_program in
     let root_result = candle_cv_fsn_result_sqrt radii
       (Cexp_fst center_certificates) (Cexp_fst box_certificates)
       input_result in
     let coefficient_result = candle_cv_fs_poly_program_fixed
       dimensions radii (Cexp_fst coefficient_programs) in
     let term_result = candle_cv_fs_result_mul
       radii coefficient_result root_result in
     candle_cv_case10173_compact_coordinates dimensions radii
       input_programs (Cexp_snd coefficient_programs)
       (Cexp_snd center_certificates) (Cexp_snd box_certificates)
       (candle_cv_case10173_compact_acc_add_result acc term_result))`;;

let candle_cv_case10173_compact_coordinates_compute = prove
 (`!dimensions radii input_programs coefficient_programs
       center_certificates box_certificates acc.
     candle_cv_case10173_compact_coordinates dimensions radii
       input_programs coefficient_programs center_certificates
       box_certificates acc =
     Cexp_if (Cexp_ispair input_programs)
       (let input_result = candle_cv_fs_poly_program_fixed
          dimensions radii (Cexp_fst input_programs) in
        let root_result = candle_cv_fsn_result_sqrt radii
          (Cexp_fst center_certificates) (Cexp_fst box_certificates)
          input_result in
        let coefficient_result = candle_cv_fs_poly_program_fixed
          dimensions radii (Cexp_fst coefficient_programs) in
        let term_result = candle_cv_fs_result_mul
          radii coefficient_result root_result in
        candle_cv_case10173_compact_coordinates dimensions radii
          (Cexp_snd input_programs) (Cexp_snd coefficient_programs)
          (Cexp_snd center_certificates) (Cexp_snd box_certificates)
          (candle_cv_case10173_compact_acc_add_result acc term_result))
       acc`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `input_programs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_compact_coordinates_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def;
     LET_DEF;LET_END_DEF]);;

let candle_cv_case10173_compact_historical_result_def = new_definition
 `candle_cv_case10173_compact_historical_result
      center_environment box_environment radii roots =
    let center_first = candle_cv_fs_hist_first_order center_environment
      (candle_cv_fs_interval_lookup (Cexp_num 0) roots)
      (candle_cv_fs_interval_lookup (Cexp_num 1) roots) in
    let box_second = candle_cv_fs_hist_second_order box_environment
      (candle_cv_fs_interval_lookup (Cexp_num 2) roots)
      (candle_cv_fs_interval_lookup (Cexp_num 3) roots) in
    candle_cv_fs_result_complete_rounded radii (Cexp_num 1)
      center_first (candle_cv_fs_hist_second_hessian box_second)`;;

let candle_cv_case10173_compact_result_def = new_definition
 `candle_cv_case10173_compact_result plan boxes
      center_certificates box_certificates roots =
    let center_boxes = candle_cv_q_center_environment_list boxes in
    let dimensions = candle_cv_fs_interval_list_of_q center_boxes in
    let box_environment = candle_cv_fs_interval_list_of_q boxes in
    let q_radii = candle_cv_q_fixed_list_round_upper
      (candle_cv_q_radius_list boxes) in
    let radii = candle_cv_fs_list_of_q q_radii in
    let constants = candle_cv_fs_interval_lookup (Cexp_num 0) plan in
    let input_programs = candle_cv_fs_interval_lookup (Cexp_num 1) plan in
    let coefficient_programs =
      candle_cv_fs_interval_lookup (Cexp_num 2) plan in
    let angle_coefficient_program =
      candle_cv_fs_interval_lookup (Cexp_num 3) plan in
    let constants_acc = candle_cv_case10173_compact_constants
      dimensions radii constants
      (candle_cv_case10173_compact_acc_zero dimensions) in
    let coordinate_acc = candle_cv_case10173_compact_coordinates
      dimensions radii input_programs coefficient_programs
      center_certificates box_certificates constants_acc in
    let angle = candle_cv_case10173_compact_historical_result
      dimensions box_environment radii roots in
    let angle_coefficient = candle_cv_fs_poly_program_fixed
      dimensions radii angle_coefficient_program in
    let angle_term = candle_cv_fs_result_mul
      radii angle_coefficient angle in
    let final_acc = candle_cv_case10173_compact_acc_add_result
      coordinate_acc angle_term in
    candle_cv_fs_result_to_q
      (candle_cv_fs_result_complete_rounded radii
        (candle_cv_case10173_compact_acc_domain final_acc)
        (candle_cv_case10173_compact_acc_center final_acc)
        (candle_cv_case10173_compact_acc_hessian final_acc))`;;

let candle_cv_case10173_compact_certified_check_def = new_definition
 `candle_cv_case10173_compact_certified_check plan boxes
      center_certificates box_certificates roots =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_case10173_compact_result plan boxes
        center_certificates box_certificates roots)`;;

let candle_cv_case10173_compact_plan_shape_def = new_definition
 `candle_cv_case10173_compact_plan_shape plan =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_case10173_compact_list_length plan)
        (Cexp_num 4))
      (candle_cv_bool_and
        (Cexp_eq
          (candle_cv_case10173_compact_list_length
            (candle_cv_fs_interval_lookup (Cexp_num 0) plan))
          (Cexp_num 7))
        (candle_cv_bool_and
          (Cexp_eq
            (candle_cv_case10173_compact_list_length
              (candle_cv_fs_interval_lookup (Cexp_num 1) plan))
            (Cexp_num 6))
          (Cexp_eq
            (candle_cv_case10173_compact_list_length
              (candle_cv_fs_interval_lookup (Cexp_num 2) plan))
            (Cexp_num 6))))`;;

let candle_cv_case10173_compact_roots_shape_def = new_definition
 `candle_cv_case10173_compact_roots_shape expected_length roots =
    Cexp_eq (candle_cv_case10173_compact_list_length roots)
      expected_length`;;

let candle_cv_case10173_compact_jobs_check_def = define
 `(candle_cv_case10173_compact_jobs_check plan
      (Cexp_num n) (Cexp_num m) = Cexp_num 1) /\
  (candle_cv_case10173_compact_jobs_check plan
      (Cexp_num n) (Cexp_pair root_record roots) = Cexp_num 0) /\
  (candle_cv_case10173_compact_jobs_check plan
      (Cexp_pair job jobs) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_case10173_compact_jobs_check plan
      (Cexp_pair job jobs) (Cexp_pair root_record roots) =
     let box_certificates = Cexp_fst job in
     let center_certificates = Cexp_fst (Cexp_snd job) in
     let boxes = Cexp_snd (Cexp_snd job) in
     Cexp_if
       (candle_cv_case10173_compact_roots_shape
         (Cexp_num 7) box_certificates)
       (Cexp_if
         (candle_cv_case10173_compact_roots_shape
           (Cexp_num 7) center_certificates)
         (Cexp_if
           (candle_cv_case10173_compact_roots_shape
             (Cexp_num 4) root_record)
           (Cexp_if
             (Cexp_fst
               (candle_cv_case10173_compact_certified_check plan boxes
                 center_certificates box_certificates root_record))
             (candle_cv_case10173_compact_jobs_check plan jobs roots)
             (Cexp_num 0))
           (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_case10173_compact_jobs_check_compute = prove
 (`!plan jobs roots.
     candle_cv_case10173_compact_jobs_check plan jobs roots =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if (Cexp_ispair roots)
         (let job = Cexp_fst jobs in
          let box_certificates = Cexp_fst job in
          let center_certificates = Cexp_fst (Cexp_snd job) in
          let boxes = Cexp_snd (Cexp_snd job) in
          Cexp_if
            (candle_cv_case10173_compact_roots_shape
              (Cexp_num 7) box_certificates)
            (Cexp_if
              (candle_cv_case10173_compact_roots_shape
                (Cexp_num 7) center_certificates)
              (Cexp_if
                (candle_cv_case10173_compact_roots_shape
                  (Cexp_num 4) (Cexp_fst roots))
                (Cexp_if
                  (Cexp_fst
                    (candle_cv_case10173_compact_certified_check plan boxes
                      center_certificates box_certificates
                      (Cexp_fst roots)))
                  (candle_cv_case10173_compact_jobs_check plan
                    (Cexp_snd jobs) (Cexp_snd roots))
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
    [candle_cv_case10173_compact_jobs_check_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def;
     LET_DEF;LET_END_DEF]);;

let candle_cv_case10173_compact_raw_jobs_check_def = new_definition
 `candle_cv_case10173_compact_raw_jobs_check plan encoded_jobs roots =
    candle_cv_bool_and
      (candle_cv_case10173_compact_plan_shape plan)
      (candle_cv_bool_and
        (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
          encoded_jobs)
        (candle_cv_case10173_compact_jobs_check
          plan encoded_jobs roots))`;;

(* Stage discriminators retain the exact compact arithmetic but return one   *)
(* small digest.  The digest is not an integrity claim; it forces the entire *)
(* computed data tree and permits repeat-equality checks without a large      *)
(* theorem handoff.                                                           *)

let candle_cv_case10173_compact_digest_def = define
 `(candle_cv_case10173_compact_digest (Cexp_num n) = Cexp_num n) /\
  (candle_cv_case10173_compact_digest (Cexp_pair h t) =
     Cexp_add (candle_cv_case10173_compact_digest h)
       (candle_cv_case10173_compact_digest t))`;;

let candle_cv_case10173_compact_digest_compute = prove
 (`!value.
     candle_cv_case10173_compact_digest value =
     Cexp_if (Cexp_ispair value)
       (Cexp_add
         (candle_cv_case10173_compact_digest (Cexp_fst value))
         (candle_cv_case10173_compact_digest (Cexp_snd value)))
       value`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `value:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_compact_digest_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_case10173_compact_coordinate_acc_def = new_definition
 `candle_cv_case10173_compact_coordinate_acc plan boxes
      center_certificates box_certificates =
    let center_boxes = candle_cv_q_center_environment_list boxes in
    let dimensions = candle_cv_fs_interval_list_of_q center_boxes in
    let q_radii = candle_cv_q_fixed_list_round_upper
      (candle_cv_q_radius_list boxes) in
    let radii = candle_cv_fs_list_of_q q_radii in
    let constants = candle_cv_fs_interval_lookup (Cexp_num 0) plan in
    let input_programs = candle_cv_fs_interval_lookup (Cexp_num 1) plan in
    let coefficient_programs =
      candle_cv_fs_interval_lookup (Cexp_num 2) plan in
    let constants_acc = candle_cv_case10173_compact_constants
      dimensions radii constants
      (candle_cv_case10173_compact_acc_zero dimensions) in
    candle_cv_case10173_compact_coordinates dimensions radii
      input_programs coefficient_programs center_certificates
      box_certificates constants_acc`;;

let candle_cv_case10173_compact_coordinate_jobs_digest_def = define
 `(candle_cv_case10173_compact_coordinate_jobs_digest plan
      (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_case10173_compact_coordinate_jobs_digest plan
      (Cexp_pair job jobs) =
     Cexp_add
       (candle_cv_case10173_compact_digest
         (candle_cv_case10173_compact_coordinate_acc plan
           (Cexp_snd (Cexp_snd job)) (Cexp_fst (Cexp_snd job))
           (Cexp_fst job)))
       (candle_cv_case10173_compact_coordinate_jobs_digest plan jobs))`;;

let candle_cv_case10173_compact_coordinate_jobs_digest_compute = prove
 (`!plan jobs.
     candle_cv_case10173_compact_coordinate_jobs_digest plan jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_add
         (candle_cv_case10173_compact_digest
           (candle_cv_case10173_compact_coordinate_acc plan
             (Cexp_snd (Cexp_snd (Cexp_fst jobs)))
             (Cexp_fst (Cexp_snd (Cexp_fst jobs)))
             (Cexp_fst (Cexp_fst jobs))))
         (candle_cv_case10173_compact_coordinate_jobs_digest
           plan (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_compact_coordinate_jobs_digest_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

(* Direct coordinate sqrt jet.  For sqrt(x_i), all first derivatives except  *)
(* i and all Hessian entries except (i,i) are structurally zero.              *)

let candle_cv_case10173_coordinate_vector_def = define
 `(candle_cv_case10173_coordinate_vector value variable
      (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_case10173_coordinate_vector value (Cexp_pair p q)
      (Cexp_pair h t) = Cexp_num 0) /\
  (candle_cv_case10173_coordinate_vector value (Cexp_num 0)
      (Cexp_pair h t) =
     Cexp_pair value (candle_cv_fs_interval_zeros t)) /\
  (candle_cv_case10173_coordinate_vector value (Cexp_num (SUC n))
      (Cexp_pair h t) =
     Cexp_pair candle_cv_fs_interval_zero
       (candle_cv_case10173_coordinate_vector value (Cexp_num n) t))`;;

let candle_cv_case10173_coordinate_vector_compute = prove
 (`!value variable dimensions.
     candle_cv_case10173_coordinate_vector value variable dimensions =
     Cexp_if (Cexp_ispair dimensions)
       (Cexp_if (Cexp_ispair variable) (Cexp_num 0)
         (Cexp_if (Cexp_eq variable (Cexp_num 0))
           (Cexp_pair value
             (candle_cv_fs_interval_zeros (Cexp_snd dimensions)))
           (Cexp_pair candle_cv_fs_interval_zero
             (candle_cv_case10173_coordinate_vector value
               (Cexp_sub variable (Cexp_num 1))
               (Cexp_snd dimensions)))))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `dimensions:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `variable:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_coordinate_vector_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def] THEN
  MP_TAC (SPEC `a:num` num_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST1_TAC
     (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
  REWRITE_TAC
    [candle_cv_case10173_coordinate_vector_def;cexp_if_def;
     cexp_eq_def;cexp_sub_def;injectivity "cval";injectivity "num";
     NOT_SUC;ARITH_RULE `SUC n - 1 = n`]);;

let candle_cv_case10173_coordinate_diagonal_aux_def = define
 `(candle_cv_case10173_coordinate_diagonal_aux value variable
      (Cexp_num n) column_dimensions = Cexp_num 0) /\
  (candle_cv_case10173_coordinate_diagonal_aux value (Cexp_pair p q)
      (Cexp_pair h t) column_dimensions = Cexp_num 0) /\
  (candle_cv_case10173_coordinate_diagonal_aux value (Cexp_num 0)
      (Cexp_pair h t) column_dimensions =
     Cexp_pair
       (candle_cv_case10173_coordinate_vector
         value (Cexp_num 0) column_dimensions)
       (candle_cv_fs_interval_zero_matrix t column_dimensions)) /\
  (candle_cv_case10173_coordinate_diagonal_aux value (Cexp_num (SUC n))
      (Cexp_pair h t) column_dimensions =
     Cexp_pair (candle_cv_fs_interval_zeros column_dimensions)
       (candle_cv_case10173_coordinate_diagonal_aux
         value (Cexp_num n) t column_dimensions))`;;

let candle_cv_case10173_coordinate_diagonal_aux_compute = prove
 (`!value variable row_dimensions column_dimensions.
     candle_cv_case10173_coordinate_diagonal_aux
       value variable row_dimensions column_dimensions =
     Cexp_if (Cexp_ispair row_dimensions)
       (Cexp_if (Cexp_ispair variable) (Cexp_num 0)
         (Cexp_if (Cexp_eq variable (Cexp_num 0))
           (Cexp_pair
             (candle_cv_case10173_coordinate_vector
               value (Cexp_num 0) column_dimensions)
             (candle_cv_fs_interval_zero_matrix
               (Cexp_snd row_dimensions) column_dimensions))
           (Cexp_pair (candle_cv_fs_interval_zeros column_dimensions)
             (candle_cv_case10173_coordinate_diagonal_aux
               value (Cexp_sub variable (Cexp_num 1))
               (Cexp_snd row_dimensions) column_dimensions))))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `row_dimensions:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `variable:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_coordinate_diagonal_aux_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def] THEN
  MP_TAC (SPEC `a:num` num_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST1_TAC
     (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
  REWRITE_TAC
    [candle_cv_case10173_coordinate_diagonal_aux_def;cexp_if_def;
     cexp_eq_def;cexp_sub_def;injectivity "cval";injectivity "num";
     NOT_SUC;ARITH_RULE `SUC n - 1 = n`]);;

let candle_cv_case10173_coordinate_diagonal_def = new_definition
 `candle_cv_case10173_coordinate_diagonal value variable dimensions =
    candle_cv_case10173_coordinate_diagonal_aux
      value variable dimensions dimensions`;;

let candle_cv_case10173_direct_coordinate_sqrt_result_def = new_definition
 `candle_cv_case10173_direct_coordinate_sqrt_result
      dimensions boxes radii variable center_certificate box_certificate =
    let center_input = candle_cv_fs_interval_lookup variable dimensions in
    let box_input = candle_cv_fs_interval_of_q
      (candle_cv_fs_interval_lookup variable boxes) in
    let center_value = candle_cv_fs_interval_of_q center_certificate in
    let center_d = candle_cv_fs_interval_of_q
      (candle_cv_q_dim_jet_sqrt_d center_certificate) in
    let box_dd = candle_cv_fs_interval_of_q
      (candle_cv_q_dim_jet_sqrt_dd box_certificate
        (candle_cv_fs_interval_to_q box_input)) in
    candle_cv_fs_result_complete_rounded radii
      (candle_cv_bool_and
        (candle_cv_fsn_sqrt_domain center_certificate center_input)
        (candle_cv_fsn_sqrt_domain box_certificate box_input))
      (candle_cv_fs_first_make center_value
        (candle_cv_case10173_coordinate_vector
          center_d variable dimensions))
      (candle_cv_case10173_coordinate_diagonal
        box_dd variable dimensions)`;;

let candle_cv_case10173_direct_coordinates_def = define
 `(candle_cv_case10173_direct_coordinates dimensions boxes radii
      (Cexp_num n) coefficient_programs center_certificates
      box_certificates acc = acc) /\
  (candle_cv_case10173_direct_coordinates dimensions boxes radii
      (Cexp_pair input_program input_programs) coefficient_programs
      center_certificates box_certificates acc =
     let variable = Cexp_snd (Cexp_fst input_program) in
     let root_result = candle_cv_case10173_direct_coordinate_sqrt_result
       dimensions boxes radii variable
       (Cexp_fst center_certificates) (Cexp_fst box_certificates) in
     let coefficient_result = candle_cv_fs_poly_program_fixed
       dimensions radii (Cexp_fst coefficient_programs) in
     let term_result = candle_cv_fs_result_mul
       radii coefficient_result root_result in
     candle_cv_case10173_direct_coordinates dimensions boxes radii
       input_programs (Cexp_snd coefficient_programs)
       (Cexp_snd center_certificates) (Cexp_snd box_certificates)
       (candle_cv_case10173_compact_acc_add_result acc term_result))`;;

let candle_cv_case10173_direct_coordinates_compute = prove
 (`!dimensions boxes radii input_programs coefficient_programs
       center_certificates box_certificates acc.
     candle_cv_case10173_direct_coordinates dimensions boxes radii
       input_programs coefficient_programs center_certificates
       box_certificates acc =
     Cexp_if (Cexp_ispair input_programs)
       (let variable = Cexp_snd (Cexp_fst (Cexp_fst input_programs)) in
        let root_result = candle_cv_case10173_direct_coordinate_sqrt_result
          dimensions boxes radii variable
          (Cexp_fst center_certificates) (Cexp_fst box_certificates) in
        let coefficient_result = candle_cv_fs_poly_program_fixed
          dimensions radii (Cexp_fst coefficient_programs) in
        let term_result = candle_cv_fs_result_mul
          radii coefficient_result root_result in
        candle_cv_case10173_direct_coordinates dimensions boxes radii
          (Cexp_snd input_programs) (Cexp_snd coefficient_programs)
          (Cexp_snd center_certificates) (Cexp_snd box_certificates)
          (candle_cv_case10173_compact_acc_add_result acc term_result))
       acc`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `input_programs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_direct_coordinates_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def;
     LET_DEF;LET_END_DEF]);;

let candle_cv_case10173_direct_coordinate_acc_def = new_definition
 `candle_cv_case10173_direct_coordinate_acc plan boxes
      center_certificates box_certificates =
    let center_boxes = candle_cv_q_center_environment_list boxes in
    let dimensions = candle_cv_fs_interval_list_of_q center_boxes in
    let radii = candle_cv_fs_list_of_q
      (candle_cv_q_fixed_list_round_upper
        (candle_cv_q_radius_list boxes)) in
    let constants = candle_cv_fs_interval_lookup (Cexp_num 0) plan in
    let input_programs = candle_cv_fs_interval_lookup (Cexp_num 1) plan in
    let coefficient_programs =
      candle_cv_fs_interval_lookup (Cexp_num 2) plan in
    let constants_acc = candle_cv_case10173_compact_constants
      dimensions radii constants
      (candle_cv_case10173_compact_acc_zero dimensions) in
    candle_cv_case10173_direct_coordinates dimensions boxes radii
      input_programs coefficient_programs center_certificates
      box_certificates constants_acc`;;

let candle_cv_case10173_direct_coordinate_jobs_digest_def = define
 `(candle_cv_case10173_direct_coordinate_jobs_digest plan
      (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_case10173_direct_coordinate_jobs_digest plan
      (Cexp_pair job jobs) =
     Cexp_add
       (candle_cv_case10173_compact_digest
         (candle_cv_case10173_direct_coordinate_acc plan
           (Cexp_snd (Cexp_snd job)) (Cexp_fst (Cexp_snd job))
           (Cexp_fst job)))
       (candle_cv_case10173_direct_coordinate_jobs_digest plan jobs))`;;

let candle_cv_case10173_direct_coordinate_jobs_digest_compute = prove
 (`!plan jobs.
     candle_cv_case10173_direct_coordinate_jobs_digest plan jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_add
         (candle_cv_case10173_compact_digest
           (candle_cv_case10173_direct_coordinate_acc plan
             (Cexp_snd (Cexp_snd (Cexp_fst jobs)))
             (Cexp_fst (Cexp_snd (Cexp_fst jobs)))
             (Cexp_fst (Cexp_fst jobs))))
         (candle_cv_case10173_direct_coordinate_jobs_digest
           plan (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_direct_coordinate_jobs_digest_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_case10173_compact_angle_result_def = new_definition
 `candle_cv_case10173_compact_angle_result boxes roots =
    let center_boxes = candle_cv_q_center_environment_list boxes in
    let dimensions = candle_cv_fs_interval_list_of_q center_boxes in
    let box_environment = candle_cv_fs_interval_list_of_q boxes in
    let radii = candle_cv_fs_list_of_q
      (candle_cv_q_fixed_list_round_upper
        (candle_cv_q_radius_list boxes)) in
    candle_cv_case10173_compact_historical_result
      dimensions box_environment radii roots`;;

let candle_cv_case10173_compact_angle_jobs_digest_def = define
 `(candle_cv_case10173_compact_angle_jobs_digest
      (Cexp_num n) (Cexp_num m) = Cexp_num 0) /\
  (candle_cv_case10173_compact_angle_jobs_digest
      (Cexp_num n) (Cexp_pair root_record roots) = Cexp_num 0) /\
  (candle_cv_case10173_compact_angle_jobs_digest
      (Cexp_pair job jobs) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_case10173_compact_angle_jobs_digest
      (Cexp_pair job jobs) (Cexp_pair root_record roots) =
     Cexp_add
       (candle_cv_case10173_compact_digest
         (candle_cv_case10173_compact_angle_result
           (Cexp_snd (Cexp_snd job)) root_record))
       (candle_cv_case10173_compact_angle_jobs_digest jobs roots))`;;

let candle_cv_case10173_compact_angle_jobs_digest_compute = prove
 (`!jobs roots.
     candle_cv_case10173_compact_angle_jobs_digest jobs roots =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if (Cexp_ispair roots)
         (Cexp_add
           (candle_cv_case10173_compact_digest
             (candle_cv_case10173_compact_angle_result
               (Cexp_snd (Cexp_snd (Cexp_fst jobs)))
               (Cexp_fst roots)))
           (candle_cv_case10173_compact_angle_jobs_digest
             (Cexp_snd jobs) (Cexp_snd roots)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `roots:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_compact_angle_jobs_digest_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_case10173_compact_structure_jobs_check_def = define
 `(candle_cv_case10173_compact_structure_jobs_check
      (Cexp_num n) (Cexp_num m) = Cexp_num 1) /\
  (candle_cv_case10173_compact_structure_jobs_check
      (Cexp_num n) (Cexp_pair root_record roots) = Cexp_num 0) /\
  (candle_cv_case10173_compact_structure_jobs_check
      (Cexp_pair job jobs) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_case10173_compact_structure_jobs_check
      (Cexp_pair job jobs) (Cexp_pair root_record roots) =
     Cexp_if
       (candle_cv_case10173_compact_roots_shape
         (Cexp_num 7) (Cexp_fst job))
       (Cexp_if
         (candle_cv_case10173_compact_roots_shape
           (Cexp_num 7) (Cexp_fst (Cexp_snd job)))
         (Cexp_if
           (candle_cv_case10173_compact_roots_shape
             (Cexp_num 4) root_record)
           (candle_cv_case10173_compact_structure_jobs_check jobs roots)
           (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_case10173_compact_structure_jobs_check_compute = prove
 (`!jobs roots.
     candle_cv_case10173_compact_structure_jobs_check jobs roots =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if (Cexp_ispair roots)
         (Cexp_if
           (candle_cv_case10173_compact_roots_shape
             (Cexp_num 7) (Cexp_fst (Cexp_fst jobs)))
           (Cexp_if
             (candle_cv_case10173_compact_roots_shape
               (Cexp_num 7) (Cexp_fst (Cexp_snd (Cexp_fst jobs))))
             (Cexp_if
               (candle_cv_case10173_compact_roots_shape
                 (Cexp_num 4) (Cexp_fst roots))
               (candle_cv_case10173_compact_structure_jobs_check
                 (Cexp_snd jobs) (Cexp_snd roots))
               (Cexp_num 0))
             (Cexp_num 0))
           (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_if (Cexp_ispair roots) (Cexp_num 0) (Cexp_num 1))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `roots:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_compact_structure_jobs_check_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_case10173_compact_structure_check_def = new_definition
 `candle_cv_case10173_compact_structure_check encoded_jobs roots =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_case10173_compact_structure_jobs_check
        encoded_jobs roots)`;;

let candle_cv_case10173_compact_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fixed_nonlinear_compute_eqs
      (union candle_cv_fs_hist_first_compute_eqs
        (map SPEC_ALL
        [candle_cv_case10173_compact_list_length_compute;
         candle_cv_case10173_compact_acc_make_def;
         candle_cv_case10173_compact_acc_domain_def;
         candle_cv_case10173_compact_acc_center_def;
         candle_cv_case10173_compact_acc_hessian_def;
         candle_cv_case10173_compact_acc_zero_def;
         candle_cv_case10173_compact_acc_add_result_def;
         candle_cv_case10173_compact_constants_compute;
         candle_cv_case10173_compact_coordinates_compute;
         candle_cv_case10173_compact_historical_result_def;
         candle_cv_case10173_compact_result_def;
         candle_cv_case10173_compact_certified_check_def;
         candle_cv_case10173_compact_plan_shape_def;
         candle_cv_case10173_compact_roots_shape_def;
         candle_cv_case10173_compact_jobs_check_compute;
         candle_cv_case10173_compact_raw_jobs_check_def;
         candle_cv_case10173_compact_digest_compute;
         candle_cv_case10173_compact_coordinate_acc_def;
         candle_cv_case10173_compact_coordinate_jobs_digest_compute;
         candle_cv_case10173_coordinate_vector_compute;
         candle_cv_case10173_coordinate_diagonal_aux_compute;
         candle_cv_case10173_coordinate_diagonal_def;
         candle_cv_case10173_direct_coordinate_sqrt_result_def;
         candle_cv_case10173_direct_coordinates_compute;
         candle_cv_case10173_direct_coordinate_acc_def;
         candle_cv_case10173_direct_coordinate_jobs_digest_compute;
         candle_cv_case10173_compact_angle_result_def;
         candle_cv_case10173_compact_angle_jobs_digest_compute;
         candle_cv_case10173_compact_structure_jobs_check_compute;
         candle_cv_case10173_compact_structure_check_def])));;

end;;
