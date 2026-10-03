(* ========================================================================== *)
(* Fixed-scale dense propagation through nonlinear Taylor instructions.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  Scalar inverse, sqrt, and *)
(* atan enclosures remain the established rational computations.  Their      *)
(* resulting scalar derivative intervals are outward-rounded once to the     *)
(* existing 10^12 fixed scale; dense gradient and Hessian propagation then   *)
(* stays fixed.  This file is a performance/coverage discriminator only until *)
(* the corresponding general analytic invariant is proved.                   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear = struct

open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_expr_first_jet_program_compute;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;

let candle_cv_fsn_interval_mul_def = new_definition
 `candle_cv_fsn_interval_mul left right =
    candle_cv_fs_raw_interval_round candle_cv_fs_scale
      (candle_cv_fs_raw_interval_mul left right)`;;

let candle_cv_fsn_interval_list_scale_def = new_definition
 `candle_cv_fsn_interval_list_scale scalar items =
    candle_cv_fs_raw_interval_list_round candle_cv_fs_scale
      (candle_cv_fs_raw_interval_list_scale scalar items)`;;

let candle_cv_fsn_interval_matrix_scale_def = new_definition
 `candle_cv_fsn_interval_matrix_scale scalar row_lists =
    candle_cv_fs_raw_interval_matrix_round candle_cv_fs_scale
      (candle_cv_fs_raw_interval_matrix_scale scalar row_lists)`;;

let candle_cv_fsn_interval_outer_def = new_definition
 `candle_cv_fsn_interval_outer left right =
    candle_cv_fs_raw_interval_matrix_round candle_cv_fs_scale
      (candle_cv_fs_raw_interval_outer left right)`;;

let candle_cv_fsn_q_inv_interval_def = new_definition
 `candle_cv_fsn_q_inv_interval fixed_interval =
    candle_cv_q_interval_inv
      (candle_cv_fs_interval_to_q fixed_interval)`;;

let candle_cv_fsn_first_inv_def = new_definition
 `candle_cv_fsn_first_inv first =
    let r = candle_cv_fs_interval_of_q
      (candle_cv_fsn_q_inv_interval
        (candle_cv_fs_first_value first)) in
    let r2 = candle_cv_fsn_interval_mul r r in
    candle_cv_fs_first_make r
      (candle_cv_fsn_interval_list_scale
        (candle_cv_fs_interval_neg r2)
        (candle_cv_fs_first_gradient first))`;;

let candle_cv_fsn_inv_hessian_def = new_definition
 `candle_cv_fsn_inv_hessian value gradient hessian =
    let r = candle_cv_fs_interval_of_q
      (candle_cv_fsn_q_inv_interval value) in
    let r2 = candle_cv_fsn_interval_mul r r in
    let r3 = candle_cv_fsn_interval_mul r2 r in
    candle_cv_fs_interval_matrix_add
      (candle_cv_fsn_interval_matrix_scale
        (candle_cv_fs_interval_neg r2) hessian)
      (candle_cv_fsn_interval_matrix_scale
        (candle_cv_fs_interval_add r3 r3)
        (candle_cv_fsn_interval_outer gradient gradient))`;;

let candle_cv_fsn_result_inv_def = new_definition
 `candle_cv_fsn_result_inv radii result =
    candle_cv_fs_result_complete_rounded radii
      (candle_cv_bool_and
        (candle_cv_fs_result_domain result)
        (candle_cv_bool_and
          (candle_cv_q_interval_not_zero
            (candle_cv_fs_interval_to_q
              (candle_cv_fs_first_value
                (candle_cv_fs_result_center result))))
          (candle_cv_q_interval_not_zero
            (candle_cv_fs_interval_to_q
              (candle_cv_fs_result_value_bound result)))))
      (candle_cv_fsn_first_inv (candle_cv_fs_result_center result))
      (candle_cv_fsn_inv_hessian
        (candle_cv_fs_result_value_bound result)
        (candle_cv_fs_result_gradient_bounds result)
        (candle_cv_fs_result_hessian result))`;;

let candle_cv_fsn_sqrt_domain_def = new_definition
 `candle_cv_fsn_sqrt_domain certificate fixed_interval =
    let input = candle_cv_fs_interval_to_q fixed_interval in
    Cexp_if
      (candle_cv_q_interval_sqrt_certificate input certificate)
      (Cexp_if
        (candle_cv_q_interval_not_zero
          (candle_cv_q_interval_add_normalized certificate certificate))
        (candle_cv_q_interval_not_zero
          (candle_cv_q_interval_mul_normalized
            (candle_cv_q_interval_add_normalized certificate certificate)
            (candle_cv_q_interval_add_normalized input input)))
        (Cexp_num 0))
      (Cexp_num 0)`;;

let candle_cv_fsn_first_sqrt_def = new_definition
 `candle_cv_fsn_first_sqrt certificate first =
    let value = candle_cv_fs_interval_of_q certificate in
    let d = candle_cv_fs_interval_of_q
      (candle_cv_q_dim_jet_sqrt_d certificate) in
    candle_cv_fs_first_make value
      (candle_cv_fsn_interval_list_scale d
        (candle_cv_fs_first_gradient first))`;;

let candle_cv_fsn_sqrt_hessian_def = new_definition
 `candle_cv_fsn_sqrt_hessian certificate value gradient hessian =
    let input = candle_cv_fs_interval_to_q value in
    let d = candle_cv_fs_interval_of_q
      (candle_cv_q_dim_jet_sqrt_d certificate) in
    let dd = candle_cv_fs_interval_of_q
      (candle_cv_q_dim_jet_sqrt_dd certificate input) in
    candle_cv_fs_interval_matrix_add
      (candle_cv_fsn_interval_matrix_scale dd
        (candle_cv_fsn_interval_outer gradient gradient))
      (candle_cv_fsn_interval_matrix_scale d hessian)`;;

let candle_cv_fsn_result_sqrt_def = new_definition
 `candle_cv_fsn_result_sqrt
      radii center_certificate box_certificate result =
    candle_cv_fs_result_complete_rounded radii
      (candle_cv_bool_and
        (candle_cv_fs_result_domain result)
        (candle_cv_bool_and
          (candle_cv_fsn_sqrt_domain center_certificate
            (candle_cv_fs_first_value
              (candle_cv_fs_result_center result)))
          (candle_cv_fsn_sqrt_domain box_certificate
            (candle_cv_fs_result_value_bound result))))
      (candle_cv_fsn_first_sqrt center_certificate
        (candle_cv_fs_result_center result))
      (candle_cv_fsn_sqrt_hessian box_certificate
        (candle_cv_fs_result_value_bound result)
        (candle_cv_fs_result_gradient_bounds result)
        (candle_cv_fs_result_hessian result))`;;

let candle_cv_fsn_atn_domain_def = new_definition
 `candle_cv_fsn_atn_domain fixed_interval =
    let input = candle_cv_fs_interval_to_q fixed_interval in
    Cexp_if (candle_cv_q_interval_atn_range_domain input)
      (candle_cv_q_interval_not_zero
        (candle_cv_q_dim_jet_atn_denominator input))
      (Cexp_num 0)`;;

let candle_cv_fsn_atn_d_fixed_def = new_definition
 `candle_cv_fsn_atn_d_fixed fixed_interval =
    candle_cv_fs_interval_of_q
      (candle_cv_q_dim_jet_atn_d
        (candle_cv_fs_interval_to_q fixed_interval))`;;

let candle_cv_fsn_atn_dd_fixed_def = new_definition
 `candle_cv_fsn_atn_dd_fixed fixed_interval =
    candle_cv_fs_interval_of_q
      (candle_cv_q_dim_jet_atn_dd
        (candle_cv_fs_interval_to_q fixed_interval))`;;

let candle_cv_fsn_first_atn_def = new_definition
 `candle_cv_fsn_first_atn first =
    let value = candle_cv_fs_interval_of_q
      (candle_cv_q_interval_atn_range
        (candle_cv_fs_interval_to_q
          (candle_cv_fs_first_value first))) in
    let d = candle_cv_fsn_atn_d_fixed
      (candle_cv_fs_first_value first) in
    candle_cv_fs_first_make value
      (candle_cv_fsn_interval_list_scale d
        (candle_cv_fs_first_gradient first))`;;

let candle_cv_fsn_atn_hessian_def = new_definition
 `candle_cv_fsn_atn_hessian value gradient hessian =
    let d = candle_cv_fsn_atn_d_fixed value in
    let dd = candle_cv_fsn_atn_dd_fixed value in
    candle_cv_fs_interval_matrix_add
      (candle_cv_fsn_interval_matrix_scale dd
        (candle_cv_fsn_interval_outer gradient gradient))
      (candle_cv_fsn_interval_matrix_scale d hessian)`;;

let candle_cv_fsn_result_atn_def = new_definition
 `candle_cv_fsn_result_atn radii result =
    candle_cv_fs_result_complete_rounded radii
      (candle_cv_bool_and
        (candle_cv_fs_result_domain result)
        (candle_cv_bool_and
          (candle_cv_fsn_atn_domain
            (candle_cv_fs_first_value
              (candle_cv_fs_result_center result)))
          (candle_cv_fsn_atn_domain
            (candle_cv_fs_result_value_bound result))))
      (candle_cv_fsn_first_atn (candle_cv_fs_result_center result))
      (candle_cv_fsn_atn_hessian
        (candle_cv_fs_result_value_bound result)
        (candle_cv_fs_result_gradient_bounds result)
        (candle_cv_fs_result_hessian result))`;;

let candle_cv_fsn_result_pi_half_def = new_definition
 `candle_cv_fsn_result_pi_half radii dimensions =
    candle_cv_fs_result_complete_rounded radii (Cexp_num 1)
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_of_q candle_cv_q_pi_half_interval)
        (candle_cv_fs_interval_zeros dimensions))
      (candle_cv_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_cv_fsn_item_sqrt_def = new_definition
 `candle_cv_fsn_item_sqrt
      radii center_certificate box_certificate item =
    candle_cv_fsa_item_fixed
      (candle_cv_fsn_result_sqrt (candle_cv_fs_list_of_q radii)
        center_certificate box_certificate
        (candle_cv_fsa_item_to_fixed item))`;;

let candle_cv_fsn_item_inv_def = new_definition
 `candle_cv_fsn_item_inv radii item =
    candle_cv_fsa_item_fixed
      (candle_cv_fsn_result_inv (candle_cv_fs_list_of_q radii)
        (candle_cv_fsa_item_to_fixed item))`;;

let candle_cv_fsn_item_atn_def = new_definition
 `candle_cv_fsn_item_atn radii item =
    candle_cv_fsa_item_fixed
      (candle_cv_fsn_result_atn (candle_cv_fs_list_of_q radii)
        (candle_cv_fsa_item_to_fixed item))`;;

let candle_cv_fsn_item_pi_half_def = new_definition
 `candle_cv_fsn_item_pi_half radii dimensions =
    candle_cv_fsa_item_fixed
      (candle_cv_fsn_result_pi_half
        (candle_cv_fs_list_of_q radii) dimensions)`;;

let candle_cv_fso_program_step_fixed_nonlinear_def = new_definition
 `candle_cv_fso_program_step_fixed_nonlinear
      center_boxes boxes radii center_instruction box_instruction stack =
    Cexp_if (Cexp_ispair center_instruction)
      (Cexp_if (Cexp_ispair box_instruction)
        (Cexp_if (Cexp_eq (Cexp_fst center_instruction) (Cexp_num 0))
          (Cexp_if (Cexp_eq (Cexp_fst box_instruction) (Cexp_num 0))
            (Cexp_pair
              (candle_cv_fsa_item_fixed
                (candle_cv_fs_poly_program center_boxes radii
                  (Cexp_snd center_instruction)))
              stack)
            (Cexp_pair
              (candle_cv_fsa_item_default center_boxes boxes) stack))
          (Cexp_if (Cexp_eq (Cexp_fst center_instruction) (Cexp_num 1))
            (Cexp_if (Cexp_eq (Cexp_fst box_instruction) (Cexp_num 1))
              (Cexp_pair
                (candle_cv_fsn_item_sqrt radii
                  (Cexp_snd center_instruction)
                  (Cexp_snd box_instruction)
                  (candle_cv_fsa_item_head center_boxes boxes stack))
                (candle_cv_fsa_item_tail stack))
              (Cexp_pair
                (candle_cv_fsa_item_default center_boxes boxes) stack))
            (Cexp_pair
              (candle_cv_fsa_item_default center_boxes boxes) stack)))
        (Cexp_pair
          (candle_cv_fsa_item_default center_boxes boxes) stack))
      (Cexp_if (Cexp_ispair box_instruction)
        (Cexp_pair
          (candle_cv_fsa_item_default center_boxes boxes) stack)
        (Cexp_if (Cexp_eq center_instruction box_instruction)
          (Cexp_if (Cexp_eq center_instruction (Cexp_num 2))
            (Cexp_pair
              (candle_cv_fsa_item_neg (Cexp_num 1) radii
                (candle_cv_fsa_item_head center_boxes boxes stack))
              (candle_cv_fsa_item_tail stack))
            (Cexp_if (Cexp_eq center_instruction (Cexp_num 3))
              (Cexp_pair
                (candle_cv_fsa_item_add (Cexp_num 1) radii
                  (candle_cv_fsa_item_head center_boxes boxes
                    (candle_cv_fsa_item_tail stack))
                  (candle_cv_fsa_item_head center_boxes boxes stack))
                (candle_cv_fsa_item_tail
                  (candle_cv_fsa_item_tail stack)))
              (Cexp_if (Cexp_eq center_instruction (Cexp_num 4))
                (Cexp_pair
                  (candle_cv_fso_item_mul radii
                    (candle_cv_fsa_item_head center_boxes boxes
                      (candle_cv_fsa_item_tail stack))
                    (candle_cv_fsa_item_head center_boxes boxes stack))
                  (candle_cv_fsa_item_tail
                    (candle_cv_fsa_item_tail stack)))
                (Cexp_if (Cexp_eq center_instruction (Cexp_num 5))
                  (Cexp_pair
                    (candle_cv_fso_item_square radii
                      (candle_cv_fsa_item_head center_boxes boxes stack))
                    (candle_cv_fsa_item_tail stack))
                  (Cexp_if (Cexp_eq center_instruction (Cexp_num 6))
                    (Cexp_pair
                      (candle_cv_fsn_item_inv radii
                        (candle_cv_fsa_item_head center_boxes boxes stack))
                      (candle_cv_fsa_item_tail stack))
                    (Cexp_if (Cexp_eq center_instruction (Cexp_num 7))
                      (Cexp_pair
                        (candle_cv_fsn_item_atn radii
                          (candle_cv_fsa_item_head center_boxes boxes stack))
                        (candle_cv_fsa_item_tail stack))
                      (Cexp_if (Cexp_eq center_instruction (Cexp_num 8))
                        (Cexp_pair
                          (candle_cv_fsn_item_pi_half radii boxes) stack)
                        (Cexp_pair
                          (candle_cv_fsa_item_default center_boxes boxes)
                          stack))))))))
          (Cexp_pair
            (candle_cv_fsa_item_default center_boxes boxes) stack)))`;;

let candle_cv_fsn_program_run_def = define
 `(candle_cv_fsn_program_run
     center_boxes boxes radii (Cexp_num n) box_program stack = stack) /\
  (candle_cv_fsn_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_num n) stack = stack) /\
  (candle_cv_fsn_program_run
     center_boxes boxes radii
     (Cexp_pair ch ct) (Cexp_pair bh bt) stack =
     candle_cv_fsn_program_run center_boxes boxes radii ct bt
       (candle_cv_fso_program_step_fixed_nonlinear
         center_boxes boxes radii ch bh stack))`;;

let candle_cv_fsn_program_run_compute = prove
 (`!center_boxes boxes radii center_program box_program stack.
     candle_cv_fsn_program_run
       center_boxes boxes radii center_program box_program stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (candle_cv_fsn_program_run center_boxes boxes radii
           (Cexp_snd center_program) (Cexp_snd box_program)
           (candle_cv_fso_program_step_fixed_nonlinear
             center_boxes boxes radii
             (Cexp_fst center_program) (Cexp_fst box_program) stack))
         stack)
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fsn_program_run_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_fsn_program_def = new_definition
 `candle_cv_fsn_program center_program box_program boxes =
    candle_cv_fsa_item_to_q
      (candle_cv_fsa_item_head
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_fsn_program_run
          (candle_cv_q_center_environment_list boxes) boxes
          (candle_cv_q_fixed_list_round_upper
            (candle_cv_q_radius_list boxes))
          center_program box_program (Cexp_num 0)))`;;

let candle_cv_fsn_certified_check_def = new_definition
 `candle_cv_fsn_certified_check center_program box_program boxes =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_fsn_program center_program box_program boxes)`;;

let candle_cv_fsn_variable_jobs_check_def = define
 `(candle_cv_fsn_variable_jobs_check
      source_program (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fsn_variable_jobs_check
      source_program (Cexp_pair job jobs) =
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
               (candle_cv_fsn_certified_check
                 (Cexp_snd center_patched) (Cexp_snd box_patched)
                 (Cexp_snd (Cexp_snd job))))
             (candle_cv_fsn_variable_jobs_check source_program jobs)
             (Cexp_num 0))
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_fsn_variable_jobs_check_compute = prove
 (`!source_program jobs.
     candle_cv_fsn_variable_jobs_check source_program jobs =
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
                 (candle_cv_fsn_certified_check
                   (Cexp_snd center_patched) (Cexp_snd box_patched)
                   (Cexp_snd (Cexp_snd (Cexp_fst jobs)))))
               (candle_cv_fsn_variable_jobs_check
                 source_program (Cexp_snd jobs))
               (Cexp_num 0))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fsn_variable_jobs_check_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def;
     LET_DEF;LET_END_DEF]);;

let candle_cv_fsn_variable_raw_jobs_check_def = new_definition
 `candle_cv_fsn_variable_raw_jobs_check source_program encoded_jobs =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
        encoded_jobs)
      (candle_cv_fsn_variable_jobs_check source_program encoded_jobs)`;;

let candle_cv_fixed_nonlinear_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fso_variable_raw_compute_eqs
      (map SPEC_ALL
        [candle_cv_fsn_interval_mul_def;
         candle_cv_fsn_interval_list_scale_def;
         candle_cv_fsn_interval_matrix_scale_def;
         candle_cv_fsn_interval_outer_def;
         candle_cv_fsn_q_inv_interval_def;
         candle_cv_fsn_first_inv_def;
         candle_cv_fsn_inv_hessian_def;
         candle_cv_fsn_result_inv_def;
         candle_cv_fsn_sqrt_domain_def;
         candle_cv_fsn_first_sqrt_def;
         candle_cv_fsn_sqrt_hessian_def;
         candle_cv_fsn_result_sqrt_def;
         candle_cv_fsn_atn_domain_def;
         candle_cv_fsn_atn_d_fixed_def;
         candle_cv_fsn_atn_dd_fixed_def;
         candle_cv_fsn_first_atn_def;
         candle_cv_fsn_atn_hessian_def;
         candle_cv_fsn_result_atn_def;
         candle_cv_fsn_result_pi_half_def;
         candle_cv_fsn_item_sqrt_def;
         candle_cv_fsn_item_inv_def;
         candle_cv_fsn_item_atn_def;
         candle_cv_fsn_item_pi_half_def;
         candle_cv_fso_program_step_fixed_nonlinear_def;
         candle_cv_fsn_program_run_compute;
         candle_cv_fsn_program_def;
         candle_cv_fsn_certified_check_def;
         candle_cv_fsn_variable_jobs_check_compute;
         candle_cv_fsn_variable_raw_jobs_check_def]));;

end;;
