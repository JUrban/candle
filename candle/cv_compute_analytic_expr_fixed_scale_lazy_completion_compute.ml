(* ========================================================================== *)
(* Lazy completion discriminator for fixed-scale polynomial programs.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Internal nodes retain only domain, rounded     *)
(* center jet, and rounded Hessian.  Complete value/gradient bounds are       *)
(* reconstructed exactly when multiplication/square consumes them and once   *)
(* at the polynomial-block boundary.  The proved production path is unchanged *)
(* until exact-result and performance checks justify integration.             *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;

module Candle_cv_analytic_expr_fixed_scale_lazy_completion_compute = struct

open Candle_cv_analytic_expr_fixed_scale_compute;;

let candle_cv_fs_core_make_def = new_definition
 `candle_cv_fs_core_make domain center hessian =
    Cexp_pair domain (Cexp_pair center hessian)`;;

let candle_cv_fs_core_domain_def = new_definition
 `candle_cv_fs_core_domain core = Cexp_fst core`;;

let candle_cv_fs_core_center_def = new_definition
 `candle_cv_fs_core_center core = Cexp_fst (Cexp_snd core)`;;

let candle_cv_fs_core_hessian_def = new_definition
 `candle_cv_fs_core_hessian core = Cexp_snd (Cexp_snd core)`;;

let candle_cv_fs_core_force_def = new_definition
 `candle_cv_fs_core_force radii core =
    candle_cv_fs_result_complete_rounded radii
      (candle_cv_fs_core_domain core)
      (candle_cv_fs_core_center core)
      (candle_cv_fs_core_hessian core)`;;

let candle_cv_fs_core_zero_def = new_definition
 `candle_cv_fs_core_zero dimensions =
    candle_cv_fs_core_make (Cexp_num 0)
      (candle_cv_fs_first_make candle_cv_fs_interval_zero
        (candle_cv_fs_interval_zeros dimensions))
      (candle_cv_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_cv_fs_core_head_def = new_definition
 `candle_cv_fs_core_head dimensions stack =
    Cexp_if (Cexp_ispair stack) (Cexp_fst stack)
      (candle_cv_fs_core_zero dimensions)`;;

let candle_cv_fs_core_tail_def = new_definition
 `candle_cv_fs_core_tail stack =
    Cexp_if (Cexp_ispair stack) (Cexp_snd stack) (Cexp_num 0)`;;

let candle_cv_fs_core_constant_def = new_definition
 `candle_cv_fs_core_constant dimensions q =
    candle_cv_fs_core_make (Cexp_num 1)
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_constant q)
        (candle_cv_fs_interval_zeros dimensions))
      (candle_cv_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_cv_fs_core_variable_def = new_definition
 `candle_cv_fs_core_variable dimensions variable =
    candle_cv_fs_core_make (Cexp_num 1)
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_lookup variable dimensions)
        (candle_cv_fs_interval_unit variable dimensions))
      (candle_cv_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_cv_fs_core_neg_def = new_definition
 `candle_cv_fs_core_neg core =
    candle_cv_fs_core_make
      (candle_cv_fs_core_domain core)
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_neg
          (candle_cv_fs_first_value (candle_cv_fs_core_center core)))
        (candle_cv_fs_interval_list_neg
          (candle_cv_fs_first_gradient (candle_cv_fs_core_center core))))
      (candle_cv_fs_interval_matrix_neg
        (candle_cv_fs_core_hessian core))`;;

let candle_cv_fs_core_add_def = new_definition
 `candle_cv_fs_core_add left right =
    candle_cv_fs_core_make
      (candle_cv_bool_and
        (candle_cv_fs_core_domain left)
        (candle_cv_fs_core_domain right))
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_add
          (candle_cv_fs_first_value (candle_cv_fs_core_center left))
          (candle_cv_fs_first_value (candle_cv_fs_core_center right)))
        (candle_cv_fs_interval_list_add
          (candle_cv_fs_first_gradient (candle_cv_fs_core_center left))
          (candle_cv_fs_first_gradient (candle_cv_fs_core_center right))))
      (candle_cv_fs_interval_matrix_add
        (candle_cv_fs_core_hessian left)
        (candle_cv_fs_core_hessian right))`;;

let candle_cv_fs_core_complete_raw_def = new_definition
 `candle_cv_fs_core_complete_raw domain raw_center raw_hessian =
    candle_cv_fs_core_make domain
      (candle_cv_fs_first_make
        (candle_cv_fs_raw_interval_round candle_cv_fs_scale
          (candle_cv_fs_first_value raw_center))
        (candle_cv_fs_raw_interval_list_round candle_cv_fs_scale
          (candle_cv_fs_first_gradient raw_center)))
      (candle_cv_fs_raw_interval_matrix_round
        candle_cv_fs_scale raw_hessian)`;;

let candle_cv_fs_core_mul_full_def = new_definition
 `candle_cv_fs_core_mul_full left right =
    candle_cv_fs_core_complete_raw
      (candle_cv_bool_and
        (candle_cv_fs_result_domain left)
        (candle_cv_fs_result_domain right))
      (candle_cv_fs_first_make
        (candle_cv_fs_raw_interval_mul
          (candle_cv_fs_first_value (candle_cv_fs_result_center left))
          (candle_cv_fs_first_value (candle_cv_fs_result_center right)))
        (candle_cv_fs_raw_interval_list_add
          (candle_cv_fs_raw_interval_list_scale
            (candle_cv_fs_first_value (candle_cv_fs_result_center right))
            (candle_cv_fs_first_gradient (candle_cv_fs_result_center left)))
          (candle_cv_fs_raw_interval_list_scale
            (candle_cv_fs_first_value (candle_cv_fs_result_center left))
            (candle_cv_fs_first_gradient (candle_cv_fs_result_center right)))))
      (candle_cv_fs_raw_interval_matrix_add
        (candle_cv_fs_raw_interval_matrix_add
          (candle_cv_fs_raw_interval_matrix_scale
            (candle_cv_fs_result_value_bound right)
            (candle_cv_fs_result_hessian left))
          (candle_cv_fs_raw_interval_outer
            (candle_cv_fs_result_gradient_bounds left)
            (candle_cv_fs_result_gradient_bounds right)))
        (candle_cv_fs_raw_interval_matrix_add
          (candle_cv_fs_raw_interval_outer
            (candle_cv_fs_result_gradient_bounds right)
            (candle_cv_fs_result_gradient_bounds left))
          (candle_cv_fs_raw_interval_matrix_scale
            (candle_cv_fs_result_value_bound left)
            (candle_cv_fs_result_hessian right))))`;;

let candle_cv_fs_core_mul_def = new_definition
 `candle_cv_fs_core_mul radii left right =
    candle_cv_fs_core_mul_full
      (candle_cv_fs_core_force radii left)
      (candle_cv_fs_core_force radii right)`;;

let candle_cv_fs_core_square_full_def = new_definition
 `candle_cv_fs_core_square_full result =
    candle_cv_fs_core_mul_full result result`;;

let candle_cv_fs_core_square_def = new_definition
 `candle_cv_fs_core_square radii core =
    candle_cv_fs_core_square_full
      (candle_cv_fs_core_force radii core)`;;

let candle_cv_fs_poly_step_lazy_def = new_definition
 `candle_cv_fs_poly_step_lazy dimensions radii instruction stack =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
        (Cexp_pair
          (candle_cv_fs_core_constant dimensions (Cexp_snd instruction)) stack)
        (Cexp_pair
          (candle_cv_fs_core_variable dimensions (Cexp_snd instruction)) stack))
      (Cexp_if (Cexp_eq instruction (Cexp_num 2))
        (Cexp_pair
          (candle_cv_fs_core_neg
            (candle_cv_fs_core_head dimensions stack))
          (candle_cv_fs_core_tail stack))
        (Cexp_if (Cexp_eq instruction (Cexp_num 3))
          (Cexp_pair
            (candle_cv_fs_core_add
              (candle_cv_fs_core_head dimensions
                (candle_cv_fs_core_tail stack))
              (candle_cv_fs_core_head dimensions stack))
            (candle_cv_fs_core_tail (candle_cv_fs_core_tail stack)))
          (Cexp_if (Cexp_eq instruction (Cexp_num 4))
            (Cexp_pair
              (candle_cv_fs_core_mul radii
                (candle_cv_fs_core_head dimensions
                  (candle_cv_fs_core_tail stack))
                (candle_cv_fs_core_head dimensions stack))
              (candle_cv_fs_core_tail (candle_cv_fs_core_tail stack)))
            (Cexp_pair
              (candle_cv_fs_core_square radii
                (candle_cv_fs_core_head dimensions stack))
              (candle_cv_fs_core_tail stack)))))`;;

let candle_cv_fs_poly_run_lazy_def = define
 `(candle_cv_fs_poly_run_lazy
     dimensions radii (Cexp_num n) stack = stack) /\
  (candle_cv_fs_poly_run_lazy
     dimensions radii (Cexp_pair h t) stack =
     candle_cv_fs_poly_run_lazy dimensions radii t
       (candle_cv_fs_poly_step_lazy dimensions radii h stack))`;;

let candle_cv_fs_poly_run_lazy_compute = prove
 (`!dimensions radii program stack.
     candle_cv_fs_poly_run_lazy dimensions radii program stack =
     Cexp_if (Cexp_ispair program)
       (candle_cv_fs_poly_run_lazy dimensions radii (Cexp_snd program)
         (candle_cv_fs_poly_step_lazy
           dimensions radii (Cexp_fst program) stack))
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_poly_run_lazy_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_poly_program_fixed_lazy_def = new_definition
 `candle_cv_fs_poly_program_fixed_lazy dimensions radii program =
    candle_cv_fs_core_force radii
      (candle_cv_fs_core_head dimensions
        (candle_cv_fs_poly_run_lazy
          dimensions radii program (Cexp_num 0)))`;;

let candle_cv_fs_poly_program_lazy_def = new_definition
 `candle_cv_fs_poly_program_lazy center_boxes radii program =
    candle_cv_fs_poly_program_fixed_lazy
      (candle_cv_fs_interval_list_of_q center_boxes)
      (candle_cv_fs_list_of_q radii) program`;;

let candle_cv_fs_lazy_completion_compute_eqs =
  union candle_cv_fs_compute_eqs
    (map SPEC_ALL
      [candle_cv_fs_core_make_def;
       candle_cv_fs_core_domain_def;
       candle_cv_fs_core_center_def;
       candle_cv_fs_core_hessian_def;
       candle_cv_fs_core_force_def;
       candle_cv_fs_core_zero_def;
       candle_cv_fs_core_head_def;
       candle_cv_fs_core_tail_def;
       candle_cv_fs_core_constant_def;
       candle_cv_fs_core_variable_def;
       candle_cv_fs_core_neg_def;
       candle_cv_fs_core_add_def;
       candle_cv_fs_core_complete_raw_def;
       candle_cv_fs_core_mul_full_def;
       candle_cv_fs_core_mul_def;
       candle_cv_fs_core_square_full_def;
       candle_cv_fs_core_square_def;
       candle_cv_fs_poly_step_lazy_def;
       candle_cv_fs_poly_run_lazy_compute;
       candle_cv_fs_poly_program_fixed_lazy_def;
       candle_cv_fs_poly_program_lazy_def]);;

end;;
