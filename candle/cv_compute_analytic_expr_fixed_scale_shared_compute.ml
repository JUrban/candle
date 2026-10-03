(* ========================================================================== *)
(* Shared symmetric-error construction for the fixed-scale Taylor backend.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This candidate evaluates each symmetric       *)
(* reconstruction radius once, then reuses the resulting cval for both       *)
(* interval endpoints.  It is kept separate from the proved production path  *)
(* until exact-result and performance checks justify integrating it.          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;

module Candle_cv_analytic_expr_fixed_scale_shared_compute = struct

open Candle_cv_analytic_expr_fixed_scale_compute;;

let candle_cv_fs_symmetric_raw_interval_def = new_definition
 `candle_cv_fs_symmetric_raw_interval error =
    Cexp_pair (candle_cv_fs_raw_neg error) error`;;

let candle_cv_fs_gradient_bounds_shared_def = define
 `(candle_cv_fs_gradient_bounds_shared
     radii (Cexp_num n) row_lists = Cexp_num 0) /\
  (candle_cv_fs_gradient_bounds_shared
     radii (Cexp_pair g gs) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_gradient_bounds_shared
     radii (Cexp_pair g gs) (Cexp_pair interval_row row_lists) =
     Cexp_pair
       (candle_cv_fs_raw_interval_round candle_cv_fs_scale
         (candle_cv_fs_raw_interval_add
           (Cexp_pair
             (candle_cv_fs_raw_scale candle_cv_fs_scale (Cexp_fst g))
             (candle_cv_fs_raw_scale candle_cv_fs_scale (Cexp_snd g)))
           (candle_cv_fs_symmetric_raw_interval
             (candle_cv_fs_dot_abs_upper radii interval_row))))
       (candle_cv_fs_gradient_bounds_shared radii gs row_lists))`;;

let candle_cv_fs_gradient_bounds_shared_compute = prove
 (`!radii gradients row_lists.
     candle_cv_fs_gradient_bounds_shared radii gradients row_lists =
     Cexp_if (Cexp_ispair gradients)
       (Cexp_if (Cexp_ispair row_lists)
         (Cexp_pair
           (candle_cv_fs_raw_interval_round candle_cv_fs_scale
             (candle_cv_fs_raw_interval_add
               (Cexp_pair
                 (candle_cv_fs_raw_scale candle_cv_fs_scale
                   (Cexp_fst (Cexp_fst gradients)))
                 (candle_cv_fs_raw_scale candle_cv_fs_scale
                   (Cexp_snd (Cexp_fst gradients))))
               (candle_cv_fs_symmetric_raw_interval
                 (candle_cv_fs_dot_abs_upper
                   radii (Cexp_fst row_lists)))))
           (candle_cv_fs_gradient_bounds_shared
             radii (Cexp_snd gradients) (Cexp_snd row_lists)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `gradients:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_gradient_bounds_shared_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_result_complete_rounded_shared_def = new_definition
 `candle_cv_fs_result_complete_rounded_shared radii domain center hessian =
    candle_cv_fs_result_make domain center
      (candle_cv_fs_raw_interval_round candle_cv_fs_two_scale_squared
        (candle_cv_fs_raw_interval_add
          (Cexp_pair
            (candle_cv_fs_raw_scale candle_cv_fs_two_scale_squared
              (Cexp_fst (candle_cv_fs_first_value center)))
            (candle_cv_fs_raw_scale candle_cv_fs_two_scale_squared
              (Cexp_snd (candle_cv_fs_first_value center))))
          (candle_cv_fs_symmetric_raw_interval
            (candle_cv_fs_raw_add
              (candle_cv_fs_raw_scale
                (Cexp_mul (Cexp_num 2) candle_cv_fs_scale)
                (candle_cv_fs_dot_abs_upper radii
                  (candle_cv_fs_first_gradient center)))
              (candle_cv_fs_weighted_rows_abs_upper
                radii radii hessian)))))
      (candle_cv_fs_gradient_bounds_shared
        radii (candle_cv_fs_first_gradient center) hessian)
      hessian`;;

let candle_cv_fs_result_complete_raw_shared_def = new_definition
 `candle_cv_fs_result_complete_raw_shared radii domain raw_center raw_hessian =
    candle_cv_fs_result_complete_rounded_shared radii domain
      (candle_cv_fs_first_make
        (candle_cv_fs_raw_interval_round candle_cv_fs_scale
          (candle_cv_fs_first_value raw_center))
        (candle_cv_fs_raw_interval_list_round candle_cv_fs_scale
          (candle_cv_fs_first_gradient raw_center)))
      (candle_cv_fs_raw_interval_matrix_round
        candle_cv_fs_scale raw_hessian)`;;

let candle_cv_fs_result_constant_shared_def = new_definition
 `candle_cv_fs_result_constant_shared dimensions radii q =
    candle_cv_fs_result_complete_rounded_shared radii (Cexp_num 1)
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_constant q)
        (candle_cv_fs_interval_zeros dimensions))
      (candle_cv_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_cv_fs_result_variable_shared_def = new_definition
 `candle_cv_fs_result_variable_shared dimensions radii variable =
    candle_cv_fs_result_complete_rounded_shared radii (Cexp_num 1)
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_lookup variable dimensions)
        (candle_cv_fs_interval_unit variable dimensions))
      (candle_cv_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_cv_fs_result_neg_shared_def = new_definition
 `candle_cv_fs_result_neg_shared radii result =
    candle_cv_fs_result_complete_rounded_shared radii
      (candle_cv_fs_result_domain result)
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_neg
          (candle_cv_fs_first_value
            (candle_cv_fs_result_center result)))
        (candle_cv_fs_interval_list_neg
          (candle_cv_fs_first_gradient
            (candle_cv_fs_result_center result))))
      (candle_cv_fs_interval_matrix_neg
        (candle_cv_fs_result_hessian result))`;;

let candle_cv_fs_result_add_shared_def = new_definition
 `candle_cv_fs_result_add_shared radii left right =
    candle_cv_fs_result_complete_rounded_shared radii
      (candle_cv_bool_and
        (candle_cv_fs_result_domain left)
        (candle_cv_fs_result_domain right))
      (candle_cv_fs_first_make
        (candle_cv_fs_interval_add
          (candle_cv_fs_first_value (candle_cv_fs_result_center left))
          (candle_cv_fs_first_value (candle_cv_fs_result_center right)))
        (candle_cv_fs_interval_list_add
          (candle_cv_fs_first_gradient (candle_cv_fs_result_center left))
          (candle_cv_fs_first_gradient (candle_cv_fs_result_center right))))
      (candle_cv_fs_interval_matrix_add
        (candle_cv_fs_result_hessian left)
        (candle_cv_fs_result_hessian right))`;;

let candle_cv_fs_result_mul_shared_def = new_definition
 `candle_cv_fs_result_mul_shared radii left right =
    candle_cv_fs_result_complete_raw_shared radii
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

let candle_cv_fs_result_square_shared_def = new_definition
 `candle_cv_fs_result_square_shared radii result =
    candle_cv_fs_result_mul_shared radii result result`;;

let candle_cv_fs_poly_step_shared_def = new_definition
 `candle_cv_fs_poly_step_shared dimensions radii instruction stack =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
        (Cexp_pair
          (candle_cv_fs_result_constant_shared
            dimensions radii (Cexp_snd instruction)) stack)
        (Cexp_pair
          (candle_cv_fs_result_variable_shared
            dimensions radii (Cexp_snd instruction)) stack))
      (Cexp_if (Cexp_eq instruction (Cexp_num 2))
        (Cexp_pair
          (candle_cv_fs_result_neg_shared radii
            (candle_cv_fs_result_head dimensions stack))
          (candle_cv_fs_result_tail stack))
        (Cexp_if (Cexp_eq instruction (Cexp_num 3))
          (Cexp_pair
            (candle_cv_fs_result_add_shared radii
              (candle_cv_fs_result_head dimensions
                (candle_cv_fs_result_tail stack))
              (candle_cv_fs_result_head dimensions stack))
            (candle_cv_fs_result_tail
              (candle_cv_fs_result_tail stack)))
          (Cexp_if (Cexp_eq instruction (Cexp_num 4))
            (Cexp_pair
              (candle_cv_fs_result_mul_shared radii
                (candle_cv_fs_result_head dimensions
                  (candle_cv_fs_result_tail stack))
                (candle_cv_fs_result_head dimensions stack))
              (candle_cv_fs_result_tail
                (candle_cv_fs_result_tail stack)))
            (Cexp_pair
              (candle_cv_fs_result_square_shared radii
                (candle_cv_fs_result_head dimensions stack))
              (candle_cv_fs_result_tail stack)))))`;;

let candle_cv_fs_poly_run_shared_def = define
 `(candle_cv_fs_poly_run_shared
     dimensions radii (Cexp_num n) stack = stack) /\
  (candle_cv_fs_poly_run_shared
     dimensions radii (Cexp_pair h t) stack =
     candle_cv_fs_poly_run_shared dimensions radii t
       (candle_cv_fs_poly_step_shared dimensions radii h stack))`;;

let candle_cv_fs_poly_run_shared_compute = prove
 (`!dimensions radii program stack.
     candle_cv_fs_poly_run_shared dimensions radii program stack =
     Cexp_if (Cexp_ispair program)
       (candle_cv_fs_poly_run_shared dimensions radii (Cexp_snd program)
         (candle_cv_fs_poly_step_shared
           dimensions radii (Cexp_fst program) stack))
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_poly_run_shared_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_poly_program_shared_def = new_definition
 `candle_cv_fs_poly_program_shared center_boxes radii program =
    candle_cv_fs_result_head (candle_cv_fs_interval_list_of_q center_boxes)
      (candle_cv_fs_poly_run_shared
        (candle_cv_fs_interval_list_of_q center_boxes)
        (candle_cv_fs_list_of_q radii) program (Cexp_num 0))`;;

let candle_cv_fs_shared_compute_eqs =
  union candle_cv_fs_compute_eqs
    (map SPEC_ALL
      [candle_cv_fs_symmetric_raw_interval_def;
       candle_cv_fs_gradient_bounds_shared_compute;
       candle_cv_fs_result_complete_rounded_shared_def;
       candle_cv_fs_result_complete_raw_shared_def;
       candle_cv_fs_result_constant_shared_def;
       candle_cv_fs_result_variable_shared_def;
       candle_cv_fs_result_neg_shared_def;
       candle_cv_fs_result_add_shared_def;
       candle_cv_fs_result_mul_shared_def;
       candle_cv_fs_result_square_shared_def;
       candle_cv_fs_poly_step_shared_def;
       candle_cv_fs_poly_run_shared_compute;
       candle_cv_fs_poly_program_shared_def]);;

end;;
