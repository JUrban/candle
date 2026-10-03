(* ========================================================================== *)
(* Soundness and exactness for lazy fixed-scale polynomial completion.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_lazy_completion_compute.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_invariant.ml";;

module Candle_cv_analytic_expr_fixed_scale_lazy_completion_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_analytic_expr_fixed_scale_lazy_completion_compute;;

(* Logical counterpart of the compact internal core. *)

let candle_fs_core_make_def = new_definition
 `candle_fs_core_make domain center hessian = (domain,(center,hessian))`;;

let candle_fs_core_domain_def = new_definition
 `candle_fs_core_domain core = FST core`;;

let candle_fs_core_center_def = new_definition
 `candle_fs_core_center core = FST (SND core)`;;

let candle_fs_core_hessian_def = new_definition
 `candle_fs_core_hessian core = SND (SND core)`;;

let candle_fs_core_force_def = new_definition
 `candle_fs_core_force radii core =
    candle_fs_result_complete_rounded radii
      (candle_fs_core_domain core)
      (candle_fs_core_center core)
      (candle_fs_core_hessian core)`;;

let candle_fs_core_zero_def = new_definition
 `candle_fs_core_zero dimensions =
    candle_fs_core_make F
      (candle_fs_first_make candle_fs_interval_zero
        (candle_fs_interval_zeros dimensions))
      (candle_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_fs_core_head_def = define
 `(candle_fs_core_head dimensions [] = candle_fs_core_zero dimensions) /\
  (candle_fs_core_head dimensions (CONS h t) = h)`;;

let candle_fs_core_tail_def = define
 `(candle_fs_core_tail [] = []) /\
  (candle_fs_core_tail (CONS h t) = t)`;;

let candle_fs_core_constant_def = new_definition
 `candle_fs_core_constant dimensions q =
    candle_fs_core_make T
      (candle_fs_first_make
        (candle_fs_interval_constant q)
        (candle_fs_interval_zeros dimensions))
      (candle_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_fs_core_variable_def = new_definition
 `candle_fs_core_variable dimensions variable =
    candle_fs_core_make T
      (candle_fs_first_make
        (candle_fs_interval_lookup variable dimensions)
        (candle_fs_interval_unit variable dimensions))
      (candle_fs_interval_zero_matrix dimensions dimensions)`;;

let candle_fs_core_neg_def = new_definition
 `candle_fs_core_neg core =
    candle_fs_core_make
      (candle_fs_core_domain core)
      (candle_fs_first_make
        (candle_fs_interval_neg
          (candle_fs_first_value (candle_fs_core_center core)))
        (candle_fs_interval_list_neg
          (candle_fs_first_gradient (candle_fs_core_center core))))
      (candle_fs_interval_matrix_neg (candle_fs_core_hessian core))`;;

let candle_fs_core_add_def = new_definition
 `candle_fs_core_add left right =
    candle_fs_core_make
      (candle_fs_core_domain left /\ candle_fs_core_domain right)
      (candle_fs_first_make
        (candle_fs_interval_add
          (candle_fs_first_value (candle_fs_core_center left))
          (candle_fs_first_value (candle_fs_core_center right)))
        (candle_fs_interval_list_add
          (candle_fs_first_gradient (candle_fs_core_center left))
          (candle_fs_first_gradient (candle_fs_core_center right))))
      (candle_fs_interval_matrix_add
        (candle_fs_core_hessian left) (candle_fs_core_hessian right))`;;

let candle_fs_core_complete_raw_def = new_definition
 `candle_fs_core_complete_raw domain raw_center raw_hessian =
    candle_fs_core_make domain
      (candle_fs_first_make
        (candle_fs_raw_interval_round candle_fs_scale
          (candle_fs_first_value raw_center))
        (candle_fs_raw_interval_list_round candle_fs_scale
          (candle_fs_first_gradient raw_center)))
      (candle_fs_raw_interval_matrix_round candle_fs_scale raw_hessian)`;;

let candle_fs_core_mul_full_def = new_definition
 `candle_fs_core_mul_full left right =
    candle_fs_core_complete_raw
      (candle_fs_result_domain left /\ candle_fs_result_domain right)
      (candle_fs_first_make
        (candle_fs_raw_interval_mul
          (candle_fs_first_value (candle_fs_result_center left))
          (candle_fs_first_value (candle_fs_result_center right)))
        (candle_fs_raw_interval_list_add
          (candle_fs_raw_interval_list_scale
            (candle_fs_first_value (candle_fs_result_center right))
            (candle_fs_first_gradient (candle_fs_result_center left)))
          (candle_fs_raw_interval_list_scale
            (candle_fs_first_value (candle_fs_result_center left))
            (candle_fs_first_gradient (candle_fs_result_center right)))))
      (candle_fs_raw_interval_matrix_add
        (candle_fs_raw_interval_matrix_add
          (candle_fs_raw_interval_matrix_scale
            (candle_fs_result_value_bound right)
            (candle_fs_result_hessian left))
          (candle_fs_raw_interval_outer
            (candle_fs_result_gradient_bounds left)
            (candle_fs_result_gradient_bounds right)))
        (candle_fs_raw_interval_matrix_add
          (candle_fs_raw_interval_outer
            (candle_fs_result_gradient_bounds right)
            (candle_fs_result_gradient_bounds left))
          (candle_fs_raw_interval_matrix_scale
            (candle_fs_result_value_bound left)
            (candle_fs_result_hessian right))))`;;

let candle_fs_core_mul_def = new_definition
 `candle_fs_core_mul radii left right =
    candle_fs_core_mul_full
      (candle_fs_core_force radii left)
      (candle_fs_core_force radii right)`;;

let candle_fs_core_square_def = new_definition
 `candle_fs_core_square radii core =
    candle_fs_core_mul_full
      (candle_fs_core_force radii core)
      (candle_fs_core_force radii core)`;;

let candle_fs_poly_step_lazy_def = define
 `(candle_fs_poly_step_lazy dimensions radii
      (Candle_q_push p n d) stack =
     CONS (candle_fs_core_constant dimensions ((p,n),d)) stack) /\
  (candle_fs_poly_step_lazy dimensions radii
      (Candle_q_load variable) stack =
     CONS (candle_fs_core_variable dimensions variable) stack) /\
  (candle_fs_poly_step_lazy dimensions radii Candle_q_neg stack =
     CONS (candle_fs_core_neg (candle_fs_core_head dimensions stack))
       (candle_fs_core_tail stack)) /\
  (candle_fs_poly_step_lazy dimensions radii Candle_q_add stack =
     CONS
       (candle_fs_core_add
         (candle_fs_core_head dimensions (candle_fs_core_tail stack))
         (candle_fs_core_head dimensions stack))
       (candle_fs_core_tail (candle_fs_core_tail stack))) /\
  (candle_fs_poly_step_lazy dimensions radii Candle_q_mul stack =
     CONS
       (candle_fs_core_mul radii
         (candle_fs_core_head dimensions (candle_fs_core_tail stack))
         (candle_fs_core_head dimensions stack))
       (candle_fs_core_tail (candle_fs_core_tail stack))) /\
  (candle_fs_poly_step_lazy dimensions radii Candle_q_square stack =
     CONS
       (candle_fs_core_square radii
         (candle_fs_core_head dimensions stack))
       (candle_fs_core_tail stack))`;;

let candle_fs_poly_run_lazy_def = define
 `(candle_fs_poly_run_lazy dimensions radii [] stack = stack) /\
  (candle_fs_poly_run_lazy dimensions radii (CONS h t) stack =
     candle_fs_poly_run_lazy dimensions radii t
       (candle_fs_poly_step_lazy dimensions radii h stack))`;;

let candle_fs_poly_program_fixed_lazy_def = new_definition
 `candle_fs_poly_program_fixed_lazy dimensions radii program =
    candle_fs_core_force radii
      (candle_fs_core_head dimensions
        (candle_fs_poly_run_lazy dimensions radii program []))`;;

let candle_fs_poly_program_lazy_def = new_definition
 `candle_fs_poly_program_lazy center_boxes radii program =
    candle_fs_poly_program_fixed_lazy
      (candle_fs_interval_list_of_q center_boxes)
      (candle_fs_list_of_q radii) program`;;

(* Computed-value representation of logical cores. *)

let candle_cv_fs_core_def = new_definition
 `candle_cv_fs_core core =
    candle_cv_fs_core_make
      (candle_cv_bool (candle_fs_core_domain core))
      (candle_cv_fs_first (candle_fs_core_center core))
      (candle_cv_fs_interval_matrix (candle_fs_core_hessian core))`;;

let candle_cv_fs_core_list_def = define
 `(candle_cv_fs_core_list [] = Cexp_num 0) /\
  (candle_cv_fs_core_list (CONS h t) =
     Cexp_pair (candle_cv_fs_core h) (candle_cv_fs_core_list t))`;;

let candle_cv_fs_core_bool_false = prove
 (`Cexp_num 0 = candle_cv_bool F`,
  REWRITE_TAC[candle_cv_bool_def]);;

let candle_cv_fs_core_bool_true = prove
 (`Cexp_num 1 = candle_cv_bool T`,
  REWRITE_TAC[candle_cv_bool_def; ARITH_RULE `1 = SUC 0`]);;


let candle_cv_fs_core_make_correct = prove
 (`!domain center hessian.
     candle_cv_fs_core_make (candle_cv_bool domain)
       (candle_cv_fs_first center) (candle_cv_fs_interval_matrix hessian) =
     candle_cv_fs_core (candle_fs_core_make domain center hessian)`,
  REWRITE_TAC[candle_cv_fs_core_def; candle_cv_fs_core_make_def;
              candle_fs_core_make_def; candle_fs_core_domain_def;
              candle_fs_core_center_def; candle_fs_core_hessian_def;
              FST; SND]);;


let candle_cv_fs_core_domain_correct = prove
 (`!core.
     candle_cv_fs_core_domain (candle_cv_fs_core core) =
     candle_cv_bool (candle_fs_core_domain core)`,
  REWRITE_TAC[candle_cv_fs_core_domain_def; candle_cv_fs_core_def;
              candle_cv_fs_core_make_def; cexp_fst_def]);;


let candle_cv_fs_core_center_correct = prove
 (`!core.
     candle_cv_fs_core_center (candle_cv_fs_core core) =
     candle_cv_fs_first (candle_fs_core_center core)`,
  REWRITE_TAC[candle_cv_fs_core_center_def; candle_cv_fs_core_def;
              candle_cv_fs_core_make_def; cexp_fst_def; cexp_snd_def]);;


let candle_cv_fs_core_hessian_correct = prove
 (`!core.
     candle_cv_fs_core_hessian (candle_cv_fs_core core) =
     candle_cv_fs_interval_matrix (candle_fs_core_hessian core)`,
  REWRITE_TAC[candle_cv_fs_core_hessian_def; candle_cv_fs_core_def;
              candle_cv_fs_core_make_def; cexp_snd_def]);;


let candle_cv_fs_core_force_correct = prove
 (`!radii core.
     candle_cv_fs_core_force
       (candle_cv_lc_vec radii) (candle_cv_fs_core core) =
     candle_cv_fs_result (candle_fs_core_force radii core)`,
  REWRITE_TAC[candle_cv_fs_core_force_def; candle_fs_core_force_def;
              candle_cv_fs_core_domain_correct;
              candle_cv_fs_core_center_correct;
              candle_cv_fs_core_hessian_correct;
              candle_cv_fs_result_complete_rounded_correct]);;


let candle_cv_fs_core_zero_correct = prove
 (`!dimensions.
     candle_cv_fs_core_zero (candle_cv_fs_interval_list dimensions) =
     candle_cv_fs_core (candle_fs_core_zero dimensions)`,
  REWRITE_TAC[candle_cv_fs_core_zero_def; candle_fs_core_zero_def;
              candle_cv_fs_core_bool_false;
              candle_cv_fs_interval_zero_correct;
              candle_cv_fs_interval_zeros_correct;
              candle_cv_fs_interval_zero_matrix_like_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_core_make_correct]);;


let candle_cv_fs_core_head_correct = prove
 (`!dimensions stack.
     candle_cv_fs_core_head (candle_cv_fs_interval_list dimensions)
       (candle_cv_fs_core_list stack) =
     candle_cv_fs_core (candle_fs_core_head dimensions stack)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_fs_core_head_def; candle_fs_core_head_def;
              candle_cv_fs_core_list_def; cexp_if_def; cexp_ispair_def;
              cexp_fst_def; candle_cv_fs_core_zero_correct]);;

let candle_cv_fs_core_tail_correct = prove
 (`!stack.
     candle_cv_fs_core_tail (candle_cv_fs_core_list stack) =
     candle_cv_fs_core_list (candle_fs_core_tail stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_fs_core_tail_def; candle_fs_core_tail_def;
              candle_cv_fs_core_list_def; cexp_if_def; cexp_ispair_def;
              cexp_snd_def]);;

let candle_cv_fs_core_constant_correct = prove
 (`!dimensions q.
     candle_cv_fs_core_constant
       (candle_cv_fs_interval_list dimensions) (candle_cv_q q) =
     candle_cv_fs_core (candle_fs_core_constant dimensions q)`,
  REWRITE_TAC[candle_cv_fs_core_constant_def;
              candle_fs_core_constant_def; candle_cv_fs_core_bool_true;
              candle_cv_fs_interval_constant_correct;
              candle_cv_fs_interval_zeros_correct;
              candle_cv_fs_interval_zero_matrix_like_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_core_make_correct]);;


let candle_cv_fs_core_variable_correct = prove
 (`!dimensions variable.
     candle_cv_fs_core_variable
       (candle_cv_fs_interval_list dimensions) (Cexp_num variable) =
     candle_cv_fs_core (candle_fs_core_variable dimensions variable)`,
  REWRITE_TAC[candle_cv_fs_core_variable_def;
              candle_fs_core_variable_def; candle_cv_fs_core_bool_true;
              candle_cv_fs_interval_lookup_correct;
              candle_cv_fs_interval_unit_correct;
              candle_cv_fs_interval_zero_matrix_like_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_core_make_correct]);;


let candle_cv_fs_core_neg_correct = prove
 (`!core.
     candle_cv_fs_core_neg (candle_cv_fs_core core) =
     candle_cv_fs_core (candle_fs_core_neg core)`,
  REWRITE_TAC[candle_cv_fs_core_neg_def; candle_fs_core_neg_def;
              candle_cv_fs_core_domain_correct;
              candle_cv_fs_core_center_correct;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fs_interval_neg_correct;
              candle_cv_fs_interval_list_neg_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_core_hessian_correct;
              candle_cv_fs_interval_matrix_neg_correct;
              candle_cv_fs_core_make_correct]);;


let candle_cv_fs_core_add_correct = prove
 (`!left right.
     candle_cv_fs_core_add
       (candle_cv_fs_core left) (candle_cv_fs_core right) =
     candle_cv_fs_core (candle_fs_core_add left right)`,
  REWRITE_TAC[candle_cv_fs_core_add_def; candle_fs_core_add_def;
              candle_cv_fs_core_domain_correct; candle_cv_bool_and_correct;
              candle_cv_fs_core_center_correct;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fs_interval_add_correct;
              candle_cv_fs_interval_list_add_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_core_hessian_correct;
              candle_cv_fs_interval_matrix_add_correct;
              candle_cv_fs_core_make_correct]);;


let candle_cv_fs_core_complete_raw_correct = prove
 (`!domain raw_center raw_hessian.
     candle_cv_fs_core_complete_raw
       (candle_cv_bool domain) (candle_cv_fs_first raw_center)
       (candle_cv_fs_interval_matrix raw_hessian) =
     candle_cv_fs_core
       (candle_fs_core_complete_raw domain raw_center raw_hessian)`,
  REWRITE_TAC[candle_cv_fs_core_complete_raw_def;
              candle_fs_core_complete_raw_def;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fs_scale_correct;
              candle_cv_fs_raw_interval_round_correct;
              candle_cv_fs_raw_interval_list_round_correct;
              candle_cv_fs_raw_interval_matrix_round_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_core_make_correct]);;


let candle_cv_fs_core_mul_full_correct = prove
 (`!left right.
     candle_cv_fs_core_mul_full
       (candle_cv_fs_result left) (candle_cv_fs_result right) =
     candle_cv_fs_core (candle_fs_core_mul_full left right)`,
  REWRITE_TAC[candle_cv_fs_core_mul_full_def; candle_fs_core_mul_full_def;
              candle_cv_fs_result_domain_correct; candle_cv_bool_and_correct;
              candle_cv_fs_result_center_correct;
              candle_cv_fs_first_value_correct;
              candle_cv_fs_first_gradient_correct;
              candle_cv_fs_raw_interval_mul_correct;
              candle_cv_fs_raw_interval_list_scale_correct;
              candle_cv_fs_raw_interval_list_add_correct;
              candle_cv_fs_first_make_correct;
              candle_cv_fs_result_value_bound_correct;
              candle_cv_fs_result_gradient_bounds_correct;
              candle_cv_fs_result_hessian_correct;
              candle_cv_fs_raw_interval_matrix_scale_correct;
              candle_cv_fs_raw_interval_outer_correct;
              candle_cv_fs_raw_interval_matrix_add_correct;
              candle_cv_fs_core_complete_raw_correct]);;


let candle_cv_fs_core_mul_correct = prove
 (`!radii left right.
     candle_cv_fs_core_mul (candle_cv_lc_vec radii)
       (candle_cv_fs_core left) (candle_cv_fs_core right) =
     candle_cv_fs_core (candle_fs_core_mul radii left right)`,
  REWRITE_TAC[candle_cv_fs_core_mul_def; candle_fs_core_mul_def;
              candle_cv_fs_core_force_correct;
              candle_cv_fs_core_mul_full_correct]);;


let candle_cv_fs_core_square_correct = prove
 (`!radii core.
     candle_cv_fs_core_square (candle_cv_lc_vec radii)
       (candle_cv_fs_core core) =
     candle_cv_fs_core (candle_fs_core_square radii core)`,
  REWRITE_TAC[candle_cv_fs_core_square_def;
              candle_cv_fs_core_square_full_def;
              candle_fs_core_square_def;
              candle_cv_fs_core_force_correct;
              candle_cv_fs_core_mul_full_correct]);;


let candle_cv_fs_poly_step_lazy_correct = prove
 (`!instruction dimensions radii stack.
     candle_cv_fs_poly_step_lazy
       (candle_cv_fs_interval_list dimensions)
       (candle_cv_lc_vec radii)
       (candle_cv_q_instruction instruction)
       (candle_cv_fs_core_list stack) =
     candle_cv_fs_core_list
       (candle_fs_poly_step_lazy dimensions radii instruction stack)`,
  MATCH_MP_TAC candle_q_instruction_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_poly_step_lazy_def;
              candle_fs_poly_step_lazy_def;
              candle_cv_q_instruction_def; candle_cv_fs_core_list_def;
              cexp_fst_def; cexp_snd_def; cexp_eq_def; cexp_if_def;
              cexp_ispair_def; distinctness "cval"; injectivity "cval";
              NOT_SUC; candle_one_ne_zero; candle_four_ne_two;
              candle_four_ne_three; candle_three_ne_two;
              candle_five_ne_two; candle_five_ne_three;
              candle_five_ne_four;
              candle_cv_fs_core_constant_correct;
              candle_cv_fs_core_variable_correct;
              candle_cv_fs_core_head_correct;
              candle_cv_fs_core_tail_correct;
              candle_cv_fs_core_neg_correct;
              candle_cv_fs_core_add_correct;
              candle_cv_fs_core_mul_correct;
              candle_cv_fs_core_square_correct]);;


let candle_cv_fs_poly_run_lazy_correct = prove
 (`!program dimensions radii stack.
     candle_cv_fs_poly_run_lazy
       (candle_cv_fs_interval_list dimensions)
       (candle_cv_lc_vec radii)
       (candle_cv_q_instruction_list program)
       (candle_cv_fs_core_list stack) =
     candle_cv_fs_core_list
       (candle_fs_poly_run_lazy dimensions radii program stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_instruction_list_def;
                  candle_cv_fs_poly_run_lazy_def;
                  candle_fs_poly_run_lazy_def;
                  candle_cv_fs_poly_step_lazy_correct]);;


let candle_cv_fs_poly_program_fixed_lazy_correct = prove
 (`!program dimensions radii.
     candle_cv_fs_poly_program_fixed_lazy
       (candle_cv_fs_interval_list dimensions)
       (candle_cv_lc_vec radii)
       (candle_cv_q_instruction_list program) =
     candle_cv_fs_result
       (candle_fs_poly_program_fixed_lazy dimensions radii program)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_poly_program_fixed_lazy_def;
              candle_fs_poly_program_fixed_lazy_def;
              GSYM candle_cv_fs_core_list_def;
              candle_cv_fs_poly_run_lazy_correct;
              candle_cv_fs_core_head_correct;
              candle_cv_fs_core_force_correct]);;


let candle_cv_fs_poly_program_lazy_correct = prove
 (`!program center_boxes radii.
     candle_cv_fs_poly_program_lazy
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction_list program) =
     candle_cv_fs_result
       (candle_fs_poly_program_lazy center_boxes radii program)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_poly_program_lazy_def;
              candle_fs_poly_program_lazy_def;
              candle_cv_fs_interval_list_of_q_correct;
              candle_cv_fs_list_of_q_correct;
              candle_cv_fs_poly_program_fixed_lazy_correct]);;


(* Exact logical relation at every force point. *)

let candle_fs_core_force_constant = prove
 (`!dimensions radii q.
     candle_fs_core_force radii (candle_fs_core_constant dimensions q) =
     candle_fs_result_constant dimensions radii q`,
  REWRITE_TAC[candle_fs_core_force_def; candle_fs_core_constant_def;
              candle_fs_result_constant_def; candle_fs_core_domain_def;
              candle_fs_core_center_def; candle_fs_core_hessian_def;
              candle_fs_core_make_def; FST; SND]);;


let candle_fs_core_force_variable = prove
 (`!dimensions radii variable.
     candle_fs_core_force radii
       (candle_fs_core_variable dimensions variable) =
     candle_fs_result_variable dimensions radii variable`,
  REWRITE_TAC[candle_fs_core_force_def; candle_fs_core_variable_def;
              candle_fs_result_variable_def; candle_fs_core_domain_def;
              candle_fs_core_center_def; candle_fs_core_hessian_def;
              candle_fs_core_make_def; FST; SND]);;


let candle_fs_core_force_neg = prove
 (`!radii core.
     candle_fs_core_force radii (candle_fs_core_neg core) =
     candle_fs_result_neg radii (candle_fs_core_force radii core)`,
  REWRITE_TAC[candle_fs_core_force_def; candle_fs_core_neg_def;
              candle_fs_result_neg_def; candle_fs_core_domain_def;
              candle_fs_core_center_def; candle_fs_core_hessian_def;
              candle_fs_core_make_def; candle_fs_result_complete_rounded_def;
              candle_fs_result_domain_def; candle_fs_result_center_def;
              candle_fs_result_hessian_def; candle_fs_result_make_def;
              FST; SND]);;


let candle_fs_core_force_add = prove
 (`!radii left right.
     candle_fs_core_force radii (candle_fs_core_add left right) =
     candle_fs_result_add radii
       (candle_fs_core_force radii left)
       (candle_fs_core_force radii right)`,
  REWRITE_TAC[candle_fs_core_force_def; candle_fs_core_add_def;
              candle_fs_result_add_def; candle_fs_core_domain_def;
              candle_fs_core_center_def; candle_fs_core_hessian_def;
              candle_fs_core_make_def; candle_fs_result_complete_rounded_def;
              candle_fs_result_domain_def; candle_fs_result_center_def;
              candle_fs_result_hessian_def; candle_fs_result_make_def;
              FST; SND]);;


let candle_fs_core_force_mul = prove
 (`!radii left right.
     candle_fs_core_force radii (candle_fs_core_mul radii left right) =
     candle_fs_result_mul radii
       (candle_fs_core_force radii left)
       (candle_fs_core_force radii right)`,
  REWRITE_TAC[candle_fs_core_force_def; candle_fs_core_mul_def;
              candle_fs_core_mul_full_def; candle_fs_core_complete_raw_def;
              candle_fs_result_mul_def; candle_fs_result_complete_raw_def;
              candle_fs_core_domain_def; candle_fs_core_center_def;
              candle_fs_core_hessian_def; candle_fs_core_make_def;
              FST; SND]);;


let candle_fs_core_force_square = prove
 (`!radii core.
     candle_fs_core_force radii (candle_fs_core_square radii core) =
     candle_fs_result_square radii (candle_fs_core_force radii core)`,
  REWRITE_TAC[candle_fs_core_force_def; candle_fs_core_square_def;
              candle_fs_core_mul_full_def; candle_fs_core_complete_raw_def;
              candle_fs_result_square_def; candle_fs_result_mul_def;
              candle_fs_result_complete_raw_def;
              candle_fs_core_domain_def; candle_fs_core_center_def;
              candle_fs_core_hessian_def; candle_fs_core_make_def;
              FST; SND]);;


let candle_fs_core_eval_def = define
 `(candle_fs_core_eval dimensions radii (Candle_poly_const p n d) =
     candle_fs_core_constant dimensions ((p,n),d)) /\
  (candle_fs_core_eval dimensions radii (Candle_poly_var variable) =
     candle_fs_core_variable dimensions variable) /\
  (candle_fs_core_eval dimensions radii (Candle_poly_neg expr) =
     candle_fs_core_neg (candle_fs_core_eval dimensions radii expr)) /\
  (candle_fs_core_eval dimensions radii (Candle_poly_add left right) =
     candle_fs_core_add
       (candle_fs_core_eval dimensions radii left)
       (candle_fs_core_eval dimensions radii right)) /\
  (candle_fs_core_eval dimensions radii (Candle_poly_mul left right) =
     candle_fs_core_mul radii
       (candle_fs_core_eval dimensions radii left)
       (candle_fs_core_eval dimensions radii right)) /\
  (candle_fs_core_eval dimensions radii (Candle_poly_square expr) =
     candle_fs_core_square radii
       (candle_fs_core_eval dimensions radii expr))`;;

let candle_fs_core_eval_force = prove
 (`!expr dimensions radii.
     candle_fs_core_force radii
       (candle_fs_core_eval dimensions radii expr) =
     candle_fs_poly_eval dimensions radii expr`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_fs_core_eval_def; candle_fs_poly_eval_def;
                  candle_fs_core_force_constant;
                  candle_fs_core_force_variable;
                  candle_fs_core_force_neg;
                  candle_fs_core_force_add;
                  candle_fs_core_force_mul;
                  candle_fs_core_force_square]);;


let candle_fs_poly_run_lazy_append = prove
 (`!left right dimensions radii stack.
     candle_fs_poly_run_lazy dimensions radii (APPEND left right) stack =
     candle_fs_poly_run_lazy dimensions radii right
       (candle_fs_poly_run_lazy dimensions radii left stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; candle_fs_poly_run_lazy_def]);;


let candle_fs_poly_compile_run_lazy = prove
 (`!expr dimensions radii stack.
     candle_fs_poly_run_lazy dimensions radii
       (candle_poly_compile expr) stack =
     CONS (candle_fs_core_eval dimensions radii expr) stack`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_fs_core_eval_def; candle_poly_compile_def;
                  candle_fs_poly_run_lazy_append;
                  candle_fs_poly_run_lazy_def;
                  candle_fs_poly_step_lazy_def;
                  candle_fs_core_head_def; candle_fs_core_tail_def;
                  APPEND]);;


let candle_fs_poly_program_fixed_lazy_compile = prove
 (`!expr dimensions radii.
     candle_fs_poly_program_fixed_lazy dimensions radii
       (candle_poly_compile expr) =
     candle_fs_poly_eval dimensions radii expr`,
  REWRITE_TAC[candle_fs_poly_program_fixed_lazy_def;
              candle_fs_poly_compile_run_lazy;
              candle_fs_core_head_def;
              candle_fs_core_eval_force]);;


let candle_cv_fs_poly_program_fixed_lazy_compile_correct = prove
 (`!expr dimensions radii.
     candle_cv_fs_poly_program_fixed_lazy
       (candle_cv_fs_interval_list dimensions)
       (candle_cv_lc_vec radii)
       (candle_cv_q_instruction_list (candle_poly_compile expr)) =
     candle_cv_fs_result (candle_fs_poly_eval dimensions radii expr)`,
  REWRITE_TAC[candle_cv_fs_poly_program_fixed_lazy_correct;
              candle_fs_poly_program_fixed_lazy_compile]);;


let candle_cv_fs_poly_program_lazy_compile_correct = prove
 (`!expr center_boxes radii.
     candle_cv_fs_poly_program_lazy
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction_list (candle_poly_compile expr)) =
     candle_cv_fs_result
       (candle_fs_poly_program center_boxes radii
         (candle_poly_compile expr))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_fs_poly_program_lazy_correct;
              candle_fs_poly_program_lazy_def;
              candle_fs_poly_program_def;
              candle_fs_poly_program_fixed_lazy_compile;
              candle_fs_poly_program_compile]);;


let candle_cv_fs_poly_program_lazy_compile_exact = prove
 (`!expr center_boxes radii.
     candle_cv_fs_poly_program_lazy
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction_list (candle_poly_compile expr)) =
     candle_cv_fs_poly_program
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_list radii)
       (candle_cv_q_instruction_list (candle_poly_compile expr))`,
  REWRITE_TAC[candle_cv_fs_poly_program_lazy_compile_correct;
              candle_cv_fs_poly_program_correct]);;

print_endline
  "CANDLE_CV_FIXED_SCALE_LAZY_COMPLETION_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
