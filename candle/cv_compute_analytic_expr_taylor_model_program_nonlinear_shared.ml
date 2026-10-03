(* ========================================================================== *)
(* Shared rational subexpressions in nonlinear Taylor-model instructions.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  These definitions name identical interval     *)
(* expressions that the established evaluator expands repeatedly.  The exact *)
(* equality theorems below are the authority for the candidate; no enclosure  *)
(* formula, rounding operation, or checker interface changes.                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer.ml";;

module Candle_cv_analytic_expr_taylor_model_program_nonlinear_shared = struct

open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_expr_first_jet_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;

let candle_cv_q_dim_analytic_first_jet_inv_shared_def = new_definition
 `candle_cv_q_dim_analytic_first_jet_inv_shared a =
    let r = candle_cv_q_interval_inv (candle_cv_q_dim_first_jet_f a) in
    let r2 = candle_cv_q_interval_mul_normalized r r in
    candle_cv_q_dim_first_jet_make r
      (candle_cv_q_dim_interval_list_scale
        (candle_cv_q_interval_neg r2)
        (candle_cv_q_dim_first_jet_gradient a))`;;

let candle_cv_q_dim_jet_inv_with_shared_def = new_definition
 `candle_cv_q_dim_jet_inv_with_shared r a =
    let r2 = candle_cv_q_interval_mul_normalized r r in
    let r3 = candle_cv_q_interval_mul_normalized r2 r in
    candle_cv_q_dim_jet_make r
      (candle_cv_q_dim_interval_list_scale
        (candle_cv_q_interval_neg r2)
        (candle_cv_q_dim_jet_gradient a))
      (candle_cv_q_dim_interval_matrix_add
        (candle_cv_q_dim_interval_matrix_scale
          (candle_cv_q_interval_neg r2)
          (candle_cv_q_dim_jet_hessian a))
        (candle_cv_q_dim_interval_matrix_scale
          (candle_cv_q_interval_add_normalized r3 r3)
          (candle_cv_q_dim_interval_outer
            (candle_cv_q_dim_jet_gradient a)
            (candle_cv_q_dim_jet_gradient a))))`;;

let candle_cv_q_dim_jet_inv_shared_def = new_definition
 `candle_cv_q_dim_jet_inv_shared a =
    candle_cv_q_dim_jet_inv_with_shared
      (candle_cv_q_interval_inv (candle_cv_q_dim_jet_f a)) a`;;

let candle_cv_q_dim_taylor_model_result_inv_shared_def = new_definition
 `candle_cv_q_dim_taylor_model_result_inv_shared radii result =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_bool_and
        (candle_cv_q_dim_taylor_model_result_domain result)
        (candle_cv_bool_and
          (candle_cv_q_dim_analytic_first_jet_inv_domain
            (candle_cv_q_dim_taylor_model_result_center result))
          (candle_cv_q_dim_jet_inv_domain
            (candle_cv_q_dim_taylor_model_proxy result))))
      (candle_cv_q_dim_analytic_first_jet_inv_shared
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_jet_inv_shared
          (candle_cv_q_dim_taylor_model_proxy result)))`;;

let candle_cv_q_dim_jet_sqrt_with_shared_def = new_definition
 `candle_cv_q_dim_jet_sqrt_with_shared s a =
    let two_s = candle_cv_q_interval_add_normalized s s in
    let two_f =
      candle_cv_q_interval_add_normalized
        (candle_cv_q_dim_jet_f a) (candle_cv_q_dim_jet_f a) in
    let d = candle_cv_q_interval_inv two_s in
    let dd =
      candle_cv_q_interval_neg
        (candle_cv_q_interval_inv
          (candle_cv_q_interval_mul_normalized two_s two_f)) in
    candle_cv_q_dim_jet_make s
      (candle_cv_q_dim_interval_list_scale d
        (candle_cv_q_dim_jet_gradient a))
      (candle_cv_q_dim_interval_matrix_add
        (candle_cv_q_dim_interval_matrix_scale dd
          (candle_cv_q_dim_interval_outer
            (candle_cv_q_dim_jet_gradient a)
            (candle_cv_q_dim_jet_gradient a)))
        (candle_cv_q_dim_interval_matrix_scale d
          (candle_cv_q_dim_jet_hessian a)))`;;

let candle_cv_q_dim_taylor_model_result_sqrt_shared_def = new_definition
 `candle_cv_q_dim_taylor_model_result_sqrt_shared
      radii center_s box_s result =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_bool_and
        (candle_cv_q_dim_taylor_model_result_domain result)
        (candle_cv_bool_and
          (candle_cv_q_dim_analytic_first_jet_sqrt_domain center_s
            (candle_cv_q_dim_taylor_model_result_center result))
          (candle_cv_q_dim_jet_sqrt_domain box_s
            (candle_cv_q_dim_taylor_model_proxy result))))
      (candle_cv_q_dim_analytic_first_jet_sqrt_with center_s
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_jet_sqrt_with_shared box_s
          (candle_cv_q_dim_taylor_model_proxy result)))`;;

let candle_cv_q_dim_jet_atn_with_shared_def = new_definition
 `candle_cv_q_dim_jet_atn_with_shared value_interval a =
    let input = candle_cv_q_dim_jet_f a in
    let d = candle_cv_q_dim_jet_atn_d input in
    let dd =
      candle_cv_q_interval_neg
        (candle_cv_q_interval_mul_normalized
          (candle_cv_q_interval_add_normalized input input)
          (candle_cv_q_interval_mul_normalized d d)) in
    candle_cv_q_dim_jet_make value_interval
      (candle_cv_q_dim_interval_list_scale d
        (candle_cv_q_dim_jet_gradient a))
      (candle_cv_q_dim_interval_matrix_add
        (candle_cv_q_dim_interval_matrix_scale dd
          (candle_cv_q_dim_interval_outer
            (candle_cv_q_dim_jet_gradient a)
            (candle_cv_q_dim_jet_gradient a)))
        (candle_cv_q_dim_interval_matrix_scale d
          (candle_cv_q_dim_jet_hessian a)))`;;

let candle_cv_q_dim_jet_atn_shared_def = new_definition
 `candle_cv_q_dim_jet_atn_shared a =
    candle_cv_q_dim_jet_atn_with_shared
      (candle_cv_q_interval_atn_range (candle_cv_q_dim_jet_f a)) a`;;

let candle_cv_q_dim_taylor_model_result_atn_shared_def = new_definition
 `candle_cv_q_dim_taylor_model_result_atn_shared radii result =
    candle_cv_q_dim_taylor_model_result_complete radii
      (candle_cv_bool_and
        (candle_cv_q_dim_taylor_model_result_domain result)
        (candle_cv_bool_and
          (candle_cv_q_dim_analytic_first_jet_atn_domain
            (candle_cv_q_dim_taylor_model_result_center result))
          (candle_cv_q_dim_jet_atn_domain
            (candle_cv_q_dim_taylor_model_proxy result))))
      (candle_cv_q_dim_analytic_first_jet_atn
        (candle_cv_q_dim_taylor_model_result_center result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_jet_atn_shared
          (candle_cv_q_dim_taylor_model_proxy result)))`;;

let candle_cv_fsa_item_sqrt_shared_def = new_definition
 `candle_cv_fsa_item_sqrt_shared
      radii center_certificate box_certificate item =
    candle_cv_fsa_item_q
      (candle_cv_q_dim_taylor_model_result_sqrt_shared radii
        center_certificate box_certificate
        (candle_cv_fsa_item_to_q item))`;;

let candle_cv_fsa_item_inv_shared_def = new_definition
 `candle_cv_fsa_item_inv_shared radii item =
    candle_cv_fsa_item_q
      (candle_cv_q_dim_taylor_model_result_inv_shared radii
        (candle_cv_fsa_item_to_q item))`;;

let candle_cv_fsa_item_atn_shared_def = new_definition
 `candle_cv_fsa_item_atn_shared radii item =
    candle_cv_fsa_item_q
      (candle_cv_q_dim_taylor_model_result_atn_shared radii
        (candle_cv_fsa_item_to_q item))`;;

let candle_cv_fso_program_step_nonlinear_shared_def = new_definition
 `candle_cv_fso_program_step_nonlinear_shared
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
                (candle_cv_fsa_item_sqrt_shared radii
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
                      (candle_cv_fsa_item_inv_shared radii
                        (candle_cv_fsa_item_head center_boxes boxes stack))
                      (candle_cv_fsa_item_tail stack))
                    (Cexp_if (Cexp_eq center_instruction (Cexp_num 7))
                      (Cexp_pair
                        (candle_cv_fsa_item_atn_shared radii
                          (candle_cv_fsa_item_head center_boxes boxes stack))
                        (candle_cv_fsa_item_tail stack))
                      (Cexp_if (Cexp_eq center_instruction (Cexp_num 8))
                        (Cexp_pair
                          (candle_cv_fsa_item_pi_half
                            radii center_boxes boxes) stack)
                        (Cexp_pair
                          (candle_cv_fsa_item_default center_boxes boxes)
                          stack))))))))
          (Cexp_pair
            (candle_cv_fsa_item_default center_boxes boxes) stack)))`;;

let candle_cv_q_dim_analytic_first_jet_inv_shared_exact = prove
 (`!a.
     candle_cv_q_dim_analytic_first_jet_inv_shared a =
     candle_cv_q_dim_analytic_first_jet_inv a`,
  REWRITE_TAC
    [candle_cv_q_dim_analytic_first_jet_inv_shared_def;
     candle_cv_q_dim_analytic_first_jet_inv_def; LET_DEF; LET_END_DEF]);;

let candle_cv_q_dim_jet_inv_with_shared_exact = prove
 (`!r a.
     candle_cv_q_dim_jet_inv_with_shared r a =
     candle_cv_q_dim_jet_inv_with r a`,
  REWRITE_TAC
    [candle_cv_q_dim_jet_inv_with_shared_def;
     candle_cv_q_dim_jet_inv_with_def; LET_DEF; LET_END_DEF]);;

let candle_cv_q_dim_jet_inv_shared_exact = prove
 (`!a. candle_cv_q_dim_jet_inv_shared a = candle_cv_q_dim_jet_inv a`,
  REWRITE_TAC
    [candle_cv_q_dim_jet_inv_shared_def; candle_cv_q_dim_jet_inv_def;
     candle_cv_q_dim_jet_inv_with_shared_exact]);;

let candle_cv_q_dim_taylor_model_result_inv_shared_exact = prove
 (`!radii result.
     candle_cv_q_dim_taylor_model_result_inv_shared radii result =
     candle_cv_q_dim_taylor_model_result_inv radii result`,
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_result_inv_shared_def;
     candle_cv_q_dim_taylor_model_result_inv_def;
     candle_cv_q_dim_analytic_first_jet_inv_shared_exact;
     candle_cv_q_dim_jet_inv_shared_exact]);;

let candle_cv_q_dim_jet_sqrt_with_shared_exact = prove
 (`!s a.
     candle_cv_q_dim_jet_sqrt_with_shared s a =
     candle_cv_q_dim_jet_sqrt_with s a`,
  REWRITE_TAC
    [candle_cv_q_dim_jet_sqrt_with_shared_def;
     candle_cv_q_dim_jet_sqrt_with_def;
     candle_cv_q_dim_jet_sqrt_d_def;
     candle_cv_q_dim_jet_sqrt_dd_def; LET_DEF; LET_END_DEF]);;

let candle_cv_q_dim_taylor_model_result_sqrt_shared_exact = prove
 (`!radii center_s box_s result.
     candle_cv_q_dim_taylor_model_result_sqrt_shared
       radii center_s box_s result =
     candle_cv_q_dim_taylor_model_result_sqrt
       radii center_s box_s result`,
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_result_sqrt_shared_def;
     candle_cv_q_dim_taylor_model_result_sqrt_def;
     candle_cv_q_dim_jet_sqrt_with_shared_exact]);;

let candle_cv_q_dim_jet_atn_with_shared_exact = prove
 (`!value_interval a.
     candle_cv_q_dim_jet_atn_with_shared value_interval a =
     candle_cv_q_dim_jet_atn_with value_interval a`,
  REWRITE_TAC
    [candle_cv_q_dim_jet_atn_with_shared_def;
     candle_cv_q_dim_jet_atn_with_def; candle_cv_q_dim_jet_atn_dd_def;
     LET_DEF; LET_END_DEF]);;

let candle_cv_q_dim_jet_atn_shared_exact = prove
 (`!a. candle_cv_q_dim_jet_atn_shared a = candle_cv_q_dim_jet_atn a`,
  REWRITE_TAC
    [candle_cv_q_dim_jet_atn_shared_def; candle_cv_q_dim_jet_atn_def;
     candle_cv_q_dim_jet_atn_with_shared_exact]);;

let candle_cv_q_dim_taylor_model_result_atn_shared_exact = prove
 (`!radii result.
     candle_cv_q_dim_taylor_model_result_atn_shared radii result =
     candle_cv_q_dim_taylor_model_result_atn radii result`,
  REWRITE_TAC
    [candle_cv_q_dim_taylor_model_result_atn_shared_def;
     candle_cv_q_dim_taylor_model_result_atn_def;
     candle_cv_q_dim_jet_atn_shared_exact]);;

let candle_cv_fsa_item_sqrt_shared_exact = prove
 (`!radii center_certificate box_certificate item.
     candle_cv_fsa_item_sqrt_shared
       radii center_certificate box_certificate item =
     candle_cv_fsa_item_sqrt
       radii center_certificate box_certificate item`,
  REWRITE_TAC
    [candle_cv_fsa_item_sqrt_shared_def; candle_cv_fsa_item_sqrt_def;
     candle_cv_q_dim_taylor_model_result_sqrt_shared_exact]);;

let candle_cv_fsa_item_inv_shared_exact = prove
 (`!radii item.
     candle_cv_fsa_item_inv_shared radii item =
     candle_cv_fsa_item_inv radii item`,
  REWRITE_TAC
    [candle_cv_fsa_item_inv_shared_def; candle_cv_fsa_item_inv_def;
     candle_cv_q_dim_taylor_model_result_inv_shared_exact]);;

let candle_cv_fsa_item_atn_shared_exact = prove
 (`!radii item.
     candle_cv_fsa_item_atn_shared radii item =
     candle_cv_fsa_item_atn radii item`,
  REWRITE_TAC
    [candle_cv_fsa_item_atn_shared_def; candle_cv_fsa_item_atn_def;
     candle_cv_q_dim_taylor_model_result_atn_shared_exact]);;

let candle_cv_fso_program_step_nonlinear_shared_exact = prove
 (`!center_boxes boxes radii center_instruction box_instruction stack.
     candle_cv_fso_program_step_nonlinear_shared
       center_boxes boxes radii center_instruction box_instruction stack =
     candle_cv_fso_program_step
       center_boxes boxes radii center_instruction box_instruction stack`,
  REWRITE_TAC
    [candle_cv_fso_program_step_nonlinear_shared_def;
     candle_cv_fso_program_step_def;
     candle_cv_fsa_item_sqrt_shared_exact;
     candle_cv_fsa_item_inv_shared_exact;
     candle_cv_fsa_item_atn_shared_exact]);;

let candle_cv_nonlinear_shared_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fso_compute_eqs
      (map SPEC_ALL
        [candle_cv_q_dim_analytic_first_jet_inv_shared_def;
         candle_cv_q_dim_jet_inv_with_shared_def;
         candle_cv_q_dim_jet_inv_shared_def;
         candle_cv_q_dim_taylor_model_result_inv_shared_def;
         candle_cv_q_dim_jet_sqrt_with_shared_def;
         candle_cv_q_dim_taylor_model_result_sqrt_shared_def;
         candle_cv_q_dim_jet_atn_with_shared_def;
         candle_cv_q_dim_jet_atn_shared_def;
         candle_cv_q_dim_taylor_model_result_atn_shared_def;
         candle_cv_fsa_item_sqrt_shared_def;
         candle_cv_fsa_item_inv_shared_def;
         candle_cv_fsa_item_atn_shared_def;
         candle_cv_fso_program_step_nonlinear_shared_def]));;

end;;
