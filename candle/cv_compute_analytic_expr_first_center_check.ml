(* ========================================================================== *)
(* Hessian-free center checking for reflected analytic shared jets.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The center evaluation computes only the value *)
(* and gradient.  The whole-box evaluation retains the Hessian needed by the  *)
(* existing universal analytic Taylor soundness theorem.                      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_check.ml";;
needs "candle/cv_compute_analytic_expr_first_jet_program_compute.ml";;

module Candle_cv_analytic_expr_first_center_check = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_check;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_first_jet_program_compute;;
open Candle_cv_analytic_expr_jet_check;;

let candle_cv_q_dim_analytic_first_center_upper_pair_def = new_definition
 `candle_cv_q_dim_analytic_first_center_upper_pair
      boxes center_result box_result =
    candle_cv_q_dim_taylor_upper
      (candle_cv_q_radius_list boxes)
      (candle_cv_q_dim_first_jet_f
        (candle_cv_q_dim_analytic_first_result_jet center_result))
      (candle_cv_q_dim_first_jet_gradient
        (candle_cv_q_dim_analytic_first_result_jet center_result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_analytic_result_jet box_result))`;;

let candle_cv_q_dim_analytic_first_center_finish_def = new_definition
 `candle_cv_q_dim_analytic_first_center_finish
      boxes center_result box_result =
    candle_cv_q_dim_whole_box_finish
      (candle_cv_bool_and
        (candle_cv_q_dim_analytic_first_result_domain center_result)
        (candle_cv_q_dim_analytic_result_domain box_result))
      (candle_cv_q_box_valid_list boxes)
      (candle_cv_q_dim_analytic_first_center_upper_pair
        boxes center_result box_result)`;;

let candle_cv_q_dim_analytic_first_center_check_def = new_definition
 `candle_cv_q_dim_analytic_first_center_check program boxes =
    candle_cv_q_dim_analytic_first_center_finish boxes
      (candle_cv_q_dim_analytic_first_program
        (candle_cv_q_center_environment_list boxes) program)
      (candle_cv_q_dim_analytic_program boxes program)`;;

let candle_cv_q_dim_analytic_first_center_upper_pair_correct = prove
 (`!boxes center_result box_result.
     candle_cv_q_dim_analytic_first_center_upper_pair
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_analytic_first_result_encode center_result)
       (candle_cv_q_dim_analytic_result_encode box_result) =
     candle_cv_q
       (candle_q_dim_jet_taylor_upper boxes
         (candle_q_dim_analytic_result_jet center_result)
         (candle_q_dim_analytic_result_jet box_result))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_first_center_upper_pair_def;
              candle_cv_q_dim_analytic_first_result_jet_correct;
              candle_cv_q_dim_analytic_result_jet_correct;
              candle_cv_q_radius_list_correct;
              candle_cv_q_dim_first_jet_f_correct;
              candle_cv_q_dim_first_jet_gradient_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_dim_taylor_upper_correct;
              candle_q_dim_jet_taylor_upper_def]);;

let candle_cv_q_dim_analytic_first_center_finish_correct = prove
 (`!boxes center_result box_result.
     candle_cv_q_dim_analytic_first_center_finish
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_analytic_first_result_encode center_result)
       (candle_cv_q_dim_analytic_result_encode box_result) =
     Cexp_pair
       (Cexp_num
         (if candle_q_box_valid_list boxes /\
             candle_q_dim_analytic_result_domain center_result /\
             candle_q_dim_analytic_result_domain box_result /\
             ~(candle_q_le candle_q_zero
                (candle_q_dim_jet_taylor_upper boxes
                  (candle_q_dim_analytic_result_jet center_result)
                  (candle_q_dim_analytic_result_jet box_result)))
          then SUC 0 else 0))
       (candle_cv_q
         (candle_q_dim_jet_taylor_upper boxes
           (candle_q_dim_analytic_result_jet center_result)
           (candle_q_dim_analytic_result_jet box_result)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_first_center_finish_def;
              candle_cv_q_dim_analytic_first_result_domain_correct;
              candle_cv_q_dim_analytic_result_domain_correct;
              candle_cv_bool_and_correct;
              candle_cv_bool_def;
              candle_cv_bool_and_def;
              candle_cv_q_box_valid_list_correct;
              candle_cv_q_dim_analytic_first_center_upper_pair_correct;
              candle_cv_q_dim_whole_box_finish_def;
              candle_cv_q_zero_def; candle_cv_q_le_correct;
              cexp_if_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_dim_analytic_first_center_check_correct = prove
 (`!e boxes.
     candle_cv_q_dim_analytic_first_center_check
       (candle_cv_analytic_instruction_list (candle_analytic_compile e))
       (candle_cv_q_interval_list boxes) =
     Cexp_pair
       (Cexp_num
         (if candle_q_dim_analytic_jet_whole_box_numerical_accept e boxes
          then SUC 0 else 0))
       (candle_cv_q (candle_q_dim_analytic_jet_whole_box_upper e boxes))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_analytic_first_center_check_def;
              candle_cv_q_center_environment_list_correct;
              candle_cv_q_dim_analytic_first_compile_program_correct;
              candle_cv_q_dim_analytic_compile_program_correct;
              candle_cv_q_dim_analytic_first_center_finish_correct;
              candle_q_dim_analytic_result_domain_def;
              candle_q_dim_analytic_result_jet_def;
              candle_q_dim_analytic_jet_whole_box_numerical_accept_def;
              candle_q_dim_analytic_jet_whole_box_upper_def]);;

let candle_cv_q_dim_analytic_first_center_compute_eqs =
  union candle_cv_q_dim_analytic_first_program_compute_eqs
    candle_cv_q_dim_analytic_jet_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_dim_analytic_first_center_upper_pair_def;
    candle_cv_q_dim_analytic_first_center_finish_def;
    candle_cv_q_dim_analytic_first_center_check_def];;

end;;
