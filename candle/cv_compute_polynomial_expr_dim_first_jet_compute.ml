(* ========================================================================== *)
(* Reflected first-order interval jets for polynomial center evaluation.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The whole-box Taylor checker needs only the   *)
(* value and gradient from its center traversal.  This evaluator preserves   *)
(* those two components while avoiding construction of the center Hessian;   *)
(* the second-order box traversal still supplies the latter where needed.    *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_jet_compute.ml";;

module Candle_cv_polynomial_expr_dim_first_jet_compute = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet_compute;;

(* A first-order jet is (value,gradient). *)

let candle_cv_q_dim_first_jet_make_def = new_definition
 `candle_cv_q_dim_first_jet_make f gradient = Cexp_pair f gradient`;;

let candle_cv_q_dim_first_jet_f_def = new_definition
 `candle_cv_q_dim_first_jet_f jet = Cexp_fst jet`;;

let candle_cv_q_dim_first_jet_gradient_def = new_definition
 `candle_cv_q_dim_first_jet_gradient jet = Cexp_snd jet`;;

let candle_cv_q_dim_first_jet_zero_def = new_definition
 `candle_cv_q_dim_first_jet_zero boxes =
    candle_cv_q_dim_first_jet_make candle_cv_q_zero_interval
      (candle_cv_q_dim_interval_zeros boxes)`;;

let candle_cv_q_dim_first_jet_constant_def = new_definition
 `candle_cv_q_dim_first_jet_constant boxes q =
    candle_cv_q_dim_first_jet_make (Cexp_pair q q)
      (candle_cv_q_dim_interval_zeros boxes)`;;

let candle_cv_q_dim_first_jet_variable_def = new_definition
 `candle_cv_q_dim_first_jet_variable boxes variable =
    candle_cv_q_dim_first_jet_make
      (candle_cv_q_interval_lookup variable boxes)
      (candle_cv_q_dim_interval_unit variable boxes)`;;

let candle_cv_q_dim_first_jet_neg_def = new_definition
 `candle_cv_q_dim_first_jet_neg a =
    candle_cv_q_dim_first_jet_make
      (candle_cv_q_interval_neg (candle_cv_q_dim_first_jet_f a))
      (candle_cv_q_dim_interval_list_neg
        (candle_cv_q_dim_first_jet_gradient a))`;;

let candle_cv_q_dim_first_jet_add_def = new_definition
 `candle_cv_q_dim_first_jet_add a b =
    candle_cv_q_dim_first_jet_make
      (candle_cv_q_interval_add_normalized
        (candle_cv_q_dim_first_jet_f a)
        (candle_cv_q_dim_first_jet_f b))
      (candle_cv_q_dim_interval_list_add
        (candle_cv_q_dim_first_jet_gradient a)
        (candle_cv_q_dim_first_jet_gradient b))`;;

let candle_cv_q_dim_first_jet_mul_def = new_definition
 `candle_cv_q_dim_first_jet_mul a b =
    candle_cv_q_dim_first_jet_make
      (candle_cv_q_interval_mul_normalized
        (candle_cv_q_dim_first_jet_f a)
        (candle_cv_q_dim_first_jet_f b))
      (candle_cv_q_dim_interval_list_add
        (candle_cv_q_dim_interval_list_scale
          (candle_cv_q_dim_first_jet_f b)
          (candle_cv_q_dim_first_jet_gradient a))
        (candle_cv_q_dim_interval_list_scale
          (candle_cv_q_dim_first_jet_f a)
          (candle_cv_q_dim_first_jet_gradient b)))`;;

let candle_cv_q_dim_first_jet_head_def = new_definition
 `candle_cv_q_dim_first_jet_head boxes stack =
    Cexp_if (Cexp_ispair stack) (Cexp_fst stack)
      (candle_cv_q_dim_first_jet_zero boxes)`;;

let candle_cv_q_dim_first_jet_tail_def = new_definition
 `candle_cv_q_dim_first_jet_tail stack =
    Cexp_if (Cexp_ispair stack) (Cexp_snd stack) (Cexp_num 0)`;;

let candle_cv_q_dim_first_jet_step_def = new_definition
 `candle_cv_q_dim_first_jet_step boxes instruction stack =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
        (Cexp_pair
          (candle_cv_q_dim_first_jet_constant
            boxes (Cexp_snd instruction)) stack)
        (Cexp_pair
          (candle_cv_q_dim_first_jet_variable
            boxes (Cexp_snd instruction)) stack))
      (Cexp_if (Cexp_eq instruction (Cexp_num 2))
        (Cexp_pair
          (candle_cv_q_dim_first_jet_neg
            (candle_cv_q_dim_first_jet_head boxes stack))
          (candle_cv_q_dim_first_jet_tail stack))
        (Cexp_if (Cexp_eq instruction (Cexp_num 3))
          (Cexp_pair
            (candle_cv_q_dim_first_jet_add
              (candle_cv_q_dim_first_jet_head boxes
                (candle_cv_q_dim_first_jet_tail stack))
              (candle_cv_q_dim_first_jet_head boxes stack))
            (candle_cv_q_dim_first_jet_tail
              (candle_cv_q_dim_first_jet_tail stack)))
          (Cexp_if (Cexp_eq instruction (Cexp_num 4))
            (Cexp_pair
              (candle_cv_q_dim_first_jet_mul
                (candle_cv_q_dim_first_jet_head boxes
                  (candle_cv_q_dim_first_jet_tail stack))
                (candle_cv_q_dim_first_jet_head boxes stack))
              (candle_cv_q_dim_first_jet_tail
                (candle_cv_q_dim_first_jet_tail stack)))
            (Cexp_pair
              (candle_cv_q_dim_first_jet_mul
                (candle_cv_q_dim_first_jet_head boxes stack)
                (candle_cv_q_dim_first_jet_head boxes stack))
              (candle_cv_q_dim_first_jet_tail stack)))))`;;

let candle_cv_q_dim_first_jet_run_def = define
 `(candle_cv_q_dim_first_jet_run boxes (Cexp_num z) stack = stack) /\
  (candle_cv_q_dim_first_jet_run boxes (Cexp_pair h t) stack =
     candle_cv_q_dim_first_jet_run boxes t
       (candle_cv_q_dim_first_jet_step boxes h stack))`;;

let candle_cv_q_dim_first_jet_run_compute = prove
 (`!boxes program stack.
     candle_cv_q_dim_first_jet_run boxes program stack =
     Cexp_if (Cexp_ispair program)
       (candle_cv_q_dim_first_jet_run boxes (Cexp_snd program)
         (candle_cv_q_dim_first_jet_step
           boxes (Cexp_fst program) stack))
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_first_jet_run_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_first_jet_program_def = new_definition
 `candle_cv_q_dim_first_jet_program boxes program =
    candle_cv_q_dim_first_jet_head boxes
      (candle_cv_q_dim_first_jet_run boxes program (Cexp_num 0))`;;

let candle_cv_q_dim_first_jet_taylor_upper_def = new_definition
 `candle_cv_q_dim_first_jet_taylor_upper radii center_jet box_jet =
    candle_cv_q_dim_taylor_upper_normalized radii
      (candle_cv_q_dim_first_jet_f center_jet)
      (candle_cv_q_dim_first_jet_gradient center_jet)
      (candle_cv_q_dim_jet_hessian box_jet)`;;

let candle_cv_q_dim_first_jet_whole_box_upper_def = new_definition
 `candle_cv_q_dim_first_jet_whole_box_upper program boxes =
    candle_cv_q_dim_first_jet_taylor_upper
      (candle_cv_q_radius_list boxes)
      (candle_cv_q_dim_first_jet_program
        (candle_cv_q_center_environment_list boxes) program)
      (candle_cv_q_dim_jet_program boxes program)`;;

let candle_cv_q_dim_first_jet_whole_box_check_def = new_definition
 `candle_cv_q_dim_first_jet_whole_box_check program boxes =
    candle_cv_q_dim_whole_box_finish (Cexp_num 1)
      (candle_cv_q_box_valid_list boxes)
      (candle_cv_q_dim_first_jet_whole_box_upper program boxes)`;;

let candle_cv_q_dim_first_jet_compute_eqs =
  candle_cv_q_dim_jet_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_dim_first_jet_make_def;
    candle_cv_q_dim_first_jet_f_def;
    candle_cv_q_dim_first_jet_gradient_def;
    candle_cv_q_dim_first_jet_zero_def;
    candle_cv_q_dim_first_jet_constant_def;
    candle_cv_q_dim_first_jet_variable_def;
    candle_cv_q_dim_first_jet_neg_def;
    candle_cv_q_dim_first_jet_add_def;
    candle_cv_q_dim_first_jet_mul_def;
    candle_cv_q_dim_first_jet_head_def;
    candle_cv_q_dim_first_jet_tail_def;
    candle_cv_q_dim_first_jet_step_def;
    candle_cv_q_dim_first_jet_run_compute;
    candle_cv_q_dim_first_jet_program_def;
    candle_cv_q_dim_first_jet_taylor_upper_def;
    candle_cv_q_dim_first_jet_whole_box_upper_def;
    candle_cv_q_dim_first_jet_whole_box_check_def];;

end;;
