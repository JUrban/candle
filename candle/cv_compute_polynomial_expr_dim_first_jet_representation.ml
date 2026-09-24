(* ========================================================================== *)
(* Representation correctness for the reflected first-order center jet.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This proves, for every encoded polynomial      *)
(* program and interval environment, that the Hessian-free evaluator returns *)
(* exactly the value/gradient projection of the proved second-order jet.      *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_first_jet_compute.ml";;
needs "candle/cv_compute_polynomial_expr_dim_jet_representation.ml";;

module Candle_cv_polynomial_expr_dim_first_jet_representation = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;

let candle_cv_q_dim_first_jet_encode_def = new_definition
 `candle_cv_q_dim_first_jet_encode jet =
    candle_cv_q_dim_first_jet_make
      (candle_cv_q_interval (candle_q_dim_jet_f jet))
      (candle_cv_q_interval_list (candle_q_dim_jet_gradient jet))`;;

let candle_cv_q_dim_first_jet_list_encode_def = define
 `(candle_cv_q_dim_first_jet_list_encode [] = Cexp_num 0) /\
  (candle_cv_q_dim_first_jet_list_encode (CONS h t) =
     Cexp_pair (candle_cv_q_dim_first_jet_encode h)
       (candle_cv_q_dim_first_jet_list_encode t))`;;

let candle_cv_q_dim_jet_first_projection_def = new_definition
 `candle_cv_q_dim_jet_first_projection jet =
    candle_cv_q_dim_first_jet_make
      (candle_cv_q_dim_jet_f jet)
      (candle_cv_q_dim_jet_gradient jet)`;;

let candle_cv_q_dim_first_jet_make_correct = prove
 (`!f gradient hessian.
     candle_cv_q_dim_first_jet_make
       (candle_cv_q_interval f)
       (candle_cv_q_interval_list gradient) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_make f gradient hessian)`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_make_def;
              candle_cv_q_dim_first_jet_encode_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def; FST; SND]);;

let candle_cv_q_dim_first_jet_f_correct = prove
 (`!jet.
     candle_cv_q_dim_first_jet_f
       (candle_cv_q_dim_first_jet_encode jet) =
     candle_cv_q_interval (candle_q_dim_jet_f jet)`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_f_def;
              candle_cv_q_dim_first_jet_encode_def;
              candle_cv_q_dim_first_jet_make_def; cexp_fst_def]);;

let candle_cv_q_dim_first_jet_gradient_correct = prove
 (`!jet.
     candle_cv_q_dim_first_jet_gradient
       (candle_cv_q_dim_first_jet_encode jet) =
     candle_cv_q_interval_list (candle_q_dim_jet_gradient jet)`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_gradient_def;
              candle_cv_q_dim_first_jet_encode_def;
              candle_cv_q_dim_first_jet_make_def; cexp_snd_def]);;

let candle_cv_q_dim_first_jet_zero_correct = prove
 (`!boxes.
     candle_cv_q_dim_first_jet_zero (candle_cv_q_interval_list boxes) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_normalized_zero boxes)`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_zero_def;
              candle_q_dim_jet_normalized_zero_def;
              candle_cv_q_dim_interval_zeros_correct;
              candle_cv_q_zero_interval_def;
              candle_cv_q_dim_first_jet_encode_def;
              candle_cv_q_dim_first_jet_make_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def; FST; SND]);;

let candle_cv_q_dim_first_jet_constant_correct = prove
 (`!boxes q.
     candle_cv_q_dim_first_jet_constant
       (candle_cv_q_interval_list boxes) (candle_cv_q q) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_normalized_constant boxes q)`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_constant_def;
              candle_q_dim_jet_normalized_constant_def;
              candle_cv_q_dim_interval_zeros_correct;
              candle_cv_q_dim_first_jet_encode_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def;
              candle_cv_q_dim_first_jet_make_def;
              candle_cv_q_interval_def; FST; SND]);;

let candle_cv_q_dim_first_jet_variable_correct = prove
 (`!boxes variable.
     candle_cv_q_dim_first_jet_variable
       (candle_cv_q_interval_list boxes) (Cexp_num variable) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_normalized_variable boxes variable)`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_variable_def;
              candle_q_dim_jet_normalized_variable_def;
              candle_cv_q_interval_lookup_correct;
              candle_cv_q_dim_interval_unit_correct;
              candle_cv_q_dim_first_jet_encode_def;
              candle_cv_q_dim_first_jet_make_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def; FST; SND]);;

let candle_cv_q_dim_first_jet_neg_correct = prove
 (`!a.
     candle_cv_q_dim_first_jet_neg
       (candle_cv_q_dim_first_jet_encode a) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_normalized_neg a)`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_neg_def;
              candle_q_dim_jet_normalized_neg_def;
              candle_cv_q_dim_first_jet_f_correct;
              candle_cv_q_dim_first_jet_gradient_correct;
              candle_cv_q_interval_neg_correct;
              candle_cv_q_dim_interval_list_neg_correct;
              candle_cv_q_dim_first_jet_encode_def;
              candle_cv_q_dim_first_jet_make_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def; FST; SND]);;

let candle_cv_q_dim_first_jet_add_correct = prove
 (`!a b.
     candle_cv_q_dim_first_jet_add
       (candle_cv_q_dim_first_jet_encode a)
       (candle_cv_q_dim_first_jet_encode b) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_normalized_add a b)`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_add_def;
              candle_q_dim_jet_normalized_add_def;
              candle_cv_q_dim_first_jet_f_correct;
              candle_cv_q_dim_first_jet_gradient_correct;
              candle_cv_q_interval_add_normalized_correct;
              candle_cv_q_dim_interval_list_add_correct;
              candle_cv_q_dim_first_jet_encode_def;
              candle_cv_q_dim_first_jet_make_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def; FST; SND]);;

let candle_cv_q_dim_first_jet_mul_correct = prove
 (`!a b.
     candle_cv_q_dim_first_jet_mul
       (candle_cv_q_dim_first_jet_encode a)
       (candle_cv_q_dim_first_jet_encode b) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_normalized_mul a b)`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_mul_def;
              candle_q_dim_jet_normalized_mul_def;
              candle_cv_q_dim_first_jet_f_correct;
              candle_cv_q_dim_first_jet_gradient_correct;
              candle_cv_q_interval_mul_normalized_correct;
              candle_cv_q_dim_interval_list_scale_correct;
              candle_cv_q_dim_interval_list_add_correct;
              candle_cv_q_dim_first_jet_encode_def;
              candle_cv_q_dim_first_jet_make_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def; FST; SND]);;

let candle_cv_q_dim_first_jet_head_correct = prove
 (`!boxes stack.
     candle_cv_q_dim_first_jet_head (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_first_jet_list_encode stack) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_normalized_head boxes stack)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_first_jet_head_def;
              candle_cv_q_dim_first_jet_list_encode_def;
              candle_q_dim_jet_normalized_head_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def;
              candle_cv_q_dim_first_jet_zero_correct]);;

let candle_cv_q_dim_first_jet_tail_correct = prove
 (`!stack.
     candle_cv_q_dim_first_jet_tail
       (candle_cv_q_dim_first_jet_list_encode stack) =
     candle_cv_q_dim_first_jet_list_encode
       (candle_q_dim_jet_normalized_tail stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_first_jet_tail_def;
              candle_cv_q_dim_first_jet_list_encode_def;
              candle_q_dim_jet_normalized_tail_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_q_dim_first_jet_step_correct = prove
 (`!instruction boxes stack.
     candle_cv_q_dim_first_jet_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction instruction)
       (candle_cv_q_dim_first_jet_list_encode stack) =
     candle_cv_q_dim_first_jet_list_encode
       (candle_q_dim_jet_normalized_step boxes instruction stack)`,
  MATCH_MP_TAC candle_q_instruction_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_first_jet_step_def;
              candle_q_dim_jet_normalized_step_def;
              candle_cv_q_instruction_def;
              candle_cv_q_dim_first_jet_list_encode_def;
              cexp_fst_def; cexp_snd_def; cexp_eq_def; cexp_if_def;
              cexp_ispair_def; distinctness "cval"; injectivity "cval";
              NOT_SUC; candle_one_ne_zero; candle_four_ne_two;
              candle_four_ne_three; candle_three_ne_two;
              candle_five_ne_two; candle_five_ne_three;
              candle_five_ne_four;
              candle_cv_q_dim_first_jet_constant_correct;
              candle_cv_q_dim_first_jet_variable_correct;
              candle_cv_q_dim_first_jet_head_correct;
              candle_cv_q_dim_first_jet_tail_correct;
              candle_cv_q_dim_first_jet_neg_correct;
              candle_cv_q_dim_first_jet_add_correct;
              candle_cv_q_dim_first_jet_mul_correct]);;

let candle_cv_q_dim_first_jet_run_correct = prove
 (`!program boxes stack.
     candle_cv_q_dim_first_jet_run
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list program)
       (candle_cv_q_dim_first_jet_list_encode stack) =
     candle_cv_q_dim_first_jet_list_encode
       (candle_q_dim_jet_normalized_run boxes program stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_instruction_list_def;
                  candle_cv_q_dim_first_jet_run_def;
                  candle_q_dim_jet_normalized_run_def;
                  candle_cv_q_dim_first_jet_step_correct]);;

let candle_cv_q_dim_first_jet_program_correct = prove
 (`!program boxes.
     candle_cv_q_dim_first_jet_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list program) =
     candle_cv_q_dim_first_jet_encode
       (candle_q_dim_jet_normalized_program boxes program)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_first_jet_program_def;
              candle_q_dim_jet_normalized_program_def;
              GSYM candle_cv_q_dim_first_jet_list_encode_def;
              candle_cv_q_dim_first_jet_run_correct;
              candle_cv_q_dim_first_jet_head_correct]);;

let candle_cv_q_dim_first_jet_encode_projection = prove
 (`!jet.
     candle_cv_q_dim_first_jet_encode jet =
     candle_cv_q_dim_jet_first_projection
       (candle_cv_q_dim_jet_encode jet)`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_encode_def;
              candle_cv_q_dim_jet_first_projection_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_dim_jet_gradient_correct]);;

let candle_cv_q_dim_first_jet_program_projection = prove
 (`!program boxes.
     candle_cv_q_dim_first_jet_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list program) =
     candle_cv_q_dim_jet_first_projection
       (candle_cv_q_dim_jet_program
         (candle_cv_q_interval_list boxes)
         (candle_cv_q_instruction_list program))`,
  REWRITE_TAC[candle_cv_q_dim_first_jet_program_correct;
              candle_cv_q_dim_jet_program_correct;
              candle_cv_q_dim_first_jet_encode_projection]);;

end;;
