(* ========================================================================== *)
(* Reflected execution for dimension-generic interval jets.                    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This evaluator traverses one compact postfix   *)
(* program and carries value, gradient, and Hessian data.  The ordinary HOL   *)
(* algorithm and source soundness theorem live in                              *)
(* [cv_compute_polynomial_expr_dim_jet.ml].  Representation correctness for   *)
(* this cval layer is deliberately a separate required theorem.                *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_jet.ml";;
needs "candle/cv_compute_whole_box_dim_taylor.ml";;
needs "candle/cv_compute_exact_rational_normalize.ml";;

module Candle_cv_polynomial_expr_dim_jet_compute = struct

open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_jet;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_exact_rational_normalize;;

let candle_cv_q_interval_add_normalized_def = new_definition
 `candle_cv_q_interval_add_normalized x y =
    candle_cv_q_interval_normalize (candle_cv_q_interval_add x y)`;;

let candle_cv_q_interval_mul_normalized_def = new_definition
 `candle_cv_q_interval_mul_normalized x y =
    candle_cv_q_interval_normalize (candle_cv_q_interval_mul x y)`;;

let candle_cv_q_list_normalize_def = define
 `(candle_cv_q_list_normalize (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_list_normalize (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_normalize h)
       (candle_cv_q_list_normalize t))`;;

let candle_cv_q_interval_list_normalize_def = define
 `(candle_cv_q_interval_list_normalize (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_interval_list_normalize (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_interval_normalize h)
       (candle_cv_q_interval_list_normalize t))`;;

let candle_cv_q_list_normalize_compute = prove
 (`!items.
     candle_cv_q_list_normalize items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair (candle_cv_q_normalize (Cexp_fst items))
         (candle_cv_q_list_normalize (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_list_normalize_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_interval_list_normalize_compute = prove
 (`!items.
     candle_cv_q_interval_list_normalize items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair (candle_cv_q_interval_normalize (Cexp_fst items))
         (candle_cv_q_interval_list_normalize (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_interval_list_normalize_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_jet_make_def = new_definition
 `candle_cv_q_dim_jet_make f gradient hessian =
    Cexp_pair f (Cexp_pair gradient hessian)`;;

let candle_cv_q_dim_jet_f_def = new_definition
 `candle_cv_q_dim_jet_f jet = Cexp_fst jet`;;

let candle_cv_q_dim_jet_gradient_def = new_definition
 `candle_cv_q_dim_jet_gradient jet = Cexp_fst (Cexp_snd jet)`;;

let candle_cv_q_dim_jet_hessian_def = new_definition
 `candle_cv_q_dim_jet_hessian jet = Cexp_snd (Cexp_snd jet)`;;

(* Dimensions are represented by the box-list spine.  All malformed numeric  *)
(* data fail closed to an empty/zero structure.                                *)

let candle_cv_q_dim_interval_zeros_def = define
 `(candle_cv_q_dim_interval_zeros (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_dim_interval_zeros (Cexp_pair h t) =
     Cexp_pair candle_cv_q_zero_interval
       (candle_cv_q_dim_interval_zeros t))`;;

let candle_cv_q_dim_interval_unit_def = define
 `(candle_cv_q_dim_interval_unit (Cexp_num n) (Cexp_num z) = Cexp_num 0) /\
  (candle_cv_q_dim_interval_unit (Cexp_pair p q) (Cexp_num z) = Cexp_num 0) /\
  (candle_cv_q_dim_interval_unit (Cexp_num 0) (Cexp_pair h t) =
     Cexp_pair candle_cv_q_one_interval
       (candle_cv_q_dim_interval_zeros t)) /\
  (candle_cv_q_dim_interval_unit (Cexp_num (SUC n)) (Cexp_pair h t) =
     Cexp_pair candle_cv_q_zero_interval
       (candle_cv_q_dim_interval_unit (Cexp_num n) t)) /\
  (candle_cv_q_dim_interval_unit (Cexp_pair p q) (Cexp_pair h t) =
     candle_cv_q_dim_interval_zeros (Cexp_pair h t))`;;

let candle_cv_q_dim_interval_zero_matrix_def = define
 `(candle_cv_q_dim_interval_zero_matrix width (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_dim_interval_zero_matrix width (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_dim_interval_zeros width)
       (candle_cv_q_dim_interval_zero_matrix width t))`;;

let candle_cv_q_dim_interval_list_neg_def = define
 `(candle_cv_q_dim_interval_list_neg (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_dim_interval_list_neg (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_interval_neg h)
       (candle_cv_q_dim_interval_list_neg t))`;;

let candle_cv_q_dim_interval_list_add_def = define
 `(candle_cv_q_dim_interval_list_add (Cexp_num n) ys = Cexp_num 0) /\
  (candle_cv_q_dim_interval_list_add (Cexp_pair x xs) (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_q_dim_interval_list_add
     (Cexp_pair x xs) (Cexp_pair y ys) =
     Cexp_pair (candle_cv_q_interval_add_normalized x y)
       (candle_cv_q_dim_interval_list_add xs ys))`;;

let candle_cv_q_dim_interval_list_scale_def = define
 `(candle_cv_q_dim_interval_list_scale q (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_dim_interval_list_scale q (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_interval_mul_normalized q h)
       (candle_cv_q_dim_interval_list_scale q t))`;;

let candle_cv_q_dim_interval_matrix_neg_def = define
 `(candle_cv_q_dim_interval_matrix_neg (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_dim_interval_matrix_neg (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_dim_interval_list_neg h)
       (candle_cv_q_dim_interval_matrix_neg t))`;;

let candle_cv_q_dim_interval_matrix_add_def = define
 `(candle_cv_q_dim_interval_matrix_add (Cexp_num n) ys = Cexp_num 0) /\
  (candle_cv_q_dim_interval_matrix_add (Cexp_pair x xs) (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_q_dim_interval_matrix_add
     (Cexp_pair x xs) (Cexp_pair y ys) =
     Cexp_pair (candle_cv_q_dim_interval_list_add x y)
       (candle_cv_q_dim_interval_matrix_add xs ys))`;;

let candle_cv_q_dim_interval_matrix_scale_def = define
 `(candle_cv_q_dim_interval_matrix_scale q (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_q_dim_interval_matrix_scale q (Cexp_pair h t) =
     Cexp_pair (candle_cv_q_dim_interval_list_scale q h)
       (candle_cv_q_dim_interval_matrix_scale q t))`;;

let candle_cv_q_dim_interval_outer_def = define
 `(candle_cv_q_dim_interval_outer (Cexp_num n) ys = Cexp_num 0) /\
  (candle_cv_q_dim_interval_outer (Cexp_pair x xs) ys =
     Cexp_pair (candle_cv_q_dim_interval_list_scale x ys)
       (candle_cv_q_dim_interval_outer xs ys))`;;

let candle_cv_q_dim_interval_zeros_compute = prove
 (`!items.
     candle_cv_q_dim_interval_zeros items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair candle_cv_q_zero_interval
         (candle_cv_q_dim_interval_zeros (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_interval_zeros_def; cexp_if_def;
              cexp_ispair_def; cexp_snd_def]);;

let candle_cv_q_dim_interval_unit_compute = prove
 (`!variable boxes.
     candle_cv_q_dim_interval_unit variable boxes =
     Cexp_if (Cexp_ispair boxes)
       (Cexp_if (Cexp_ispair variable)
         (candle_cv_q_dim_interval_zeros boxes)
         (Cexp_if (Cexp_eq variable (Cexp_num 0))
           (Cexp_pair candle_cv_q_one_interval
             (candle_cv_q_dim_interval_zeros (Cexp_snd boxes)))
           (Cexp_pair candle_cv_q_zero_interval
             (candle_cv_q_dim_interval_unit
               (Cexp_sub variable (Cexp_num 1)) (Cexp_snd boxes)))))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `boxes:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `variable:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_interval_unit_def; cexp_if_def;
              cexp_ispair_def; cexp_snd_def] THEN
  MP_TAC (SPEC `a:num` num_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
  REWRITE_TAC[candle_cv_q_dim_interval_unit_def; cexp_eq_def;
              cexp_if_def; cexp_sub_def; injectivity "cval";
              injectivity "num"; NOT_SUC;
              ARITH_RULE `SUC n - 1 = n`] THEN
  ARITH_TAC);;

let candle_cv_q_dim_interval_zero_matrix_compute = prove
 (`!width row_lists.
     candle_cv_q_dim_interval_zero_matrix width row_lists =
     Cexp_if (Cexp_ispair row_lists)
       (Cexp_pair (candle_cv_q_dim_interval_zeros width)
         (candle_cv_q_dim_interval_zero_matrix width (Cexp_snd row_lists)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_interval_zero_matrix_def; cexp_if_def;
              cexp_ispair_def; cexp_snd_def]);;

let candle_cv_q_dim_interval_list_neg_compute = prove
 (`!items.
     candle_cv_q_dim_interval_list_neg items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair (candle_cv_q_interval_neg (Cexp_fst items))
         (candle_cv_q_dim_interval_list_neg (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_interval_list_neg_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_interval_list_add_compute = prove
 (`!xs ys.
     candle_cv_q_dim_interval_list_add xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_if (Cexp_ispair ys)
         (Cexp_pair
           (candle_cv_q_interval_add_normalized
             (Cexp_fst xs) (Cexp_fst ys))
           (candle_cv_q_dim_interval_list_add
             (Cexp_snd xs) (Cexp_snd ys)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `ys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_interval_list_add_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_interval_list_scale_compute = prove
 (`!q items.
     candle_cv_q_dim_interval_list_scale q items =
     Cexp_if (Cexp_ispair items)
       (Cexp_pair
         (candle_cv_q_interval_mul_normalized q (Cexp_fst items))
         (candle_cv_q_dim_interval_list_scale q (Cexp_snd items)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_interval_list_scale_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_interval_matrix_neg_compute = prove
 (`!row_lists.
     candle_cv_q_dim_interval_matrix_neg row_lists =
     Cexp_if (Cexp_ispair row_lists)
       (Cexp_pair
         (candle_cv_q_dim_interval_list_neg (Cexp_fst row_lists))
         (candle_cv_q_dim_interval_matrix_neg (Cexp_snd row_lists)))
       (Cexp_num 0)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_interval_matrix_neg_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_interval_matrix_add_compute = prove
 (`!xs ys.
     candle_cv_q_dim_interval_matrix_add xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_if (Cexp_ispair ys)
         (Cexp_pair
           (candle_cv_q_dim_interval_list_add (Cexp_fst xs) (Cexp_fst ys))
           (candle_cv_q_dim_interval_matrix_add
             (Cexp_snd xs) (Cexp_snd ys)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `ys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_interval_matrix_add_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_interval_matrix_scale_compute = prove
 (`!q row_lists.
     candle_cv_q_dim_interval_matrix_scale q row_lists =
     Cexp_if (Cexp_ispair row_lists)
       (Cexp_pair
         (candle_cv_q_dim_interval_list_scale q (Cexp_fst row_lists))
         (candle_cv_q_dim_interval_matrix_scale q (Cexp_snd row_lists)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_interval_matrix_scale_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_interval_outer_compute = prove
 (`!xs ys.
     candle_cv_q_dim_interval_outer xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_pair
         (candle_cv_q_dim_interval_list_scale (Cexp_fst xs) ys)
         (candle_cv_q_dim_interval_outer (Cexp_snd xs) ys))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_interval_outer_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_jet_zero_def = new_definition
 `candle_cv_q_dim_jet_zero boxes =
    candle_cv_q_dim_jet_make candle_cv_q_zero_interval
      (candle_cv_q_dim_interval_zeros boxes)
      (candle_cv_q_dim_interval_zero_matrix boxes boxes)`;;

let candle_cv_q_dim_jet_constant_def = new_definition
 `candle_cv_q_dim_jet_constant boxes q =
    candle_cv_q_dim_jet_make (Cexp_pair q q)
      (candle_cv_q_dim_interval_zeros boxes)
      (candle_cv_q_dim_interval_zero_matrix boxes boxes)`;;

let candle_cv_q_dim_jet_variable_def = new_definition
 `candle_cv_q_dim_jet_variable boxes variable =
    candle_cv_q_dim_jet_make
      (candle_cv_q_interval_lookup variable boxes)
      (candle_cv_q_dim_interval_unit variable boxes)
      (candle_cv_q_dim_interval_zero_matrix boxes boxes)`;;

let candle_cv_q_dim_jet_neg_def = new_definition
 `candle_cv_q_dim_jet_neg a =
    candle_cv_q_dim_jet_make
      (candle_cv_q_interval_neg (candle_cv_q_dim_jet_f a))
      (candle_cv_q_dim_interval_list_neg
        (candle_cv_q_dim_jet_gradient a))
      (candle_cv_q_dim_interval_matrix_neg
        (candle_cv_q_dim_jet_hessian a))`;;

let candle_cv_q_dim_jet_add_def = new_definition
 `candle_cv_q_dim_jet_add a b =
    candle_cv_q_dim_jet_make
      (candle_cv_q_interval_add_normalized
        (candle_cv_q_dim_jet_f a) (candle_cv_q_dim_jet_f b))
      (candle_cv_q_dim_interval_list_add
        (candle_cv_q_dim_jet_gradient a)
        (candle_cv_q_dim_jet_gradient b))
      (candle_cv_q_dim_interval_matrix_add
        (candle_cv_q_dim_jet_hessian a)
        (candle_cv_q_dim_jet_hessian b))`;;

let candle_cv_q_dim_jet_mul_def = new_definition
 `candle_cv_q_dim_jet_mul a b =
    candle_cv_q_dim_jet_make
      (candle_cv_q_interval_mul_normalized
        (candle_cv_q_dim_jet_f a) (candle_cv_q_dim_jet_f b))
      (candle_cv_q_dim_interval_list_add
        (candle_cv_q_dim_interval_list_scale
          (candle_cv_q_dim_jet_f b)
          (candle_cv_q_dim_jet_gradient a))
        (candle_cv_q_dim_interval_list_scale
          (candle_cv_q_dim_jet_f a)
          (candle_cv_q_dim_jet_gradient b)))
      (candle_cv_q_dim_interval_matrix_add
        (candle_cv_q_dim_interval_matrix_add
          (candle_cv_q_dim_interval_matrix_scale
            (candle_cv_q_dim_jet_f b)
            (candle_cv_q_dim_jet_hessian a))
          (candle_cv_q_dim_interval_outer
            (candle_cv_q_dim_jet_gradient a)
            (candle_cv_q_dim_jet_gradient b)))
        (candle_cv_q_dim_interval_matrix_add
          (candle_cv_q_dim_interval_outer
            (candle_cv_q_dim_jet_gradient b)
            (candle_cv_q_dim_jet_gradient a))
          (candle_cv_q_dim_interval_matrix_scale
            (candle_cv_q_dim_jet_f a)
            (candle_cv_q_dim_jet_hessian b))))`;;

let candle_cv_q_dim_jet_head_def = new_definition
 `candle_cv_q_dim_jet_head boxes stack =
    Cexp_if (Cexp_ispair stack) (Cexp_fst stack)
      (candle_cv_q_dim_jet_zero boxes)`;;

let candle_cv_q_dim_jet_tail_def = new_definition
 `candle_cv_q_dim_jet_tail stack =
    Cexp_if (Cexp_ispair stack) (Cexp_snd stack) (Cexp_num 0)`;;

let candle_cv_q_dim_jet_step_def = new_definition
 `candle_cv_q_dim_jet_step boxes instruction stack =
    Cexp_if (Cexp_ispair instruction)
      (Cexp_if (Cexp_eq (Cexp_fst instruction) (Cexp_num 0))
        (Cexp_pair
          (candle_cv_q_dim_jet_constant boxes (Cexp_snd instruction)) stack)
        (Cexp_pair
          (candle_cv_q_dim_jet_variable boxes (Cexp_snd instruction)) stack))
      (Cexp_if (Cexp_eq instruction (Cexp_num 2))
        (Cexp_pair
          (candle_cv_q_dim_jet_neg
            (candle_cv_q_dim_jet_head boxes stack))
          (candle_cv_q_dim_jet_tail stack))
        (Cexp_if (Cexp_eq instruction (Cexp_num 3))
          (Cexp_pair
            (candle_cv_q_dim_jet_add
              (candle_cv_q_dim_jet_head boxes
                (candle_cv_q_dim_jet_tail stack))
              (candle_cv_q_dim_jet_head boxes stack))
            (candle_cv_q_dim_jet_tail (candle_cv_q_dim_jet_tail stack)))
          (Cexp_if (Cexp_eq instruction (Cexp_num 4))
            (Cexp_pair
              (candle_cv_q_dim_jet_mul
                (candle_cv_q_dim_jet_head boxes
                  (candle_cv_q_dim_jet_tail stack))
                (candle_cv_q_dim_jet_head boxes stack))
              (candle_cv_q_dim_jet_tail (candle_cv_q_dim_jet_tail stack)))
            (Cexp_pair
              (candle_cv_q_dim_jet_mul
                (candle_cv_q_dim_jet_head boxes stack)
                (candle_cv_q_dim_jet_head boxes stack))
              (candle_cv_q_dim_jet_tail stack)))))`;;

let candle_cv_q_dim_jet_run_def = define
 `(candle_cv_q_dim_jet_run boxes (Cexp_num z) stack = stack) /\
  (candle_cv_q_dim_jet_run boxes (Cexp_pair h t) stack =
     candle_cv_q_dim_jet_run boxes t
       (candle_cv_q_dim_jet_step boxes h stack))`;;

let candle_cv_q_dim_jet_run_compute = prove
 (`!boxes program stack.
     candle_cv_q_dim_jet_run boxes program stack =
     Cexp_if (Cexp_ispair program)
       (candle_cv_q_dim_jet_run boxes (Cexp_snd program)
         (candle_cv_q_dim_jet_step boxes (Cexp_fst program) stack))
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dim_jet_run_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_jet_program_def = new_definition
 `candle_cv_q_dim_jet_program boxes program =
    candle_cv_q_dim_jet_head boxes
      (candle_cv_q_dim_jet_run boxes program (Cexp_num 0))`;;

let candle_cv_q_dot_abs_upper_normalized_def = define
 `(candle_cv_q_dot_abs_upper_normalized (Cexp_num n) ys =
     candle_cv_q_zero) /\
  (candle_cv_q_dot_abs_upper_normalized (Cexp_pair x xs) (Cexp_num n) =
     candle_cv_q_zero) /\
  (candle_cv_q_dot_abs_upper_normalized
     (Cexp_pair x xs) (Cexp_pair y ys) =
     candle_cv_q_add_normalized
       (candle_cv_q_mul_normalized x (candle_cv_q_abs_upper y))
       (candle_cv_q_dot_abs_upper_normalized xs ys))`;;

let candle_cv_q_weighted_rows_abs_upper_normalized_def = define
 `(candle_cv_q_weighted_rows_abs_upper_normalized
     radii (Cexp_num n) row_lists = candle_cv_q_zero) /\
  (candle_cv_q_weighted_rows_abs_upper_normalized
     radii (Cexp_pair w ws) (Cexp_num n) = candle_cv_q_zero) /\
  (candle_cv_q_weighted_rows_abs_upper_normalized
     radii (Cexp_pair w ws) (Cexp_pair interval_row row_tail) =
     candle_cv_q_add_normalized
       (candle_cv_q_mul_normalized w
         (candle_cv_q_dot_abs_upper_normalized radii interval_row))
       (candle_cv_q_weighted_rows_abs_upper_normalized
         radii ws row_tail))`;;

let candle_cv_q_dot_abs_upper_normalized_compute = prove
 (`!xs ys.
     candle_cv_q_dot_abs_upper_normalized xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_if (Cexp_ispair ys)
         (candle_cv_q_add_normalized
           (candle_cv_q_mul_normalized
             (Cexp_fst xs) (candle_cv_q_abs_upper (Cexp_fst ys)))
           (candle_cv_q_dot_abs_upper_normalized
             (Cexp_snd xs) (Cexp_snd ys)))
         candle_cv_q_zero)
       candle_cv_q_zero`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `ys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dot_abs_upper_normalized_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_weighted_rows_abs_upper_normalized_compute = prove
 (`!radii weights row_lists.
     candle_cv_q_weighted_rows_abs_upper_normalized
       radii weights row_lists =
     Cexp_if (Cexp_ispair weights)
       (Cexp_if (Cexp_ispair row_lists)
         (candle_cv_q_add_normalized
           (candle_cv_q_mul_normalized (Cexp_fst weights)
             (candle_cv_q_dot_abs_upper_normalized
               radii (Cexp_fst row_lists)))
           (candle_cv_q_weighted_rows_abs_upper_normalized
             radii (Cexp_snd weights) (Cexp_snd row_lists)))
         candle_cv_q_zero)
       candle_cv_q_zero`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `weights:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_weighted_rows_abs_upper_normalized_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_taylor_upper_normalized_def = new_definition
 `candle_cv_q_dim_taylor_upper_normalized radii f gradient hessian =
    candle_cv_q_add_normalized (Cexp_snd f)
      (candle_cv_q_add_normalized
        (candle_cv_q_dot_abs_upper_normalized radii gradient)
        (candle_cv_q_mul_normalized candle_cv_q_half
          (candle_cv_q_weighted_rows_abs_upper_normalized
            radii radii hessian)))`;;

let candle_cv_q_dim_jet_taylor_upper_def = new_definition
 `candle_cv_q_dim_jet_taylor_upper radii center_jet box_jet =
    candle_cv_q_dim_taylor_upper_normalized radii
      (candle_cv_q_dim_jet_f center_jet)
      (candle_cv_q_dim_jet_gradient center_jet)
      (candle_cv_q_dim_jet_hessian box_jet)`;;

let candle_cv_q_dim_jet_whole_box_upper_def = new_definition
 `candle_cv_q_dim_jet_whole_box_upper program boxes =
    candle_cv_q_dim_jet_taylor_upper
      (candle_cv_q_radius_list boxes)
      (candle_cv_q_dim_jet_program
        (candle_cv_q_center_environment_list boxes) program)
      (candle_cv_q_dim_jet_program boxes program)`;;

let candle_cv_q_dim_jet_whole_box_check_def = new_definition
 `candle_cv_q_dim_jet_whole_box_check program boxes =
    candle_cv_q_dim_whole_box_finish (Cexp_num 1)
      (candle_cv_q_box_valid_list boxes)
      (candle_cv_q_dim_jet_whole_box_upper program boxes)`;;

let candle_cv_q_dim_jet_compute_eqs =
  candle_cv_q_dim_whole_box_compute_eqs @
  candle_cv_q_normalized_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_interval_add_normalized_def;
    candle_cv_q_interval_mul_normalized_def;
    candle_cv_q_list_normalize_compute;
    candle_cv_q_interval_list_normalize_compute;
    candle_cv_q_one_def;
    candle_cv_q_one_interval_def;
    candle_cv_q_dim_jet_make_def;
    candle_cv_q_dim_jet_f_def;
    candle_cv_q_dim_jet_gradient_def;
    candle_cv_q_dim_jet_hessian_def;
    candle_cv_q_dim_jet_zero_def;
    candle_cv_q_dim_jet_constant_def;
    candle_cv_q_dim_jet_variable_def;
    candle_cv_q_dim_jet_neg_def;
    candle_cv_q_dim_jet_add_def;
    candle_cv_q_dim_jet_mul_def;
    candle_cv_q_dim_jet_head_def;
    candle_cv_q_dim_jet_tail_def;
    candle_cv_q_dim_jet_step_def;
    candle_cv_q_dim_jet_run_compute;
    candle_cv_q_dim_jet_program_def;
    candle_cv_q_dot_abs_upper_normalized_compute;
    candle_cv_q_weighted_rows_abs_upper_normalized_compute;
    candle_cv_q_dim_taylor_upper_normalized_def;
    candle_cv_q_dim_jet_taylor_upper_def;
    candle_cv_q_dim_jet_whole_box_upper_def;
    candle_cv_q_dim_jet_whole_box_check_def] @
  map SPEC_ALL
   [candle_cv_q_dim_interval_zeros_compute;
    candle_cv_q_dim_interval_unit_compute;
    candle_cv_q_dim_interval_zero_matrix_compute;
    candle_cv_q_dim_interval_list_neg_compute;
    candle_cv_q_dim_interval_list_add_compute;
    candle_cv_q_dim_interval_list_scale_compute;
    candle_cv_q_dim_interval_matrix_neg_compute;
    candle_cv_q_dim_interval_matrix_add_compute;
    candle_cv_q_dim_interval_matrix_scale_compute;
    candle_cv_q_dim_interval_outer_compute];;

end;;
