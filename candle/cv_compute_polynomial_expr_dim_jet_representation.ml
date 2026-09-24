(* ========================================================================== *)
(* Representation correctness for normalized dimension-generic interval jets. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The reflected evaluator deliberately reduces  *)
(* exact rationals between operations.  This file gives that executable path  *)
(* an ordinary HOL denotation and proves the cval implementation represents it *)
(* exactly.  Semantic source soundness is proved after this representation    *)
(* layer, using preservation of real endpoint values under normalization.     *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_jet_compute.ml";;

module Candle_cv_polynomial_expr_dim_jet_representation = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_jet;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_exact_rational_normalize;;
open Candle_cv_polynomial_expr_dim_jet_compute;;

(* Ordinary normalized operations mirrored exactly by the cval program. *)

let candle_q_interval_add_normalized_def = new_definition
 `candle_q_interval_add_normalized x y =
    candle_q_interval_normalize (candle_q_interval_add x y)`;;

let candle_q_interval_mul_normalized_def = new_definition
 `candle_q_interval_mul_normalized x y =
    candle_q_interval_normalize (candle_q_interval_mul x y)`;;

let candle_q_dim_interval_zeros_like_def = define
 `(candle_q_dim_interval_zeros_like
     ([]:(((num#num)#num)#((num#num)#num))list) = []) /\
  (candle_q_dim_interval_zeros_like (CONS h t) =
     CONS candle_q_zero_interval (candle_q_dim_interval_zeros_like t))`;;

let candle_q_dim_interval_unit_like_def = define
 `(candle_q_dim_interval_unit_like n
     ([]:(((num#num)#num)#((num#num)#num))list) = []) /\
  (candle_q_dim_interval_unit_like 0 (CONS h t) =
     CONS candle_q_one_interval (candle_q_dim_interval_zeros_like t)) /\
  (candle_q_dim_interval_unit_like (SUC n) (CONS h t) =
     CONS candle_q_zero_interval (candle_q_dim_interval_unit_like n t))`;;

let candle_q_dim_interval_zero_matrix_like_def = define
 `(candle_q_dim_interval_zero_matrix_like width
     ([]:(((num#num)#num)#((num#num)#num))list) = []) /\
  (candle_q_dim_interval_zero_matrix_like width (CONS h t) =
     CONS (candle_q_dim_interval_zeros_like width)
       (candle_q_dim_interval_zero_matrix_like width t))`;;

let candle_q_dim_interval_list_neg_def = define
 `(candle_q_dim_interval_list_neg [] =
     ([]:(((num#num)#num)#((num#num)#num))list)) /\
  (candle_q_dim_interval_list_neg (CONS h t) =
     CONS (candle_q_interval_neg h)
       (candle_q_dim_interval_list_neg t))`;;

let candle_q_dim_interval_list_add_normalized_def = define
 `(candle_q_dim_interval_list_add_normalized [] ys =
     ([]:(((num#num)#num)#((num#num)#num))list)) /\
  (candle_q_dim_interval_list_add_normalized (CONS x xs) [] = []) /\
  (candle_q_dim_interval_list_add_normalized
     (CONS x xs) (CONS y ys) =
     CONS (candle_q_interval_add_normalized x y)
       (candle_q_dim_interval_list_add_normalized xs ys))`;;

let candle_q_dim_interval_list_scale_normalized_def = define
 `(candle_q_dim_interval_list_scale_normalized q [] =
     ([]:(((num#num)#num)#((num#num)#num))list)) /\
  (candle_q_dim_interval_list_scale_normalized q (CONS h t) =
     CONS (candle_q_interval_mul_normalized q h)
       (candle_q_dim_interval_list_scale_normalized q t))`;;

let candle_q_dim_interval_matrix_neg_def = define
 `(candle_q_dim_interval_matrix_neg
     ([]:((((num#num)#num)#((num#num)#num))list)list) = []) /\
  (candle_q_dim_interval_matrix_neg (CONS h t) =
     CONS (candle_q_dim_interval_list_neg h)
       (candle_q_dim_interval_matrix_neg t))`;;

let candle_q_dim_interval_matrix_add_normalized_def = define
 `(candle_q_dim_interval_matrix_add_normalized [] ys =
     ([]:((((num#num)#num)#((num#num)#num))list)list)) /\
  (candle_q_dim_interval_matrix_add_normalized (CONS x xs) [] = []) /\
  (candle_q_dim_interval_matrix_add_normalized
     (CONS x xs) (CONS y ys) =
     CONS (candle_q_dim_interval_list_add_normalized x y)
       (candle_q_dim_interval_matrix_add_normalized xs ys))`;;

let candle_q_dim_interval_matrix_scale_normalized_def = define
 `(candle_q_dim_interval_matrix_scale_normalized q [] =
     ([]:((((num#num)#num)#((num#num)#num))list)list)) /\
  (candle_q_dim_interval_matrix_scale_normalized q (CONS h t) =
     CONS (candle_q_dim_interval_list_scale_normalized q h)
       (candle_q_dim_interval_matrix_scale_normalized q t))`;;

let candle_q_dim_interval_outer_normalized_def = define
 `(candle_q_dim_interval_outer_normalized [] ys =
     ([]:((((num#num)#num)#((num#num)#num))list)list)) /\
  (candle_q_dim_interval_outer_normalized (CONS x xs) ys =
     CONS (candle_q_dim_interval_list_scale_normalized x ys)
       (candle_q_dim_interval_outer_normalized xs ys))`;;

let candle_q_dim_jet_normalized_zero_def = new_definition
 `candle_q_dim_jet_normalized_zero boxes =
    candle_q_dim_jet_make candle_q_zero_interval
      (candle_q_dim_interval_zeros_like boxes)
      (candle_q_dim_interval_zero_matrix_like boxes boxes)`;;

let candle_q_dim_jet_normalized_constant_def = new_definition
 `candle_q_dim_jet_normalized_constant boxes q =
    candle_q_dim_jet_make (q,q)
      (candle_q_dim_interval_zeros_like boxes)
      (candle_q_dim_interval_zero_matrix_like boxes boxes)`;;

let candle_q_dim_jet_normalized_variable_def = new_definition
 `candle_q_dim_jet_normalized_variable boxes variable =
    candle_q_dim_jet_make
      (candle_q_interval_lookup variable boxes)
      (candle_q_dim_interval_unit_like variable boxes)
      (candle_q_dim_interval_zero_matrix_like boxes boxes)`;;

let candle_q_dim_jet_normalized_neg_def = new_definition
 `candle_q_dim_jet_normalized_neg a =
    candle_q_dim_jet_make
      (candle_q_interval_neg (candle_q_dim_jet_f a))
      (candle_q_dim_interval_list_neg (candle_q_dim_jet_gradient a))
      (candle_q_dim_interval_matrix_neg (candle_q_dim_jet_hessian a))`;;

let candle_q_dim_jet_normalized_add_def = new_definition
 `candle_q_dim_jet_normalized_add a b =
    candle_q_dim_jet_make
      (candle_q_interval_add_normalized
        (candle_q_dim_jet_f a) (candle_q_dim_jet_f b))
      (candle_q_dim_interval_list_add_normalized
        (candle_q_dim_jet_gradient a) (candle_q_dim_jet_gradient b))
      (candle_q_dim_interval_matrix_add_normalized
        (candle_q_dim_jet_hessian a) (candle_q_dim_jet_hessian b))`;;

let candle_q_dim_jet_normalized_mul_def = new_definition
 `candle_q_dim_jet_normalized_mul a b =
    candle_q_dim_jet_make
      (candle_q_interval_mul_normalized
        (candle_q_dim_jet_f a) (candle_q_dim_jet_f b))
      (candle_q_dim_interval_list_add_normalized
        (candle_q_dim_interval_list_scale_normalized
          (candle_q_dim_jet_f b) (candle_q_dim_jet_gradient a))
        (candle_q_dim_interval_list_scale_normalized
          (candle_q_dim_jet_f a) (candle_q_dim_jet_gradient b)))
      (candle_q_dim_interval_matrix_add_normalized
        (candle_q_dim_interval_matrix_add_normalized
          (candle_q_dim_interval_matrix_scale_normalized
            (candle_q_dim_jet_f b) (candle_q_dim_jet_hessian a))
          (candle_q_dim_interval_outer_normalized
            (candle_q_dim_jet_gradient a)
            (candle_q_dim_jet_gradient b)))
        (candle_q_dim_interval_matrix_add_normalized
          (candle_q_dim_interval_outer_normalized
            (candle_q_dim_jet_gradient b)
            (candle_q_dim_jet_gradient a))
          (candle_q_dim_interval_matrix_scale_normalized
            (candle_q_dim_jet_f a) (candle_q_dim_jet_hessian b))))`;;

let candle_q_dim_jet_normalized_head_def = define
 `(candle_q_dim_jet_normalized_head boxes [] =
     candle_q_dim_jet_normalized_zero boxes) /\
  (candle_q_dim_jet_normalized_head boxes (CONS h t) = h)`;;

let candle_q_dim_jet_normalized_tail_def = define
 `(candle_q_dim_jet_normalized_tail
     ([]:((((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list)list))list) = []) /\
  (candle_q_dim_jet_normalized_tail (CONS h t) = t)`;;

let candle_q_dim_jet_normalized_step_def = define
 `(candle_q_dim_jet_normalized_step boxes (Candle_q_push p n d) stack =
     CONS (candle_q_dim_jet_normalized_constant boxes ((p,n),d)) stack) /\
  (candle_q_dim_jet_normalized_step boxes (Candle_q_load i) stack =
     CONS (candle_q_dim_jet_normalized_variable boxes i) stack) /\
  (candle_q_dim_jet_normalized_step boxes Candle_q_neg stack =
     CONS
       (candle_q_dim_jet_normalized_neg
         (candle_q_dim_jet_normalized_head boxes stack))
       (candle_q_dim_jet_normalized_tail stack)) /\
  (candle_q_dim_jet_normalized_step boxes Candle_q_add stack =
     CONS
       (candle_q_dim_jet_normalized_add
         (candle_q_dim_jet_normalized_head boxes
           (candle_q_dim_jet_normalized_tail stack))
         (candle_q_dim_jet_normalized_head boxes stack))
       (candle_q_dim_jet_normalized_tail
         (candle_q_dim_jet_normalized_tail stack))) /\
  (candle_q_dim_jet_normalized_step boxes Candle_q_mul stack =
     CONS
       (candle_q_dim_jet_normalized_mul
         (candle_q_dim_jet_normalized_head boxes
           (candle_q_dim_jet_normalized_tail stack))
         (candle_q_dim_jet_normalized_head boxes stack))
       (candle_q_dim_jet_normalized_tail
         (candle_q_dim_jet_normalized_tail stack))) /\
  (candle_q_dim_jet_normalized_step boxes Candle_q_square stack =
     CONS
       (candle_q_dim_jet_normalized_mul
         (candle_q_dim_jet_normalized_head boxes stack)
         (candle_q_dim_jet_normalized_head boxes stack))
       (candle_q_dim_jet_normalized_tail stack))`;;

let candle_q_dim_jet_normalized_run_def = define
 `(candle_q_dim_jet_normalized_run boxes [] stack = stack) /\
  (candle_q_dim_jet_normalized_run boxes (CONS h t) stack =
     candle_q_dim_jet_normalized_run boxes t
       (candle_q_dim_jet_normalized_step boxes h stack))`;;

let candle_q_dim_jet_normalized_program_def = new_definition
 `candle_q_dim_jet_normalized_program boxes program =
    candle_q_dim_jet_normalized_head boxes
      (candle_q_dim_jet_normalized_run boxes program [])`;;

(* Encodings for ordinary normalized jets and their stacks. *)

let candle_cv_q_dim_jet_encode_def = new_definition
 `candle_cv_q_dim_jet_encode jet =
    candle_cv_q_dim_jet_make
      (candle_cv_q_interval (candle_q_dim_jet_f jet))
      (candle_cv_q_interval_list (candle_q_dim_jet_gradient jet))
      (candle_cv_q_interval_matrix (candle_q_dim_jet_hessian jet))`;;

let candle_cv_q_dim_jet_list_encode_def = define
 `(candle_cv_q_dim_jet_list_encode [] = Cexp_num 0) /\
  (candle_cv_q_dim_jet_list_encode (CONS h t) =
     Cexp_pair (candle_cv_q_dim_jet_encode h)
       (candle_cv_q_dim_jet_list_encode t))`;;

(* Primitive and structural representation lemmas. *)

let candle_cv_q_interval_add_normalized_correct = prove
 (`!x y.
     candle_cv_q_interval_add_normalized
       (candle_cv_q_interval x) (candle_cv_q_interval y) =
     candle_cv_q_interval (candle_q_interval_add_normalized x y)`,
  REWRITE_TAC[candle_cv_q_interval_add_normalized_def;
              candle_q_interval_add_normalized_def;
              candle_cv_q_interval_add_correct;
              candle_cv_q_interval_normalize_correct]);;

let candle_cv_q_interval_mul_normalized_correct = prove
 (`!x y.
     candle_cv_q_interval_mul_normalized
       (candle_cv_q_interval x) (candle_cv_q_interval y) =
     candle_cv_q_interval (candle_q_interval_mul_normalized x y)`,
  REWRITE_TAC[candle_cv_q_interval_mul_normalized_def;
              candle_q_interval_mul_normalized_def;
              candle_cv_q_interval_mul_correct;
              candle_cv_q_interval_normalize_correct]);;

let candle_cv_q_dim_interval_zeros_correct = prove
 (`!boxes.
     candle_cv_q_dim_interval_zeros (candle_cv_q_interval_list boxes) =
     candle_cv_q_interval_list (candle_q_dim_interval_zeros_like boxes)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_dim_interval_zeros_def;
                  candle_cv_q_interval_list_def;
                  candle_q_dim_interval_zeros_like_def;
                  candle_cv_q_zero_interval_def;
                  candle_q_zero_interval_def;
                  candle_cv_q_interval_def]);;

let candle_cv_q_dim_interval_unit_correct = prove
 (`!variable boxes.
     candle_cv_q_dim_interval_unit (Cexp_num variable)
       (candle_cv_q_interval_list boxes) =
     candle_cv_q_interval_list
       (candle_q_dim_interval_unit_like variable boxes)`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_dim_interval_unit_def;
                  candle_cv_q_interval_list_def;
                  candle_q_dim_interval_unit_like_def;
                  candle_cv_q_dim_interval_zeros_correct;
                  candle_cv_q_zero_interval_def;
                  candle_q_zero_interval_def;
                  candle_cv_q_one_interval_correct;
                  candle_cv_q_interval_def]);;

let candle_cv_q_dim_interval_zero_matrix_correct = prove
 (`!width rows.
     candle_cv_q_dim_interval_zero_matrix
       (candle_cv_q_interval_list width)
       (candle_cv_q_interval_list rows) =
     candle_cv_q_interval_matrix
       (candle_q_dim_interval_zero_matrix_like width rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_dim_interval_zero_matrix_def;
                  candle_cv_q_interval_list_def;
                  candle_cv_q_interval_matrix_def;
                  candle_q_dim_interval_zero_matrix_like_def;
                  candle_cv_q_dim_interval_zeros_correct]);;

let candle_cv_q_dim_interval_list_neg_correct = prove
 (`!items.
     candle_cv_q_dim_interval_list_neg
       (candle_cv_q_interval_list items) =
     candle_cv_q_interval_list (candle_q_dim_interval_list_neg items)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_dim_interval_list_neg_def;
                  candle_cv_q_interval_list_def;
                  candle_q_dim_interval_list_neg_def;
                  candle_cv_q_interval_neg_correct]);;

let candle_cv_q_dim_interval_list_add_correct = prove
 (`!xs ys.
     candle_cv_q_dim_interval_list_add
       (candle_cv_q_interval_list xs) (candle_cv_q_interval_list ys) =
     candle_cv_q_interval_list
       (candle_q_dim_interval_list_add_normalized xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_interval_list_def;
                candle_cv_q_dim_interval_list_add_def;
                candle_q_dim_interval_list_add_normalized_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_q_interval_list_def;
                    candle_cv_q_dim_interval_list_add_def;
                    candle_q_dim_interval_list_add_normalized_def;
                    candle_cv_q_interval_add_normalized_correct]]);;

let candle_cv_q_dim_interval_list_scale_correct = prove
 (`!q items.
     candle_cv_q_dim_interval_list_scale
       (candle_cv_q_interval q) (candle_cv_q_interval_list items) =
     candle_cv_q_interval_list
       (candle_q_dim_interval_list_scale_normalized q items)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_dim_interval_list_scale_def;
                  candle_cv_q_interval_list_def;
                  candle_q_dim_interval_list_scale_normalized_def;
                  candle_cv_q_interval_mul_normalized_correct]);;

let candle_cv_q_dim_interval_matrix_neg_correct = prove
 (`!rows.
     candle_cv_q_dim_interval_matrix_neg
       (candle_cv_q_interval_matrix rows) =
     candle_cv_q_interval_matrix (candle_q_dim_interval_matrix_neg rows)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_dim_interval_matrix_neg_def;
                  candle_cv_q_interval_matrix_def;
                  candle_q_dim_interval_matrix_neg_def;
                  candle_cv_q_dim_interval_list_neg_correct]);;

let candle_cv_q_dim_interval_matrix_add_correct = prove
 (`!xs ys.
     candle_cv_q_dim_interval_matrix_add
       (candle_cv_q_interval_matrix xs) (candle_cv_q_interval_matrix ys) =
     candle_cv_q_interval_matrix
       (candle_q_dim_interval_matrix_add_normalized xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_interval_matrix_def;
                candle_cv_q_dim_interval_matrix_add_def;
                candle_q_dim_interval_matrix_add_normalized_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_q_interval_matrix_def;
                    candle_cv_q_dim_interval_matrix_add_def;
                    candle_q_dim_interval_matrix_add_normalized_def;
                    candle_cv_q_dim_interval_list_add_correct]]);;

let candle_cv_q_dim_interval_matrix_scale_correct = prove
 (`!q rows.
     candle_cv_q_dim_interval_matrix_scale
       (candle_cv_q_interval q) (candle_cv_q_interval_matrix rows) =
     candle_cv_q_interval_matrix
       (candle_q_dim_interval_matrix_scale_normalized q rows)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_dim_interval_matrix_scale_def;
                  candle_cv_q_interval_matrix_def;
                  candle_q_dim_interval_matrix_scale_normalized_def;
                  candle_cv_q_dim_interval_list_scale_correct]);;

let candle_cv_q_dim_interval_outer_correct = prove
 (`!xs ys.
     candle_cv_q_dim_interval_outer
       (candle_cv_q_interval_list xs) (candle_cv_q_interval_list ys) =
     candle_cv_q_interval_matrix
       (candle_q_dim_interval_outer_normalized xs ys)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_dim_interval_outer_def;
                  candle_cv_q_interval_list_def;
                  candle_cv_q_interval_matrix_def;
                  candle_q_dim_interval_outer_normalized_def;
                  candle_cv_q_dim_interval_list_scale_correct]);;

let candle_cv_q_dim_jet_make_correct = prove
 (`!f gradient hessian.
     candle_cv_q_dim_jet_make
       (candle_cv_q_interval f)
       (candle_cv_q_interval_list gradient)
       (candle_cv_q_interval_matrix hessian) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_jet_make f gradient hessian)`,
  REWRITE_TAC[candle_cv_q_dim_jet_make_def;
              candle_cv_q_dim_jet_encode_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def; FST; SND]);;

let candle_cv_q_dim_jet_f_correct = prove
 (`!jet.
     candle_cv_q_dim_jet_f (candle_cv_q_dim_jet_encode jet) =
     candle_cv_q_interval (candle_q_dim_jet_f jet)`,
  REWRITE_TAC[candle_cv_q_dim_jet_f_def;
              candle_cv_q_dim_jet_encode_def;
              candle_cv_q_dim_jet_make_def; cexp_fst_def]);;

let candle_cv_q_dim_jet_gradient_correct = prove
 (`!jet.
     candle_cv_q_dim_jet_gradient (candle_cv_q_dim_jet_encode jet) =
     candle_cv_q_interval_list (candle_q_dim_jet_gradient jet)`,
  REWRITE_TAC[candle_cv_q_dim_jet_gradient_def;
              candle_cv_q_dim_jet_encode_def;
              candle_cv_q_dim_jet_make_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_jet_hessian_correct = prove
 (`!jet.
     candle_cv_q_dim_jet_hessian (candle_cv_q_dim_jet_encode jet) =
     candle_cv_q_interval_matrix (candle_q_dim_jet_hessian jet)`,
  REWRITE_TAC[candle_cv_q_dim_jet_hessian_def;
              candle_cv_q_dim_jet_encode_def;
              candle_cv_q_dim_jet_make_def; cexp_snd_def]);;

let candle_cv_q_dim_jet_zero_correct = prove
 (`!boxes.
     candle_cv_q_dim_jet_zero (candle_cv_q_interval_list boxes) =
     candle_cv_q_dim_jet_encode (candle_q_dim_jet_normalized_zero boxes)`,
  REWRITE_TAC[candle_cv_q_dim_jet_zero_def;
              candle_q_dim_jet_normalized_zero_def;
              candle_cv_q_dim_interval_zeros_correct;
              candle_cv_q_dim_interval_zero_matrix_correct;
              candle_cv_q_zero_interval_def;
              candle_cv_q_dim_jet_make_correct]);;

let candle_cv_q_dim_jet_constant_correct = prove
 (`!boxes q.
     candle_cv_q_dim_jet_constant
       (candle_cv_q_interval_list boxes) (candle_cv_q q) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_jet_normalized_constant boxes q)`,
  REWRITE_TAC[candle_cv_q_dim_jet_constant_def;
              candle_q_dim_jet_normalized_constant_def;
              candle_cv_q_dim_interval_zeros_correct;
              candle_cv_q_dim_interval_zero_matrix_correct;
              candle_cv_q_dim_jet_encode_def;
              candle_q_dim_jet_make_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_cv_q_dim_jet_make_def;
              candle_cv_q_interval_def;
              FST; SND]);;

let candle_cv_q_dim_jet_variable_correct = prove
 (`!boxes variable.
     candle_cv_q_dim_jet_variable
       (candle_cv_q_interval_list boxes) (Cexp_num variable) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_jet_normalized_variable boxes variable)`,
  REWRITE_TAC[candle_cv_q_dim_jet_variable_def;
              candle_q_dim_jet_normalized_variable_def;
              candle_cv_q_interval_lookup_correct;
              candle_cv_q_dim_interval_unit_correct;
              candle_cv_q_dim_interval_zero_matrix_correct;
              candle_cv_q_dim_jet_make_correct]);;

let candle_cv_q_dim_jet_neg_correct = prove
 (`!a.
     candle_cv_q_dim_jet_neg (candle_cv_q_dim_jet_encode a) =
     candle_cv_q_dim_jet_encode (candle_q_dim_jet_normalized_neg a)`,
  REWRITE_TAC[candle_cv_q_dim_jet_neg_def;
              candle_q_dim_jet_normalized_neg_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_dim_jet_gradient_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_interval_neg_correct;
              candle_cv_q_dim_interval_list_neg_correct;
              candle_cv_q_dim_interval_matrix_neg_correct;
              candle_cv_q_dim_jet_make_correct]);;

let candle_cv_q_dim_jet_add_correct = prove
 (`!a b.
     candle_cv_q_dim_jet_add
       (candle_cv_q_dim_jet_encode a) (candle_cv_q_dim_jet_encode b) =
     candle_cv_q_dim_jet_encode (candle_q_dim_jet_normalized_add a b)`,
  REWRITE_TAC[candle_cv_q_dim_jet_add_def;
              candle_q_dim_jet_normalized_add_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_dim_jet_gradient_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_interval_add_normalized_correct;
              candle_cv_q_dim_interval_list_add_correct;
              candle_cv_q_dim_interval_matrix_add_correct;
              candle_cv_q_dim_jet_make_correct]);;

let candle_cv_q_dim_jet_mul_correct = prove
 (`!a b.
     candle_cv_q_dim_jet_mul
       (candle_cv_q_dim_jet_encode a) (candle_cv_q_dim_jet_encode b) =
     candle_cv_q_dim_jet_encode (candle_q_dim_jet_normalized_mul a b)`,
  REWRITE_TAC[candle_cv_q_dim_jet_mul_def;
              candle_q_dim_jet_normalized_mul_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_dim_jet_gradient_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_interval_mul_normalized_correct;
              candle_cv_q_dim_interval_list_scale_correct;
              candle_cv_q_dim_interval_list_add_correct;
              candle_cv_q_dim_interval_matrix_scale_correct;
              candle_cv_q_dim_interval_outer_correct;
              candle_cv_q_dim_interval_matrix_add_correct;
              candle_cv_q_dim_jet_make_correct]);;

let candle_cv_q_dim_jet_head_correct = prove
 (`!boxes stack.
     candle_cv_q_dim_jet_head (candle_cv_q_interval_list boxes)
       (candle_cv_q_dim_jet_list_encode stack) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_jet_normalized_head boxes stack)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_head_def;
              candle_cv_q_dim_jet_list_encode_def;
              candle_q_dim_jet_normalized_head_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def;
              candle_cv_q_dim_jet_zero_correct]);;

let candle_cv_q_dim_jet_tail_correct = prove
 (`!stack.
     candle_cv_q_dim_jet_tail (candle_cv_q_dim_jet_list_encode stack) =
     candle_cv_q_dim_jet_list_encode
       (candle_q_dim_jet_normalized_tail stack)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_tail_def;
              candle_cv_q_dim_jet_list_encode_def;
              candle_q_dim_jet_normalized_tail_def;
              cexp_if_def; cexp_ispair_def; cexp_snd_def]);;

let candle_cv_q_dim_jet_step_correct = prove
 (`!instruction boxes stack.
     candle_cv_q_dim_jet_step
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction instruction)
       (candle_cv_q_dim_jet_list_encode stack) =
     candle_cv_q_dim_jet_list_encode
       (candle_q_dim_jet_normalized_step boxes instruction stack)`,
  MATCH_MP_TAC candle_q_instruction_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_step_def;
              candle_q_dim_jet_normalized_step_def;
              candle_cv_q_instruction_def;
              candle_cv_q_dim_jet_list_encode_def;
              cexp_fst_def; cexp_snd_def; cexp_eq_def; cexp_if_def;
              cexp_ispair_def; distinctness "cval"; injectivity "cval";
              NOT_SUC; candle_one_ne_zero; candle_four_ne_two;
              candle_four_ne_three; candle_three_ne_two;
              candle_five_ne_two; candle_five_ne_three;
              candle_five_ne_four;
              candle_cv_q_dim_jet_constant_correct;
              candle_cv_q_dim_jet_variable_correct;
              candle_cv_q_dim_jet_head_correct;
              candle_cv_q_dim_jet_tail_correct;
              candle_cv_q_dim_jet_neg_correct;
              candle_cv_q_dim_jet_add_correct;
              candle_cv_q_dim_jet_mul_correct]);;

let candle_cv_q_dim_jet_run_correct = prove
 (`!program boxes stack.
     candle_cv_q_dim_jet_run
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list program)
       (candle_cv_q_dim_jet_list_encode stack) =
     candle_cv_q_dim_jet_list_encode
       (candle_q_dim_jet_normalized_run boxes program stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_q_instruction_list_def;
                  candle_cv_q_dim_jet_run_def;
                  candle_q_dim_jet_normalized_run_def;
                  candle_cv_q_dim_jet_step_correct]);;

let candle_cv_q_dim_jet_program_correct = prove
 (`!program boxes.
     candle_cv_q_dim_jet_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list program) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_jet_normalized_program boxes program)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_program_def;
              candle_q_dim_jet_normalized_program_def;
              GSYM candle_cv_q_dim_jet_list_encode_def;
              candle_cv_q_dim_jet_run_correct;
              candle_cv_q_dim_jet_head_correct]);;

end;;
