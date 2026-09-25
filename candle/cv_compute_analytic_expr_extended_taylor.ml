(* ========================================================================== *)
(* Extended-normalization Taylor accumulation for authentic NL leaves.       *)
(*                                                                            *)
(* This keeps the established exact Taylor formula but uses the checked      *)
(* 1024-step rational normalizer at every scalar product and accumulation.    *)
(* Its real denotation is proved identical to the baseline Taylor bound.      *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_rational_normalize_extended.ml";;
needs "candle/cv_compute_polynomial_expr_dim_jet_compute.ml";;

module Candle_cv_analytic_expr_extended_taylor = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_rational_normalize_extended;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_dim_jet_compute;;

let candle_q_dot_abs_upper_extended_def = define
 `(candle_q_dot_abs_upper_extended [] ys = candle_q_zero) /\
  (candle_q_dot_abs_upper_extended (CONS x xs) [] = candle_q_zero) /\
  (candle_q_dot_abs_upper_extended (CONS x xs) (CONS y ys) =
     candle_q_add_normalized_extended
       (candle_q_mul_normalized_extended x (candle_q_abs_upper y))
       (candle_q_dot_abs_upper_extended xs ys))`;;

let candle_q_weighted_rows_abs_upper_extended_def = define
 `(candle_q_weighted_rows_abs_upper_extended radii [] row_lists =
     candle_q_zero) /\
  (candle_q_weighted_rows_abs_upper_extended radii (CONS w ws) [] =
     candle_q_zero) /\
  (candle_q_weighted_rows_abs_upper_extended radii (CONS w ws)
     (CONS interval_row row_tail) =
     candle_q_add_normalized_extended
       (candle_q_mul_normalized_extended w
         (candle_q_dot_abs_upper_extended radii interval_row))
       (candle_q_weighted_rows_abs_upper_extended
         radii ws row_tail))`;;

let candle_q_dim_taylor_upper_extended_def = new_definition
 `candle_q_dim_taylor_upper_extended radii f gradient hessian =
    candle_q_add_normalized_extended (SND f)
      (candle_q_add_normalized_extended
        (candle_q_dot_abs_upper_extended radii gradient)
        (candle_q_mul_normalized_extended candle_q_half
          (candle_q_weighted_rows_abs_upper_extended
            radii radii hessian)))`;;

let candle_q_dot_abs_upper_extended_real = prove
 (`!xs ys.
     candle_q_real (candle_q_dot_abs_upper_extended xs ys) =
     candle_q_real (candle_q_dot_abs_upper xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_q_dot_abs_upper_extended_def;
                candle_q_dot_abs_upper_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_q_dot_abs_upper_extended_def;
                    candle_q_dot_abs_upper_def;
                    candle_q_real_add_normalized_extended;
                    candle_q_real_mul_normalized_extended;
                    candle_q_real_add; candle_q_real_mul]]);;

let candle_q_weighted_rows_abs_upper_extended_real = prove
 (`!radii weights row_lists.
     candle_q_real
       (candle_q_weighted_rows_abs_upper_extended
         radii weights row_lists) =
     candle_q_real
       (candle_q_weighted_rows_abs_upper radii weights row_lists)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_q_weighted_rows_abs_upper_extended_def;
                candle_q_weighted_rows_abs_upper_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_q_weighted_rows_abs_upper_extended_def;
                    candle_q_weighted_rows_abs_upper_def;
                    candle_q_dot_abs_upper_extended_real;
                    candle_q_real_add_normalized_extended;
                    candle_q_real_mul_normalized_extended;
                    candle_q_real_add; candle_q_real_mul]]);;

let candle_q_dim_taylor_upper_extended_real = prove
 (`!radii f gradient hessian.
     candle_q_real
       (candle_q_dim_taylor_upper_extended radii f gradient hessian) =
     candle_q_real (candle_q_dim_taylor_upper radii f gradient hessian)`,
  REWRITE_TAC[candle_q_dim_taylor_upper_extended_def;
              candle_q_dim_taylor_upper_def;
              candle_q_dot_abs_upper_extended_real;
              candle_q_weighted_rows_abs_upper_extended_real;
              candle_q_real_add_normalized_extended;
              candle_q_real_mul_normalized_extended;
              candle_q_real_add; candle_q_real_mul]);;

let candle_cv_q_dot_abs_upper_extended_def = define
 `(candle_cv_q_dot_abs_upper_extended (Cexp_num n) ys =
     candle_cv_q_zero) /\
  (candle_cv_q_dot_abs_upper_extended (Cexp_pair x xs) (Cexp_num n) =
     candle_cv_q_zero) /\
  (candle_cv_q_dot_abs_upper_extended
     (Cexp_pair x xs) (Cexp_pair y ys) =
     candle_cv_q_add_normalized_extended
       (candle_cv_q_mul_normalized_extended x (candle_cv_q_abs_upper y))
       (candle_cv_q_dot_abs_upper_extended xs ys))`;;

let candle_cv_q_weighted_rows_abs_upper_extended_def = define
 `(candle_cv_q_weighted_rows_abs_upper_extended
     radii (Cexp_num n) row_lists = candle_cv_q_zero) /\
  (candle_cv_q_weighted_rows_abs_upper_extended
     radii (Cexp_pair w ws) (Cexp_num n) = candle_cv_q_zero) /\
  (candle_cv_q_weighted_rows_abs_upper_extended
     radii (Cexp_pair w ws) (Cexp_pair interval_row row_tail) =
     candle_cv_q_add_normalized_extended
       (candle_cv_q_mul_normalized_extended w
         (candle_cv_q_dot_abs_upper_extended radii interval_row))
       (candle_cv_q_weighted_rows_abs_upper_extended
         radii ws row_tail))`;;

let candle_cv_q_dot_abs_upper_extended_compute = prove
 (`!xs ys.
     candle_cv_q_dot_abs_upper_extended xs ys =
     Cexp_if (Cexp_ispair xs)
       (Cexp_if (Cexp_ispair ys)
         (candle_cv_q_add_normalized_extended
           (candle_cv_q_mul_normalized_extended
             (Cexp_fst xs) (candle_cv_q_abs_upper (Cexp_fst ys)))
           (candle_cv_q_dot_abs_upper_extended
             (Cexp_snd xs) (Cexp_snd ys)))
         candle_cv_q_zero)
       candle_cv_q_zero`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `ys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_dot_abs_upper_extended_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_weighted_rows_abs_upper_extended_compute = prove
 (`!radii weights row_lists.
     candle_cv_q_weighted_rows_abs_upper_extended radii weights row_lists =
     Cexp_if (Cexp_ispair weights)
       (Cexp_if (Cexp_ispair row_lists)
         (candle_cv_q_add_normalized_extended
           (candle_cv_q_mul_normalized_extended (Cexp_fst weights)
             (candle_cv_q_dot_abs_upper_extended
               radii (Cexp_fst row_lists)))
           (candle_cv_q_weighted_rows_abs_upper_extended
             radii (Cexp_snd weights) (Cexp_snd row_lists)))
         candle_cv_q_zero)
       candle_cv_q_zero`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `weights:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_q_weighted_rows_abs_upper_extended_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_q_dim_taylor_upper_extended_def = new_definition
 `candle_cv_q_dim_taylor_upper_extended radii f gradient hessian =
    candle_cv_q_add_normalized_extended (Cexp_snd f)
      (candle_cv_q_add_normalized_extended
        (candle_cv_q_dot_abs_upper_extended radii gradient)
        (candle_cv_q_mul_normalized_extended candle_cv_q_half
          (candle_cv_q_weighted_rows_abs_upper_extended
            radii radii hessian)))`;;

let candle_cv_q_extended_taylor_compute_eqs =
  candle_cv_q_extended_normalized_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_dot_abs_upper_extended_compute;
    candle_cv_q_weighted_rows_abs_upper_extended_compute;
    candle_cv_q_dim_taylor_upper_extended_def];;

let candle_cv_q_dot_abs_upper_extended_correct = prove
 (`!xs ys.
     candle_cv_q_dot_abs_upper_extended
       (candle_cv_q_list xs) (candle_cv_q_interval_list ys) =
     candle_cv_q (candle_q_dot_abs_upper_extended xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_list_def;
                candle_cv_q_dot_abs_upper_extended_def;
                candle_q_dot_abs_upper_extended_def;
                candle_cv_q_zero_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_q_list_def;
                    candle_cv_q_interval_list_def;
                    candle_cv_q_dot_abs_upper_extended_def;
                    candle_q_dot_abs_upper_extended_def;
                    candle_cv_q_zero_def;
                    candle_cv_q_abs_upper_correct;
                    candle_cv_q_mul_normalized_extended_correct;
                    candle_cv_q_add_normalized_extended_correct]]);;

let candle_cv_q_weighted_rows_abs_upper_extended_correct = prove
 (`!radii weights row_lists.
     candle_cv_q_weighted_rows_abs_upper_extended
       (candle_cv_q_list radii) (candle_cv_q_list weights)
       (candle_cv_q_interval_matrix row_lists) =
     candle_cv_q
       (candle_q_weighted_rows_abs_upper_extended
         radii weights row_lists)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_q_list_def;
                candle_cv_q_weighted_rows_abs_upper_extended_def;
                candle_q_weighted_rows_abs_upper_extended_def;
                candle_cv_q_zero_def];
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[candle_cv_q_list_def;
                    candle_cv_q_interval_matrix_def;
                    candle_cv_q_weighted_rows_abs_upper_extended_def;
                    candle_q_weighted_rows_abs_upper_extended_def;
                    candle_cv_q_zero_def;
                    candle_cv_q_dot_abs_upper_extended_correct;
                    candle_cv_q_mul_normalized_extended_correct;
                    candle_cv_q_add_normalized_extended_correct]]);;

let candle_cv_q_dim_taylor_upper_extended_correct = prove
 (`!radii f gradient hessian.
     candle_cv_q_dim_taylor_upper_extended
       (candle_cv_q_list radii) (candle_cv_q_interval f)
       (candle_cv_q_interval_list gradient)
       (candle_cv_q_interval_matrix hessian) =
     candle_cv_q
       (candle_q_dim_taylor_upper_extended
         radii f gradient hessian)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_taylor_upper_extended_def;
              candle_q_dim_taylor_upper_extended_def;
              candle_cv_q_interval_snd_correct;
              candle_cv_q_half_def;
              candle_cv_q_dot_abs_upper_extended_correct;
              candle_cv_q_weighted_rows_abs_upper_extended_correct;
              candle_cv_q_mul_normalized_extended_correct;
              candle_cv_q_add_normalized_extended_correct]);;

end;;
