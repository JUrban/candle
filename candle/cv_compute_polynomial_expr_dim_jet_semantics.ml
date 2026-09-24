(* ========================================================================== *)
(* Semantic bridge for normalized dimension-generic interval jets.            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The executable jet evaluator normalizes exact *)
(* rational endpoints after addition and multiplication.  This layer proves  *)
(* that normalization preserves interval meaning, defines the corresponding  *)
(* source evaluator, and connects compiled source programs to that evaluator. *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_jet_representation.ml";;

module Candle_cv_polynomial_expr_dim_jet_semantics = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_jet;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_exact_rational_normalize;;
open Candle_cv_polynomial_expr_dim_jet_representation;;

(* Normalization is representation-only: both real endpoints are unchanged. *)

let candle_q_interval_normalize_contains = prove
 (`!i x.
     candle_q_interval_contains (candle_q_interval_normalize i) x <=>
     candle_q_interval_contains i x`,
  REWRITE_TAC[candle_q_interval_contains_def;
              candle_q_interval_normalize_def;
              candle_q_real_normalize; FST; SND]);;

let candle_q_interval_add_normalized_sound = prove
 (`!i j x y.
     candle_q_interval_contains i x /\
     candle_q_interval_contains j y
     ==> candle_q_interval_contains
           (candle_q_interval_add_normalized i j) (x + y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_add_normalized_def;
              candle_q_interval_normalize_contains] THEN
  MATCH_ACCEPT_TAC candle_q_interval_add_sound);;

let candle_q_interval_mul_normalized_sound = prove
 (`!i j x y.
     candle_q_interval_contains i x /\
     candle_q_interval_contains j y
     ==> candle_q_interval_contains
           (candle_q_interval_mul_normalized i j) (x * y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_mul_normalized_def;
              candle_q_interval_normalize_contains] THEN
  MATCH_ACCEPT_TAC candle_q_interval_mul_sound);;

let candle_q_interval_mul_normalized_sound_swapped = prove
 (`!i j x y.
     candle_q_interval_contains i x /\
     candle_q_interval_contains j y
     ==> candle_q_interval_contains
           (candle_q_interval_mul_normalized i j) (y * x)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_ACCEPT_TAC candle_q_interval_mul_normalized_sound);;

(* Structural equations expose the executable list operations as the usual   *)
(* map/zip operations on well-shaped jets.  These facts are also useful for   *)
(* keeping all dimension reasoning outside the arithmetic proof.             *)

let candle_q_dim_interval_zeros_like_map = prove
 (`!items.
     candle_q_dim_interval_zeros_like items =
     MAP (\x. candle_q_zero_interval) items`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_interval_zeros_like_def; MAP]);;

let candle_q_dim_interval_unit_like_length = prove
 (`!variable items.
     LENGTH (candle_q_dim_interval_unit_like variable items) = LENGTH items`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_interval_unit_like_def;
                  candle_q_dim_interval_zeros_like_map;
                  LENGTH_MAP; LENGTH]);;

let candle_q_dim_interval_zeros_like_lookup = prove
 (`!items i.
     i < LENGTH items
     ==> candle_q_interval_lookup i
           (candle_q_dim_interval_zeros_like items) =
         candle_q_zero_interval`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_zeros_like_map; LENGTH_MAP; EL_MAP;
               candle_q_interval_lookup_in_range]);;

let candle_q_dim_interval_zeros_like_list_of_seq = prove
 (`!items.
     candle_q_dim_interval_zeros_like items =
     list_of_seq (\i. candle_q_zero_interval) (LENGTH items)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_interval_zeros_like_map; LIST_EQ;
              LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_MAP; EL_LIST_OF_SEQ]);;

let candle_q_dim_interval_unit_like_lookup = prove
 (`!variable items i.
     i < LENGTH items
     ==> candle_q_interval_lookup i
           (candle_q_dim_interval_unit_like variable items) =
         if variable = i
         then candle_q_one_interval
         else candle_q_zero_interval`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LT];
    X_GEN_TAC `i:num` THEN
    MP_TAC (SPEC `i:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `j:num` SUBST1_TAC)) THEN
    REWRITE_TAC[LENGTH; LT_SUC;
                candle_q_dim_interval_unit_like_def;
                candle_q_interval_lookup_def] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_dim_interval_zeros_like_lookup] THEN
    ARITH_TAC;
    REWRITE_TAC[LENGTH; LT];
    X_GEN_TAC `i:num` THEN
    MP_TAC (SPEC `i:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `j:num` SUBST1_TAC)) THEN
    REWRITE_TAC[LENGTH; LT_SUC;
                candle_q_dim_interval_unit_like_def;
                candle_q_interval_lookup_def; NOT_SUC; SUC_INJ] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[]]);;

let candle_q_dim_interval_zero_matrix_like_map = prove
 (`!width rows.
     candle_q_dim_interval_zero_matrix_like width rows =
     MAP (\x. candle_q_dim_interval_zeros_like width) rows`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_interval_zero_matrix_like_def; MAP]);;

let candle_q_dim_interval_zero_matrix_like_lookup = prove
 (`!width row_lists i j.
     i < LENGTH row_lists /\ j < LENGTH width
     ==> candle_q_interval_lookup j
           (candle_q_dim_interval_row_lookup i
             (candle_q_dim_interval_zero_matrix_like width row_lists)) =
         candle_q_zero_interval`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_zero_matrix_like_map; LENGTH_MAP; EL_MAP;
               candle_q_dim_interval_row_lookup_in_range;
               candle_q_dim_interval_zeros_like_lookup]);;

let candle_q_dim_interval_list_neg_map = prove
 (`!items.
     candle_q_dim_interval_list_neg items =
     MAP candle_q_interval_neg items`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_interval_list_neg_def; MAP]);;

let candle_q_dim_interval_list_add_map2 = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys
     ==> candle_q_dim_interval_list_add_normalized xs ys =
         MAP2 candle_q_interval_add_normalized xs ys`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; NOT_SUC;
                candle_q_dim_interval_list_add_normalized_def; MAP2];
    LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
                candle_q_dim_interval_list_add_normalized_def; MAP2] THEN
    ASM_MESON_TAC[]]);;

let candle_q_dim_interval_list_scale_map = prove
 (`!q items.
     candle_q_dim_interval_list_scale_normalized q items =
     MAP (candle_q_interval_mul_normalized q) items`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_interval_list_scale_normalized_def; MAP]);;

let candle_q_dim_interval_matrix_neg_map = prove
 (`!rows.
     candle_q_dim_interval_matrix_neg rows =
     MAP candle_q_dim_interval_list_neg rows`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_interval_matrix_neg_def; MAP]);;

let candle_q_dim_interval_matrix_add_map2 = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys
     ==> candle_q_dim_interval_matrix_add_normalized xs ys =
         MAP2 candle_q_dim_interval_list_add_normalized xs ys`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; NOT_SUC;
                candle_q_dim_interval_matrix_add_normalized_def; MAP2];
    LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
                candle_q_dim_interval_matrix_add_normalized_def; MAP2] THEN
    ASM_MESON_TAC[]]);;

let candle_q_dim_interval_matrix_scale_map = prove
 (`!q rows.
     candle_q_dim_interval_matrix_scale_normalized q rows =
     MAP (candle_q_dim_interval_list_scale_normalized q) rows`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_interval_matrix_scale_normalized_def; MAP]);;

let candle_q_dim_interval_outer_map = prove
 (`!xs ys.
     candle_q_dim_interval_outer_normalized xs ys =
     MAP (\x. candle_q_dim_interval_list_scale_normalized x ys) xs`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_interval_outer_normalized_def; MAP]);;

let candle_q_dim_interval_matrix_neg_row_lookup = prove
 (`!row_lists i.
     i < LENGTH row_lists
     ==> candle_q_dim_interval_row_lookup i
           (candle_q_dim_interval_matrix_neg row_lists) =
         candle_q_dim_interval_list_neg
           (candle_q_dim_interval_row_lookup i row_lists)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_matrix_neg_map; LENGTH_MAP; EL_MAP;
               candle_q_dim_interval_row_lookup_in_range]);;

let candle_q_dim_interval_matrix_add_row_lookup = prove
 (`!xs ys i.
     LENGTH xs = LENGTH ys /\ i < LENGTH xs
     ==> candle_q_dim_interval_row_lookup i
           (candle_q_dim_interval_matrix_add_normalized xs ys) =
         candle_q_dim_interval_list_add_normalized
           (candle_q_dim_interval_row_lookup i xs)
           (candle_q_dim_interval_row_lookup i ys)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `i < LENGTH
      (ys:((((num#num)#num)#((num#num)#num))list)list)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[candle_q_dim_interval_matrix_add_map2; LENGTH_MAP2; EL_MAP2;
               candle_q_dim_interval_row_lookup_in_range]);;

let candle_q_dim_interval_matrix_scale_row_lookup = prove
 (`!q row_lists i.
     i < LENGTH row_lists
     ==> candle_q_dim_interval_row_lookup i
           (candle_q_dim_interval_matrix_scale_normalized q row_lists) =
         candle_q_dim_interval_list_scale_normalized q
           (candle_q_dim_interval_row_lookup i row_lists)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_matrix_scale_map; LENGTH_MAP; EL_MAP;
               candle_q_dim_interval_row_lookup_in_range]);;

let candle_q_dim_interval_outer_row_lookup = prove
 (`!xs ys i.
     i < LENGTH xs
     ==> candle_q_dim_interval_row_lookup i
           (candle_q_dim_interval_outer_normalized xs ys) =
         candle_q_dim_interval_list_scale_normalized
           (candle_q_interval_lookup i xs) ys`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_outer_map; LENGTH_MAP; EL_MAP;
               candle_q_interval_lookup_in_range;
               candle_q_dim_interval_row_lookup_in_range]);;

let candle_q_dim_interval_rows_width_def = define
 `(candle_q_dim_interval_rows_width n
     ([]:((((num#num)#num)#((num#num)#num))list)list) <=> T) /\
  (candle_q_dim_interval_rows_width n (CONS h t) <=>
     LENGTH h = n /\ candle_q_dim_interval_rows_width n t)`;;

let candle_q_dim_interval_matrix_shape_def = new_definition
 `candle_q_dim_interval_matrix_shape n
    (row_lists:((((num#num)#num)#((num#num)#num))list)list) <=>
    LENGTH row_lists = n /\
    candle_q_dim_interval_rows_width n row_lists`;;

let candle_q_dim_interval_rows_width_all = prove
 (`!n row_lists.
     candle_q_dim_interval_rows_width n row_lists <=>
     ALL (\row. LENGTH row = n) row_lists`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_interval_rows_width_def; ALL]);;

let candle_q_dim_interval_rows_width_lookup_length = prove
 (`!n row_lists i.
     candle_q_dim_interval_rows_width n row_lists /\ i < LENGTH row_lists
     ==> LENGTH (candle_q_dim_interval_row_lookup i row_lists) = n`,
  REWRITE_TAC[candle_q_dim_interval_rows_width_all; GSYM ALL_EL] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_row_lookup_in_range]);;

let candle_q_dim_jet_shape_def = new_definition
 `candle_q_dim_jet_shape n jet <=>
    LENGTH (candle_q_dim_jet_gradient jet) = n /\
    candle_q_dim_interval_matrix_shape n (candle_q_dim_jet_hessian jet)`;;

let candle_q_dim_interval_zero_matrix_like_rows_width = prove
 (`!width row_lists.
     candle_q_dim_interval_rows_width (LENGTH width)
       (candle_q_dim_interval_zero_matrix_like width row_lists)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_interval_zero_matrix_like_def;
                  candle_q_dim_interval_rows_width_def;
                  candle_q_dim_interval_zeros_like_map; LENGTH_MAP]);;

let candle_q_dim_interval_zero_matrix_like_shape = prove
 (`!boxes.
     candle_q_dim_interval_matrix_shape (LENGTH boxes)
       (candle_q_dim_interval_zero_matrix_like boxes boxes)`,
  REWRITE_TAC[candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_interval_zero_matrix_like_map;
              LENGTH_MAP;
              candle_q_dim_interval_zero_matrix_like_rows_width]);;

let candle_q_dim_jet_normalized_constant_shape = prove
 (`!boxes q.
     candle_q_dim_jet_shape (LENGTH boxes)
       (candle_q_dim_jet_normalized_constant boxes q)`,
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_normalized_constant_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_q_dim_interval_zeros_like_map; LENGTH_MAP;
              candle_q_dim_interval_zero_matrix_like_shape]);;

let candle_q_dim_jet_normalized_variable_shape = prove
 (`!boxes variable.
     candle_q_dim_jet_shape (LENGTH boxes)
       (candle_q_dim_jet_normalized_variable boxes variable)`,
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_normalized_variable_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_q_dim_interval_unit_like_length;
              candle_q_dim_interval_zero_matrix_like_shape]);;

let candle_q_dim_interval_list_neg_length = prove
 (`!items.
     LENGTH (candle_q_dim_interval_list_neg items) = LENGTH items`,
  REWRITE_TAC[candle_q_dim_interval_list_neg_map; LENGTH_MAP]);;

let candle_q_dim_interval_list_add_length = prove
 (`!xs ys.
     LENGTH xs = LENGTH ys
     ==> LENGTH (candle_q_dim_interval_list_add_normalized xs ys) =
         LENGTH xs`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_add_map2; LENGTH_MAP2]);;

let candle_q_dim_interval_list_scale_length = prove
 (`!q items.
     LENGTH (candle_q_dim_interval_list_scale_normalized q items) =
     LENGTH items`,
  REWRITE_TAC[candle_q_dim_interval_list_scale_map; LENGTH_MAP]);;

let candle_q_dim_interval_list_neg_lookup = prove
 (`!items i.
     i < LENGTH items
     ==> candle_q_interval_lookup i
           (candle_q_dim_interval_list_neg items) =
         candle_q_interval_neg (candle_q_interval_lookup i items)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_neg_map; LENGTH_MAP; EL_MAP;
               candle_q_interval_lookup_in_range]);;

let candle_q_dim_interval_list_add_lookup = prove
 (`!xs ys i.
     LENGTH xs = LENGTH ys /\ i < LENGTH xs
     ==> candle_q_interval_lookup i
           (candle_q_dim_interval_list_add_normalized xs ys) =
         candle_q_interval_add_normalized
           (candle_q_interval_lookup i xs)
           (candle_q_interval_lookup i ys)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `i < LENGTH
      (ys:(((num#num)#num)#((num#num)#num))list)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_add_map2; LENGTH_MAP2; EL_MAP2;
               candle_q_interval_lookup_in_range]);;

let candle_q_dim_interval_list_scale_lookup = prove
 (`!q items i.
     i < LENGTH items
     ==> candle_q_interval_lookup i
           (candle_q_dim_interval_list_scale_normalized q items) =
         candle_q_interval_mul_normalized q
           (candle_q_interval_lookup i items)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_scale_map; LENGTH_MAP; EL_MAP;
               candle_q_interval_lookup_in_range]);;

let candle_q_dim_interval_matrix_neg_rows_width = prove
 (`!n row_lists.
     candle_q_dim_interval_rows_width n row_lists
     ==> candle_q_dim_interval_rows_width n
           (candle_q_dim_interval_matrix_neg row_lists)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_q_dim_interval_rows_width_def;
                candle_q_dim_interval_matrix_neg_def];
    REWRITE_TAC[candle_q_dim_interval_rows_width_def;
                candle_q_dim_interval_matrix_neg_def] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[candle_q_dim_interval_list_neg_length] THEN
    ASM_MESON_TAC[]]);;

let candle_q_dim_interval_matrix_neg_shape = prove
 (`!n row_lists.
     candle_q_dim_interval_matrix_shape n row_lists
     ==> candle_q_dim_interval_matrix_shape n
           (candle_q_dim_interval_matrix_neg row_lists)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_interval_matrix_shape_def] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_dim_interval_matrix_neg_map; LENGTH_MAP];
    MATCH_MP_TAC candle_q_dim_interval_matrix_neg_rows_width THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_dim_interval_matrix_scale_rows_width = prove
 (`!n q row_lists.
     candle_q_dim_interval_rows_width n row_lists
     ==> candle_q_dim_interval_rows_width n
           (candle_q_dim_interval_matrix_scale_normalized q row_lists)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_q_dim_interval_rows_width_def;
                candle_q_dim_interval_matrix_scale_normalized_def];
    REWRITE_TAC[candle_q_dim_interval_rows_width_def;
                candle_q_dim_interval_matrix_scale_normalized_def] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[candle_q_dim_interval_list_scale_length] THEN
    ASM_MESON_TAC[]]);;

let candle_q_dim_interval_matrix_scale_shape = prove
 (`!n q row_lists.
     candle_q_dim_interval_matrix_shape n row_lists
     ==> candle_q_dim_interval_matrix_shape n
           (candle_q_dim_interval_matrix_scale_normalized q row_lists)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_interval_matrix_shape_def] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_dim_interval_matrix_scale_map; LENGTH_MAP];
    MATCH_MP_TAC candle_q_dim_interval_matrix_scale_rows_width THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_dim_interval_matrix_add_rows_width = prove
 (`!n xs ys.
     LENGTH xs = LENGTH ys /\
     candle_q_dim_interval_rows_width n xs /\
     candle_q_dim_interval_rows_width n ys
     ==> candle_q_dim_interval_rows_width n
           (candle_q_dim_interval_matrix_add_normalized xs ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; NOT_SUC;
                candle_q_dim_interval_rows_width_def;
                candle_q_dim_interval_matrix_add_normalized_def];
    LIST_INDUCT_TAC THENL
     [REWRITE_TAC[LENGTH; NOT_SUC];
      REWRITE_TAC[LENGTH; SUC_INJ;
                  candle_q_dim_interval_rows_width_def;
                  candle_q_dim_interval_matrix_add_normalized_def] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[candle_q_dim_interval_list_add_length];
        ASM_MESON_TAC[]]]]);;

let candle_q_dim_interval_matrix_add_shape = prove
 (`!n xs ys.
     candle_q_dim_interval_matrix_shape n xs /\
     candle_q_dim_interval_matrix_shape n ys
     ==> candle_q_dim_interval_matrix_shape n
           (candle_q_dim_interval_matrix_add_normalized xs ys)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_interval_matrix_shape_def] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[candle_q_dim_interval_matrix_add_map2; LENGTH_MAP2];
    MATCH_MP_TAC candle_q_dim_interval_matrix_add_rows_width THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_dim_interval_outer_rows_width = prove
 (`!n xs ys.
     LENGTH ys = n
     ==> candle_q_dim_interval_rows_width n
           (candle_q_dim_interval_outer_normalized xs ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_q_dim_interval_rows_width_def;
                candle_q_dim_interval_outer_normalized_def];
    REWRITE_TAC[candle_q_dim_interval_rows_width_def;
                candle_q_dim_interval_outer_normalized_def] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[candle_q_dim_interval_list_scale_length] THEN
    ASM_MESON_TAC[]]);;

let candle_q_dim_interval_outer_shape = prove
  (`!n xs ys.
     LENGTH xs = n /\ LENGTH ys = n
     ==> candle_q_dim_interval_matrix_shape n
           (candle_q_dim_interval_outer_normalized xs ys)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_interval_matrix_shape_def] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_dim_interval_outer_map; LENGTH_MAP];
    MATCH_MP_TAC candle_q_dim_interval_outer_rows_width THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_dim_jet_normalized_neg_shape = prove
 (`!n a.
     candle_q_dim_jet_shape n a
     ==> candle_q_dim_jet_shape n (candle_q_dim_jet_normalized_neg a)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_normalized_neg_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_dim_interval_list_neg_length];
    MATCH_MP_TAC candle_q_dim_interval_matrix_neg_shape THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_dim_jet_normalized_add_shape = prove
 (`!n a b.
     candle_q_dim_jet_shape n a /\ candle_q_dim_jet_shape n b
     ==> candle_q_dim_jet_shape n
           (candle_q_dim_jet_normalized_add a b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_normalized_add_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[candle_q_dim_interval_list_add_length];
    MATCH_MP_TAC candle_q_dim_interval_matrix_add_shape THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_dim_jet_normalized_mul_shape = prove
 (`!n a b.
     candle_q_dim_jet_shape n a /\ candle_q_dim_jet_shape n b
     ==> candle_q_dim_jet_shape n
           (candle_q_dim_jet_normalized_mul a b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_normalized_mul_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[candle_q_dim_interval_list_add_length;
                 candle_q_dim_interval_list_scale_length];
    MATCH_MP_TAC candle_q_dim_interval_matrix_add_shape THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_interval_matrix_add_shape THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC candle_q_dim_interval_matrix_scale_shape THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC candle_q_dim_interval_outer_shape THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC candle_q_dim_interval_matrix_add_shape THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC candle_q_dim_interval_outer_shape THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC candle_q_dim_interval_matrix_scale_shape THEN
        ASM_REWRITE_TAC[]]]]);;

let candle_q_dim_jet_normalized_neg_gradient_at = prove
 (`!n a i.
     candle_q_dim_jet_shape n a /\ i < n
     ==> candle_q_dim_jet_gradient_at
           (candle_q_dim_jet_normalized_neg a) i =
         candle_q_interval_neg (candle_q_dim_jet_gradient_at a i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_normalized_neg_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_neg_lookup]);;

let candle_q_dim_jet_normalized_neg_hessian_at = prove
 (`!n a i j.
     candle_q_dim_jet_shape n a /\ i < n /\ j < n
     ==> candle_q_dim_jet_hessian_at
           (candle_q_dim_jet_normalized_neg a) i j =
         candle_q_interval_neg (candle_q_dim_jet_hessian_at a i j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_jet_normalized_neg_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_matrix_neg_row_lookup;
               candle_q_dim_interval_list_neg_lookup;
               candle_q_dim_interval_rows_width_lookup_length]);;

let candle_q_dim_jet_normalized_add_gradient_at = prove
 (`!n a b i.
     candle_q_dim_jet_shape n a /\ candle_q_dim_jet_shape n b /\ i < n
     ==> candle_q_dim_jet_gradient_at
           (candle_q_dim_jet_normalized_add a b) i =
         candle_q_interval_add_normalized
           (candle_q_dim_jet_gradient_at a i)
           (candle_q_dim_jet_gradient_at b i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_normalized_add_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_add_lookup]);;

let candle_q_dim_jet_normalized_add_hessian_at = prove
 (`!n a b i j.
     candle_q_dim_jet_shape n a /\ candle_q_dim_jet_shape n b /\
     i < n /\ j < n
     ==> candle_q_dim_jet_hessian_at
           (candle_q_dim_jet_normalized_add a b) i j =
         candle_q_interval_add_normalized
           (candle_q_dim_jet_hessian_at a i j)
           (candle_q_dim_jet_hessian_at b i j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_jet_normalized_add_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_matrix_add_row_lookup;
               candle_q_dim_interval_list_add_lookup;
               candle_q_dim_interval_rows_width_lookup_length]);;

let candle_q_dim_jet_normalized_mul_gradient_at = prove
 (`!n a b i.
     candle_q_dim_jet_shape n a /\ candle_q_dim_jet_shape n b /\ i < n
     ==> candle_q_dim_jet_gradient_at
           (candle_q_dim_jet_normalized_mul a b) i =
         candle_q_interval_add_normalized
           (candle_q_interval_mul_normalized
             (candle_q_dim_jet_f b)
             (candle_q_dim_jet_gradient_at a i))
           (candle_q_interval_mul_normalized
             (candle_q_dim_jet_f a)
             (candle_q_dim_jet_gradient_at b i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_normalized_mul_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_add_lookup;
               candle_q_dim_interval_list_scale_lookup;
               candle_q_dim_interval_list_scale_length]);;

let candle_q_dim_jet_normalized_mul_hessian_at = prove
 (`!n a b i j.
     candle_q_dim_jet_shape n a /\ candle_q_dim_jet_shape n b /\
     i < n /\ j < n
     ==> candle_q_dim_jet_hessian_at
           (candle_q_dim_jet_normalized_mul a b) i j =
         candle_q_interval_add_normalized
           (candle_q_interval_add_normalized
             (candle_q_interval_mul_normalized
               (candle_q_dim_jet_f b)
               (candle_q_dim_jet_hessian_at a i j))
             (candle_q_interval_mul_normalized
               (candle_q_dim_jet_gradient_at a i)
               (candle_q_dim_jet_gradient_at b j)))
           (candle_q_interval_add_normalized
             (candle_q_interval_mul_normalized
               (candle_q_dim_jet_gradient_at b i)
               (candle_q_dim_jet_gradient_at a j))
             (candle_q_interval_mul_normalized
               (candle_q_dim_jet_f a)
               (candle_q_dim_jet_hessian_at b i j)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_jet_normalized_mul_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_matrix_add_row_lookup;
               candle_q_dim_interval_matrix_scale_row_lookup;
               candle_q_dim_interval_outer_row_lookup;
               candle_q_dim_interval_list_add_lookup;
               candle_q_dim_interval_list_scale_lookup;
               candle_q_dim_interval_matrix_add_map2; LENGTH_MAP2;
               candle_q_dim_interval_matrix_scale_map;
               candle_q_dim_interval_outer_map; LENGTH_MAP;
               candle_q_dim_interval_list_add_length;
               candle_q_dim_interval_list_scale_length;
               candle_q_dim_interval_rows_width_lookup_length]);;

let candle_q_dim_jet_normalized_neg_sound = prove
 (`!n a env e.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_poly_jet_contains n a env e
     ==> candle_q_dim_poly_jet_contains n
           (candle_q_dim_jet_normalized_neg a) env (Candle_poly_neg e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_poly_jet_contains_def;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_q_dim_jet_f_def]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_jet_normalized_neg_def;
                candle_q_dim_jet_f_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    MATCH_MP_TAC candle_q_interval_neg_sound THEN
    ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[candle_q_dim_jet_normalized_neg_gradient_at;
                    candle_q_interval_neg_sound];
      REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[candle_q_dim_jet_normalized_neg_hessian_at;
                    candle_q_interval_neg_sound]]]);;

let candle_q_dim_jet_normalized_add_sound = prove
 (`!n a b env ea eb.
     candle_q_dim_jet_shape n a /\ candle_q_dim_jet_shape n b /\
     candle_q_dim_poly_jet_contains n a env ea /\
     candle_q_dim_poly_jet_contains n b env eb
     ==> candle_q_dim_poly_jet_contains n
           (candle_q_dim_jet_normalized_add a b) env
           (Candle_poly_add ea eb)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_poly_jet_contains_def;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_q_dim_jet_f_def]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_jet_normalized_add_def;
                candle_q_dim_jet_f_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
    ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[candle_q_dim_jet_normalized_add_gradient_at;
                    candle_q_interval_add_normalized_sound];
      REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[candle_q_dim_jet_normalized_add_hessian_at;
                    candle_q_interval_add_normalized_sound]]]);;

let candle_q_dim_jet_normalized_mul_sound = prove
 (`!n a b env ea eb.
     candle_q_dim_jet_shape n a /\ candle_q_dim_jet_shape n b /\
     candle_q_dim_poly_jet_contains n a env ea /\
     candle_q_dim_poly_jet_contains n b env eb
     ==> candle_q_dim_poly_jet_contains n
           (candle_q_dim_jet_normalized_mul a b) env
           (Candle_poly_mul ea eb)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_poly_jet_contains_def;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[candle_q_dim_jet_f_def]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_jet_normalized_mul_def;
                candle_q_dim_jet_f_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
    ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `candle_q_dim_jet_gradient_at
          (candle_q_dim_jet_normalized_mul a b) di =
        candle_q_interval_add_normalized
          (candle_q_interval_mul_normalized
            (candle_q_dim_jet_f b)
            (candle_q_dim_jet_gradient_at a di))
          (candle_q_interval_mul_normalized
            (candle_q_dim_jet_f a)
            (candle_q_dim_jet_gradient_at b di))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC
          (SPEC `n:num` candle_q_dim_jet_normalized_mul_gradient_at) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[candle_q_dim_jet_f_def] THEN
        MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC candle_q_interval_mul_normalized_sound_swapped THEN
          ASM_MESON_TAC[];
          MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
          ASM_MESON_TAC[]]];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `candle_q_dim_jet_hessian_at
          (candle_q_dim_jet_normalized_mul a b) di dj =
        candle_q_interval_add_normalized
          (candle_q_interval_add_normalized
            (candle_q_interval_mul_normalized
              (candle_q_dim_jet_f b)
              (candle_q_dim_jet_hessian_at a di dj))
            (candle_q_interval_mul_normalized
              (candle_q_dim_jet_gradient_at a di)
              (candle_q_dim_jet_gradient_at b dj)))
          (candle_q_interval_add_normalized
            (candle_q_interval_mul_normalized
              (candle_q_dim_jet_gradient_at b di)
              (candle_q_dim_jet_gradient_at a dj))
            (candle_q_interval_mul_normalized
              (candle_q_dim_jet_f a)
              (candle_q_dim_jet_hessian_at b di dj)))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC
          (SPEC `n:num` candle_q_dim_jet_normalized_mul_hessian_at) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[candle_q_dim_jet_f_def] THEN
        MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC candle_q_interval_mul_normalized_sound_swapped THEN
            ASM_MESON_TAC[];
            MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
            ASM_MESON_TAC[]];
          MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC candle_q_interval_mul_normalized_sound_swapped THEN
            ASM_MESON_TAC[];
            MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
            ASM_MESON_TAC[]]]]]]);;

let candle_q_dim_poly_jet_contains_square = prove
 (`!n jet env e.
     candle_q_dim_poly_jet_contains n jet env (Candle_poly_square e) <=>
     candle_q_dim_poly_jet_contains n jet env (Candle_poly_mul e e)`,
  REWRITE_TAC[candle_q_dim_poly_jet_contains_def;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def]);;

let candle_q_dim_jet_normalized_square_sound = prove
 (`!n a env e.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_poly_jet_contains n a env e
     ==> candle_q_dim_poly_jet_contains n
           (candle_q_dim_jet_normalized_mul a a) env
           (Candle_poly_square e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_poly_jet_contains_square] THEN
  MATCH_MP_TAC candle_q_dim_jet_normalized_mul_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_q_dim_jet_normalized_constant_sound = prove
 (`!p numerator denominator boxes env.
     candle_q_dim_poly_jet_contains (LENGTH boxes)
       (candle_q_dim_jet_normalized_constant boxes
         ((p,numerator),denominator)) env
       (Candle_poly_const p numerator denominator)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_poly_jet_contains_def;
              candle_q_dim_jet_normalized_constant_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_zeros_like_lookup;
               candle_q_dim_interval_zero_matrix_like_lookup;
               candle_q_exact_interval_contains;
               candle_q_zero_interval_contains]);;

let candle_q_dim_jet_normalized_variable_sound = prove
 (`!variable boxes env.
     candle_q_stack_contains boxes env
     ==> candle_q_dim_poly_jet_contains (LENGTH boxes)
           (candle_q_dim_jet_normalized_variable boxes variable) env
           (Candle_poly_var variable)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_dim_poly_jet_contains_def;
              candle_q_dim_jet_normalized_variable_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND;
              candle_poly_value_list_def;
              candle_poly_d_list_def;
              candle_poly_dd_list_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_stack_lookup_contains THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[candle_q_dim_interval_unit_like_lookup] THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC[candle_q_one_interval_contains;
                      candle_q_zero_interval_contains];
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[candle_q_dim_interval_zero_matrix_like_lookup;
                   candle_q_zero_interval_contains]]]);;

(* The source evaluator mirrors the normalized executable operations while   *)
(* retaining the authenticated polynomial expression as its input.           *)

let candle_q_dim_poly_jet_normalized_def = define
 `(candle_q_dim_poly_jet_normalized boxes (Candle_poly_const p n d) =
     candle_q_dim_jet_normalized_constant boxes ((p,n),d)) /\
  (candle_q_dim_poly_jet_normalized boxes (Candle_poly_var i) =
     candle_q_dim_jet_normalized_variable boxes i) /\
  (candle_q_dim_poly_jet_normalized boxes (Candle_poly_neg a) =
     candle_q_dim_jet_normalized_neg
       (candle_q_dim_poly_jet_normalized boxes a)) /\
  (candle_q_dim_poly_jet_normalized boxes (Candle_poly_add a b) =
     candle_q_dim_jet_normalized_add
       (candle_q_dim_poly_jet_normalized boxes a)
       (candle_q_dim_poly_jet_normalized boxes b)) /\
  (candle_q_dim_poly_jet_normalized boxes (Candle_poly_mul a b) =
     candle_q_dim_jet_normalized_mul
       (candle_q_dim_poly_jet_normalized boxes a)
       (candle_q_dim_poly_jet_normalized boxes b)) /\
  (candle_q_dim_poly_jet_normalized boxes (Candle_poly_square a) =
     candle_q_dim_jet_normalized_mul
       (candle_q_dim_poly_jet_normalized boxes a)
       (candle_q_dim_poly_jet_normalized boxes a))`;;

let candle_q_dim_poly_jet_normalized_shape = prove
 (`!e boxes.
     candle_q_dim_jet_shape (LENGTH boxes)
       (candle_q_dim_poly_jet_normalized boxes e)`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_poly_jet_normalized_def;
                  candle_q_dim_jet_normalized_constant_shape;
                  candle_q_dim_jet_normalized_variable_shape;
                  candle_q_dim_jet_normalized_neg_shape;
                  candle_q_dim_jet_normalized_add_shape;
                  candle_q_dim_jet_normalized_mul_shape] THEN
  ASM_MESON_TAC[candle_q_dim_jet_normalized_neg_shape;
                candle_q_dim_jet_normalized_add_shape;
                candle_q_dim_jet_normalized_mul_shape]);;

let candle_q_dim_poly_jet_normalized_sound = prove
 (`!e boxes env.
     candle_q_stack_contains boxes env
     ==> candle_q_dim_poly_jet_contains (LENGTH boxes)
           (candle_q_dim_poly_jet_normalized boxes e) env e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[candle_q_dim_poly_jet_normalized_def] THEN
    MATCH_ACCEPT_TAC candle_q_dim_jet_normalized_constant_sound;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[candle_q_dim_poly_jet_normalized_def] THEN
    MATCH_MP_TAC candle_q_dim_jet_normalized_variable_sound THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih -> REPEAT GEN_TAC THEN DISCH_TAC THEN
                ASSUME_TAC
                 (MATCH_MP
                   (SPECL
                     [`boxes:(((num#num)#num)#((num#num)#num))list`;
                      `env:real list`] ih)
                   (ASSUME `candle_q_stack_contains boxes env`))) THEN
    REWRITE_TAC[candle_q_dim_poly_jet_normalized_def] THEN
    MATCH_MP_TAC candle_q_dim_jet_normalized_neg_sound THEN
    CONJ_TAC THENL
     [MATCH_ACCEPT_TAC candle_q_dim_poly_jet_normalized_shape;
      ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN DISCH_TAC THEN
        ASSUME_TAC
         (MATCH_MP
           (SPECL
             [`boxes:(((num#num)#num)#((num#num)#num))list`;
              `env:real list`] iha)
           (ASSUME `candle_q_stack_contains boxes env`)) THEN
        ASSUME_TAC
         (MATCH_MP
           (SPECL
             [`boxes:(((num#num)#num)#((num#num)#num))list`;
              `env:real list`] ihb)
           (ASSUME `candle_q_stack_contains boxes env`))) THEN
    REWRITE_TAC[candle_q_dim_poly_jet_normalized_def] THEN
    MATCH_MP_TAC candle_q_dim_jet_normalized_add_sound THEN
    REPEAT CONJ_TAC THENL
     [MATCH_ACCEPT_TAC candle_q_dim_poly_jet_normalized_shape;
      MATCH_ACCEPT_TAC candle_q_dim_poly_jet_normalized_shape;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN DISCH_TAC THEN
        ASSUME_TAC
         (MATCH_MP
           (SPECL
             [`boxes:(((num#num)#num)#((num#num)#num))list`;
              `env:real list`] iha)
           (ASSUME `candle_q_stack_contains boxes env`)) THEN
        ASSUME_TAC
         (MATCH_MP
           (SPECL
             [`boxes:(((num#num)#num)#((num#num)#num))list`;
              `env:real list`] ihb)
           (ASSUME `candle_q_stack_contains boxes env`))) THEN
    REWRITE_TAC[candle_q_dim_poly_jet_normalized_def] THEN
    MATCH_MP_TAC candle_q_dim_jet_normalized_mul_sound THEN
    REPEAT CONJ_TAC THENL
     [MATCH_ACCEPT_TAC candle_q_dim_poly_jet_normalized_shape;
      MATCH_ACCEPT_TAC candle_q_dim_poly_jet_normalized_shape;
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih -> REPEAT GEN_TAC THEN DISCH_TAC THEN
                ASSUME_TAC
                 (MATCH_MP
                   (SPECL
                     [`boxes:(((num#num)#num)#((num#num)#num))list`;
                      `env:real list`] ih)
                   (ASSUME `candle_q_stack_contains boxes env`))) THEN
    REWRITE_TAC[candle_q_dim_poly_jet_normalized_def] THEN
    MATCH_MP_TAC candle_q_dim_jet_normalized_square_sound THEN
    CONJ_TAC THENL
     [MATCH_ACCEPT_TAC candle_q_dim_poly_jet_normalized_shape;
      ASM_REWRITE_TAC[]]]);;

let candle_q_dim_jet_normalized_run_append = prove
 (`!left right boxes stack.
     candle_q_dim_jet_normalized_run boxes (APPEND left right) stack =
     candle_q_dim_jet_normalized_run boxes right
       (candle_q_dim_jet_normalized_run boxes left stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; candle_q_dim_jet_normalized_run_def]);;

let candle_q_dim_poly_compile_normalized_jet_run = prove
 (`!e boxes stack.
     candle_q_dim_jet_normalized_run boxes (candle_poly_compile e) stack =
     CONS (candle_q_dim_poly_jet_normalized boxes e) stack`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_poly_compile_def;
                  candle_q_dim_poly_jet_normalized_def;
                  candle_q_dim_jet_normalized_run_append;
                  candle_q_dim_jet_normalized_run_def;
                  candle_q_dim_jet_normalized_step_def;
                  candle_q_dim_jet_normalized_head_def;
                  candle_q_dim_jet_normalized_tail_def; APPEND]);;

let candle_q_dim_poly_compile_normalized_jet_program = prove
 (`!e boxes.
     candle_q_dim_jet_normalized_program boxes (candle_poly_compile e) =
     candle_q_dim_poly_jet_normalized boxes e`,
  REWRITE_TAC[candle_q_dim_jet_normalized_program_def;
              candle_q_dim_poly_compile_normalized_jet_run;
              candle_q_dim_jet_normalized_head_def]);;

let candle_cv_q_dim_poly_compile_program_correct = prove
 (`!e boxes.
     candle_cv_q_dim_jet_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list (candle_poly_compile e)) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_poly_jet_normalized boxes e)`,
  REWRITE_TAC[candle_cv_q_dim_jet_program_correct;
              candle_q_dim_poly_compile_normalized_jet_program]);;

let candle_cv_q_dim_poly_compile_program_sound = prove
 (`!e boxes env.
     candle_q_stack_contains boxes env
     ==> ?jet.
           candle_cv_q_dim_jet_program
             (candle_cv_q_interval_list boxes)
             (candle_cv_q_instruction_list (candle_poly_compile e)) =
           candle_cv_q_dim_jet_encode jet /\
           candle_q_dim_poly_jet_contains (LENGTH boxes) jet env e`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `candle_q_dim_poly_jet_normalized boxes e` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[candle_cv_q_dim_poly_compile_program_correct];
    MATCH_MP_TAC candle_q_dim_poly_jet_normalized_sound THEN
    ASM_REWRITE_TAC[]]);;

end;;
