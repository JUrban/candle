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

let candle_q_dim_interval_zero_matrix_like_map = prove
 (`!width rows.
     candle_q_dim_interval_zero_matrix_like width rows =
     MAP (\x. candle_q_dim_interval_zeros_like width) rows`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_q_dim_interval_zero_matrix_like_def; MAP]);;

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

end;;
