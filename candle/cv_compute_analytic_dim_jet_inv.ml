(* ========================================================================== *)
(* Guarded reciprocal for dimension-generic reflected interval jets.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the first analytic constructor above  *)
(* the polynomial shared-jet evaluator.  Its input and output remain data; a *)
(* separate, exact domain result prevents an interval crossing zero from     *)
(* authorizing the semantic theorem.                                         *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_inv_core.ml";;
needs "candle/cv_compute_polynomial_expr_dim_jet_semantics.ml";;

module Candle_cv_analytic_dim_jet_inv = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_rational_inv;;
open Candle_cv_exact_interval_inv_core;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;

(* If r encloses inv f, then

     D(inv f)       = -(inv f)^2 Df
     D2(inv f)      = -(inv f)^2 D2f + 2(inv f)^3 Df (x) Df.

   The two terms in the Hessian are kept separate so that interval arithmetic
   can enclose them without constructing symbolic derivative programs. *)

let candle_q_dim_jet_inv_with_def = new_definition
 `candle_q_dim_jet_inv_with r a =
    candle_q_dim_jet_make r
      (candle_q_dim_interval_list_scale_normalized
        (candle_q_interval_neg
          (candle_q_interval_mul_normalized r r))
        (candle_q_dim_jet_gradient a))
      (candle_q_dim_interval_matrix_add_normalized
        (candle_q_dim_interval_matrix_scale_normalized
          (candle_q_interval_neg
            (candle_q_interval_mul_normalized r r))
          (candle_q_dim_jet_hessian a))
        (candle_q_dim_interval_matrix_scale_normalized
          (candle_q_interval_add_normalized
            (candle_q_interval_mul_normalized
              (candle_q_interval_mul_normalized r r) r)
            (candle_q_interval_mul_normalized
              (candle_q_interval_mul_normalized r r) r))
          (candle_q_dim_interval_outer_normalized
            (candle_q_dim_jet_gradient a)
            (candle_q_dim_jet_gradient a))))`;;

let candle_q_dim_jet_inv_def = new_definition
 `candle_q_dim_jet_inv a =
    candle_q_dim_jet_inv_with
      (candle_q_interval_inv (candle_q_dim_jet_f a)) a`;;

let candle_q_dim_jet_inv_domain_def = new_definition
 `candle_q_dim_jet_inv_domain a <=>
    candle_q_interval_not_zero (candle_q_dim_jet_f a)`;;

let candle_cv_q_dim_jet_inv_with_def = new_definition
 `candle_cv_q_dim_jet_inv_with r a =
    candle_cv_q_dim_jet_make r
      (candle_cv_q_dim_interval_list_scale
        (candle_cv_q_interval_neg
          (candle_cv_q_interval_mul_normalized r r))
        (candle_cv_q_dim_jet_gradient a))
      (candle_cv_q_dim_interval_matrix_add
        (candle_cv_q_dim_interval_matrix_scale
          (candle_cv_q_interval_neg
            (candle_cv_q_interval_mul_normalized r r))
          (candle_cv_q_dim_jet_hessian a))
        (candle_cv_q_dim_interval_matrix_scale
          (candle_cv_q_interval_add_normalized
            (candle_cv_q_interval_mul_normalized
              (candle_cv_q_interval_mul_normalized r r) r)
            (candle_cv_q_interval_mul_normalized
              (candle_cv_q_interval_mul_normalized r r) r))
          (candle_cv_q_dim_interval_outer
            (candle_cv_q_dim_jet_gradient a)
            (candle_cv_q_dim_jet_gradient a))))`;;

let candle_cv_q_dim_jet_inv_def = new_definition
 `candle_cv_q_dim_jet_inv a =
    candle_cv_q_dim_jet_inv_with
      (candle_cv_q_interval_inv (candle_cv_q_dim_jet_f a)) a`;;

let candle_cv_q_dim_jet_inv_domain_def = new_definition
 `candle_cv_q_dim_jet_inv_domain a =
    candle_cv_q_interval_not_zero (candle_cv_q_dim_jet_f a)`;;

let candle_cv_q_dim_jet_inv_compute_eqs =
  candle_cv_q_dim_jet_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_inv_def;
    candle_cv_q_interval_not_zero_def;
    candle_cv_q_interval_inv_def;
    candle_cv_q_dim_jet_inv_with_def;
    candle_cv_q_dim_jet_inv_def;
    candle_cv_q_dim_jet_inv_domain_def];;

let candle_cv_q_dim_jet_inv_with_correct = prove
 (`!r a.
     candle_cv_q_dim_jet_inv_with
       (candle_cv_q_interval r) (candle_cv_q_dim_jet_encode a) =
     candle_cv_q_dim_jet_encode (candle_q_dim_jet_inv_with r a)`,
  REWRITE_TAC[candle_cv_q_dim_jet_inv_with_def;
              candle_q_dim_jet_inv_with_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_dim_jet_gradient_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_interval_neg_correct;
              candle_cv_q_interval_add_normalized_correct;
              candle_cv_q_interval_mul_normalized_correct;
              candle_cv_q_dim_interval_list_scale_correct;
              candle_cv_q_dim_interval_matrix_scale_correct;
              candle_cv_q_dim_interval_outer_correct;
              candle_cv_q_dim_interval_matrix_add_correct;
              candle_cv_q_dim_jet_make_correct]);;

let candle_cv_q_dim_jet_inv_correct = prove
 (`!a.
     candle_cv_q_dim_jet_inv (candle_cv_q_dim_jet_encode a) =
     candle_cv_q_dim_jet_encode (candle_q_dim_jet_inv a)`,
  REWRITE_TAC[candle_cv_q_dim_jet_inv_def; candle_q_dim_jet_inv_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_interval_inv_correct;
              candle_cv_q_dim_jet_inv_with_correct]);;

let candle_cv_q_dim_jet_inv_domain_correct = prove
 (`!a.
     candle_cv_q_dim_jet_inv_domain (candle_cv_q_dim_jet_encode a) =
     Cexp_num (if candle_q_dim_jet_inv_domain a then 1 else 0)`,
  REWRITE_TAC[candle_cv_q_dim_jet_inv_domain_def;
              candle_q_dim_jet_inv_domain_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_interval_not_zero_correct]);;

let candle_q_dim_jet_inv_shape = prove
 (`!n a.
     candle_q_dim_jet_shape n a
     ==> candle_q_dim_jet_shape n (candle_q_dim_jet_inv a)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_inv_def;
              candle_q_dim_jet_inv_with_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_dim_interval_list_scale_length];
    MATCH_MP_TAC candle_q_dim_interval_matrix_add_shape THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_interval_matrix_scale_shape THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_dim_interval_matrix_scale_shape THEN
      MATCH_MP_TAC candle_q_dim_interval_outer_shape THEN
      ASM_REWRITE_TAC[]]]);;

let candle_q_dim_jet_inv_gradient_at = prove
 (`!n a i.
     candle_q_dim_jet_shape n a /\ i < n
     ==> candle_q_dim_jet_gradient_at (candle_q_dim_jet_inv a) i =
         candle_q_interval_mul_normalized
           (candle_q_interval_neg
             (candle_q_interval_mul_normalized
               (candle_q_interval_inv (candle_q_dim_jet_f a))
               (candle_q_interval_inv (candle_q_dim_jet_f a))))
           (candle_q_dim_jet_gradient_at a i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_inv_def;
              candle_q_dim_jet_inv_with_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_scale_lookup]);;

let candle_q_dim_jet_inv_hessian_at = prove
 (`!n a i j.
     candle_q_dim_jet_shape n a /\ i < n /\ j < n
     ==> candle_q_dim_jet_hessian_at (candle_q_dim_jet_inv a) i j =
         candle_q_interval_add_normalized
           (candle_q_interval_mul_normalized
             (candle_q_interval_neg
               (candle_q_interval_mul_normalized
                 (candle_q_interval_inv (candle_q_dim_jet_f a))
                 (candle_q_interval_inv (candle_q_dim_jet_f a))))
             (candle_q_dim_jet_hessian_at a i j))
           (candle_q_interval_mul_normalized
             (candle_q_interval_add_normalized
               (candle_q_interval_mul_normalized
                 (candle_q_interval_mul_normalized
                   (candle_q_interval_inv (candle_q_dim_jet_f a))
                   (candle_q_interval_inv (candle_q_dim_jet_f a)))
                 (candle_q_interval_inv (candle_q_dim_jet_f a)))
               (candle_q_interval_mul_normalized
                 (candle_q_interval_mul_normalized
                   (candle_q_interval_inv (candle_q_dim_jet_f a))
                   (candle_q_interval_inv (candle_q_dim_jet_f a)))
                 (candle_q_interval_inv (candle_q_dim_jet_f a))))
             (candle_q_interval_mul_normalized
               (candle_q_dim_jet_gradient_at a i)
               (candle_q_dim_jet_gradient_at a j)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_jet_inv_def;
              candle_q_dim_jet_inv_with_def;
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

(* This component contract is independent of a particular source AST and is
   the reusable boundary for inv, sqrt, atn, and future analytic nodes. *)

let candle_q_interval_inv_square_sound = prove
 (`!i x.
     candle_q_interval_not_zero i /\ candle_q_interval_contains i x
     ==> candle_q_interval_contains
           (candle_q_interval_mul_normalized
             (candle_q_interval_inv i) (candle_q_interval_inv i))
           (inv x * inv x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
  ASM_MESON_TAC[candle_q_interval_inv_sound]);;

let candle_q_interval_inv_square_neg_sound = prove
 (`!i x.
     candle_q_interval_not_zero i /\ candle_q_interval_contains i x
     ==> candle_q_interval_contains
           (candle_q_interval_neg
             (candle_q_interval_mul_normalized
               (candle_q_interval_inv i) (candle_q_interval_inv i)))
           (--(inv x * inv x))`,
  MESON_TAC[candle_q_interval_inv_square_sound;
            candle_q_interval_neg_sound]);;

let candle_q_interval_inv_cube_sound = prove
 (`!i x.
     candle_q_interval_not_zero i /\ candle_q_interval_contains i x
     ==> candle_q_interval_contains
           (candle_q_interval_mul_normalized
             (candle_q_interval_mul_normalized
               (candle_q_interval_inv i) (candle_q_interval_inv i))
             (candle_q_interval_inv i))
           ((inv x * inv x) * inv x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_interval_inv_square_sound THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_interval_inv_sound THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_interval_inv_cube_twice_sound = prove
 (`!i x.
     candle_q_interval_not_zero i /\ candle_q_interval_contains i x
     ==> candle_q_interval_contains
           (candle_q_interval_add_normalized
             (candle_q_interval_mul_normalized
               (candle_q_interval_mul_normalized
                 (candle_q_interval_inv i) (candle_q_interval_inv i))
               (candle_q_interval_inv i))
             (candle_q_interval_mul_normalized
               (candle_q_interval_mul_normalized
                 (candle_q_interval_inv i) (candle_q_interval_inv i))
               (candle_q_interval_inv i)))
           (((inv x * inv x) * inv x) +
            ((inv x * inv x) * inv x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_interval_inv_cube_sound THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_interval_inv_cube_sound THEN ASM_REWRITE_TAC[]]);;

let candle_q_dim_jet_contains_components_def = new_definition
 `candle_q_dim_jet_contains_components n jet value gradient hessian <=>
    candle_q_interval_contains (candle_q_dim_jet_f jet) value /\
    (!i. i < n
         ==> candle_q_interval_contains
               (candle_q_dim_jet_gradient_at jet i) (gradient i)) /\
    (!i j. i < n /\ j < n
           ==> candle_q_interval_contains
                 (candle_q_dim_jet_hessian_at jet i j) (hessian i j))`;;

let candle_q_dim_jet_inv_value_sound = prove
 (`!n a value gradient hessian.
     candle_q_dim_jet_inv_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian
     ==> candle_q_interval_contains
           (candle_q_dim_jet_f (candle_q_dim_jet_inv a)) (inv value)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_inv_domain_def;
              candle_q_dim_jet_contains_components_def] THEN
  REWRITE_TAC[candle_q_dim_jet_inv_def;
              candle_q_dim_jet_inv_with_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  MESON_TAC[candle_q_interval_inv_sound]);;

let candle_q_dim_jet_inv_gradient_sound = prove
 (`!n a value gradient hessian i.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_inv_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian /\
     i < n
     ==> candle_q_interval_contains
           (candle_q_dim_jet_gradient_at (candle_q_dim_jet_inv a) i)
           ((--(inv value * inv value)) * gradient i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_inv_domain_def;
              candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[candle_q_dim_jet_inv_gradient_at;
                candle_q_interval_mul_normalized_sound;
                candle_q_interval_inv_square_neg_sound]);;

let candle_q_dim_jet_inv_hessian_sound = prove
 (`!n a value gradient hessian i j.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_inv_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian /\
     i < n /\ j < n
     ==> candle_q_interval_contains
           (candle_q_dim_jet_hessian_at (candle_q_dim_jet_inv a) i j)
           ((--(inv value * inv value)) * hessian i j +
            (((inv value * inv value) * inv value) +
             ((inv value * inv value) * inv value)) *
            (gradient i * gradient j))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_inv_domain_def;
              candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[candle_q_dim_jet_inv_hessian_at;
                candle_q_interval_add_normalized_sound;
                candle_q_interval_mul_normalized_sound;
                candle_q_interval_inv_square_neg_sound;
                candle_q_interval_inv_cube_twice_sound]);;

let candle_q_dim_jet_inv_components_sound = prove
 (`!n a value gradient hessian.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_inv_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian
     ==> candle_q_dim_jet_contains_components n (candle_q_dim_jet_inv a)
           (inv value)
           (\i. (--(inv value * inv value)) * gradient i)
           (\i j.
              (--(inv value * inv value)) * hessian i j +
              (((inv value * inv value) * inv value) +
              ((inv value * inv value) * inv value)) *
              (gradient i * gradient j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[candle_q_dim_jet_inv_value_sound];
    ASM_MESON_TAC[candle_q_dim_jet_inv_gradient_sound];
    ASM_MESON_TAC[candle_q_dim_jet_inv_hessian_sound]]);;

end;;
