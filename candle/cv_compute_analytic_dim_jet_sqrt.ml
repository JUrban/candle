(* ========================================================================== *)
(* Guarded square root for dimension-generic reflected interval jets.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The rational enclosure of sqrt(f) is supplied *)
(* as data and authenticated by the reflected squared-endpoint certificate.  *)
(* The derivative denominators are checked separately before this adapter can *)
(* authorize its component theorem.                                           *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_sqrt_certificate.ml";;
needs "candle/cv_compute_analytic_dim_jet_inv.ml";;

module Candle_cv_analytic_dim_jet_sqrt = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_inv_core;;
open Candle_cv_exact_interval_sqrt_certificate;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;

(* Flyspeck's Taylor square-root rule uses

     d  = 1 / (2 sqrt(f))
     dd = -1 / ((2 sqrt(f)) (2 f)).

   Writing the factors as interval additions avoids any new trusted scalar
   encoding and lets the existing exact interval operations prove each step. *)

let candle_q_dim_jet_sqrt_d_def = new_definition
 `candle_q_dim_jet_sqrt_d s =
    candle_q_interval_inv (candle_q_interval_add_normalized s s)`;;

let candle_q_dim_jet_sqrt_dd_def = new_definition
 `candle_q_dim_jet_sqrt_dd s f =
    candle_q_interval_neg
      (candle_q_interval_inv
        (candle_q_interval_mul_normalized
          (candle_q_interval_add_normalized s s)
          (candle_q_interval_add_normalized f f)))`;;

let candle_q_dim_jet_sqrt_with_def = new_definition
 `candle_q_dim_jet_sqrt_with s a =
    candle_q_dim_jet_make s
      (candle_q_dim_interval_list_scale_normalized
        (candle_q_dim_jet_sqrt_d s)
        (candle_q_dim_jet_gradient a))
      (candle_q_dim_interval_matrix_add_normalized
        (candle_q_dim_interval_matrix_scale_normalized
          (candle_q_dim_jet_sqrt_dd s (candle_q_dim_jet_f a))
          (candle_q_dim_interval_outer_normalized
            (candle_q_dim_jet_gradient a)
            (candle_q_dim_jet_gradient a)))
        (candle_q_dim_interval_matrix_scale_normalized
          (candle_q_dim_jet_sqrt_d s)
          (candle_q_dim_jet_hessian a)))`;;

let candle_q_dim_jet_sqrt_domain_def = new_definition
 `candle_q_dim_jet_sqrt_domain s a <=>
    candle_q_interval_sqrt_certificate (candle_q_dim_jet_f a) s /\
    candle_q_interval_not_zero (candle_q_interval_add_normalized s s) /\
    candle_q_interval_not_zero
      (candle_q_interval_mul_normalized
        (candle_q_interval_add_normalized s s)
        (candle_q_interval_add_normalized (candle_q_dim_jet_f a)
                                          (candle_q_dim_jet_f a)))`;;

let candle_cv_q_dim_jet_sqrt_d_def = new_definition
 `candle_cv_q_dim_jet_sqrt_d s =
    candle_cv_q_interval_inv (candle_cv_q_interval_add_normalized s s)`;;

let candle_cv_q_dim_jet_sqrt_dd_def = new_definition
 `candle_cv_q_dim_jet_sqrt_dd s f =
    candle_cv_q_interval_neg
      (candle_cv_q_interval_inv
        (candle_cv_q_interval_mul_normalized
          (candle_cv_q_interval_add_normalized s s)
          (candle_cv_q_interval_add_normalized f f)))`;;

let candle_cv_q_dim_jet_sqrt_with_def = new_definition
 `candle_cv_q_dim_jet_sqrt_with s a =
    candle_cv_q_dim_jet_make s
      (candle_cv_q_dim_interval_list_scale
        (candle_cv_q_dim_jet_sqrt_d s)
        (candle_cv_q_dim_jet_gradient a))
      (candle_cv_q_dim_interval_matrix_add
        (candle_cv_q_dim_interval_matrix_scale
          (candle_cv_q_dim_jet_sqrt_dd s (candle_cv_q_dim_jet_f a))
          (candle_cv_q_dim_interval_outer
            (candle_cv_q_dim_jet_gradient a)
            (candle_cv_q_dim_jet_gradient a)))
        (candle_cv_q_dim_interval_matrix_scale
          (candle_cv_q_dim_jet_sqrt_d s)
          (candle_cv_q_dim_jet_hessian a)))`;;

let candle_cv_q_dim_jet_sqrt_domain_def = new_definition
 `candle_cv_q_dim_jet_sqrt_domain s a =
    Cexp_if
      (candle_cv_q_interval_sqrt_certificate
        (candle_cv_q_dim_jet_f a) s)
      (Cexp_if
        (candle_cv_q_interval_not_zero
          (candle_cv_q_interval_add_normalized s s))
        (candle_cv_q_interval_not_zero
          (candle_cv_q_interval_mul_normalized
            (candle_cv_q_interval_add_normalized s s)
            (candle_cv_q_interval_add_normalized
              (candle_cv_q_dim_jet_f a) (candle_cv_q_dim_jet_f a))))
        (Cexp_num 0))
      (Cexp_num 0)`;;

let candle_cv_q_dim_jet_sqrt_compute_eqs =
  candle_cv_q_dim_jet_inv_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_interval_sqrt_certificate_def;
    candle_cv_q_dim_jet_sqrt_d_def;
    candle_cv_q_dim_jet_sqrt_dd_def;
    candle_cv_q_dim_jet_sqrt_with_def;
    candle_cv_q_dim_jet_sqrt_domain_def];;

let candle_cv_q_dim_jet_sqrt_d_correct = prove
 (`!s.
     candle_cv_q_dim_jet_sqrt_d (candle_cv_q_interval s) =
     candle_cv_q_interval (candle_q_dim_jet_sqrt_d s)`,
  REWRITE_TAC[candle_cv_q_dim_jet_sqrt_d_def;
              candle_q_dim_jet_sqrt_d_def;
              candle_cv_q_interval_add_normalized_correct;
              candle_cv_q_interval_inv_correct]);;

let candle_cv_q_dim_jet_sqrt_dd_correct = prove
 (`!s f.
     candle_cv_q_dim_jet_sqrt_dd
       (candle_cv_q_interval s) (candle_cv_q_interval f) =
     candle_cv_q_interval (candle_q_dim_jet_sqrt_dd s f)`,
  REWRITE_TAC[candle_cv_q_dim_jet_sqrt_dd_def;
              candle_q_dim_jet_sqrt_dd_def;
              candle_cv_q_interval_add_normalized_correct;
              candle_cv_q_interval_mul_normalized_correct;
              candle_cv_q_interval_inv_correct;
              candle_cv_q_interval_neg_correct]);;

let candle_cv_q_dim_jet_sqrt_with_correct = prove
 (`!s a.
     candle_cv_q_dim_jet_sqrt_with
       (candle_cv_q_interval s) (candle_cv_q_dim_jet_encode a) =
     candle_cv_q_dim_jet_encode (candle_q_dim_jet_sqrt_with s a)`,
  REWRITE_TAC[candle_cv_q_dim_jet_sqrt_with_def;
              candle_q_dim_jet_sqrt_with_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_dim_jet_gradient_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_dim_jet_sqrt_d_correct;
              candle_cv_q_dim_jet_sqrt_dd_correct;
              candle_cv_q_dim_interval_list_scale_correct;
              candle_cv_q_dim_interval_outer_correct;
              candle_cv_q_dim_interval_matrix_scale_correct;
              candle_cv_q_dim_interval_matrix_add_correct;
              candle_cv_q_dim_jet_make_correct]);;

let candle_cv_q_dim_jet_sqrt_if_one = prove
 (`!p q. Cexp_if (Cexp_num 1) p q = p`,
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; cexp_if_def]);;

let candle_cv_q_dim_jet_sqrt_domain_correct = prove
 (`!s a.
     candle_cv_q_dim_jet_sqrt_domain
       (candle_cv_q_interval s) (candle_cv_q_dim_jet_encode a) =
     Cexp_num (if candle_q_dim_jet_sqrt_domain s a then 1 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_sqrt_domain_def;
              candle_q_dim_jet_sqrt_domain_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_interval_sqrt_certificate_correct;
              candle_cv_q_interval_add_normalized_correct;
              candle_cv_q_interval_mul_normalized_correct;
              candle_cv_q_interval_not_zero_correct] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]) THEN
  REWRITE_TAC[candle_cv_q_dim_jet_sqrt_if_one]);;

let candle_q_dim_jet_sqrt_shape = prove
 (`!n s a.
     candle_q_dim_jet_shape n a
     ==> candle_q_dim_jet_shape n (candle_q_dim_jet_sqrt_with s a)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_sqrt_with_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_q_dim_interval_list_scale_length];
    MATCH_MP_TAC candle_q_dim_interval_matrix_add_shape THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_interval_matrix_scale_shape THEN
      MATCH_MP_TAC candle_q_dim_interval_outer_shape THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC candle_q_dim_interval_matrix_scale_shape THEN
      ASM_REWRITE_TAC[]]]);;

let candle_q_dim_jet_sqrt_gradient_at = prove
 (`!n s a i.
     candle_q_dim_jet_shape n a /\ i < n
     ==> candle_q_dim_jet_gradient_at
           (candle_q_dim_jet_sqrt_with s a) i =
         candle_q_interval_mul_normalized
           (candle_q_dim_jet_sqrt_d s)
           (candle_q_dim_jet_gradient_at a i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_sqrt_with_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_scale_lookup]);;

let candle_q_dim_jet_sqrt_hessian_at = prove
 (`!n s a i j.
     candle_q_dim_jet_shape n a /\ i < n /\ j < n
     ==> candle_q_dim_jet_hessian_at
           (candle_q_dim_jet_sqrt_with s a) i j =
         candle_q_interval_add_normalized
           (candle_q_interval_mul_normalized
             (candle_q_dim_jet_sqrt_dd s (candle_q_dim_jet_f a))
             (candle_q_interval_mul_normalized
               (candle_q_dim_jet_gradient_at a i)
               (candle_q_dim_jet_gradient_at a j)))
           (candle_q_interval_mul_normalized
             (candle_q_dim_jet_sqrt_d s)
             (candle_q_dim_jet_hessian_at a i j))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_jet_sqrt_with_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_f_def;
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

let candle_q_dim_jet_sqrt_double_sound = prove
 (`!s input x.
     candle_q_interval_sqrt_certificate input s /\
     candle_q_interval_contains input x
     ==> candle_q_interval_contains
           (candle_q_interval_add_normalized s s)
           (sqrt x + sqrt x)`,
  MESON_TAC[candle_q_interval_sqrt_certificate_sound;
            candle_q_interval_add_normalized_sound]);;

let candle_q_dim_jet_input_double_sound = prove
 (`!input x.
     candle_q_interval_contains input x
     ==> candle_q_interval_contains
           (candle_q_interval_add_normalized input input) (x + x)`,
  MESON_TAC[candle_q_interval_add_normalized_sound]);;

let candle_q_dim_jet_sqrt_d_sound = prove
 (`!s input x.
     candle_q_interval_sqrt_certificate input s /\
     candle_q_interval_not_zero (candle_q_interval_add_normalized s s) /\
     candle_q_interval_contains input x
     ==> candle_q_interval_contains (candle_q_dim_jet_sqrt_d s)
           (inv (sqrt x + sqrt x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_sqrt_d_def] THEN
  STRIP_TAC THEN MATCH_MP_TAC candle_q_interval_inv_sound THEN
  ASM_MESON_TAC[candle_q_dim_jet_sqrt_double_sound]);;

let candle_q_dim_jet_sqrt_dd_sound = prove
 (`!s input x.
     candle_q_interval_sqrt_certificate input s /\
     candle_q_interval_not_zero
       (candle_q_interval_mul_normalized
         (candle_q_interval_add_normalized s s)
         (candle_q_interval_add_normalized input input)) /\
     candle_q_interval_contains input x
     ==> candle_q_interval_contains (candle_q_dim_jet_sqrt_dd s input)
           (--inv ((sqrt x + sqrt x) * (x + x)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_sqrt_dd_def] THEN
  STRIP_TAC THEN MATCH_MP_TAC candle_q_interval_neg_sound THEN
  MATCH_MP_TAC candle_q_interval_inv_sound THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[candle_q_dim_jet_sqrt_double_sound];
    ASM_MESON_TAC[candle_q_dim_jet_input_double_sound]]);;

let candle_q_dim_jet_sqrt_value_sound = prove
 (`!n s a value gradient hessian.
     candle_q_dim_jet_sqrt_domain s a /\
     candle_q_dim_jet_contains_components n a value gradient hessian
     ==> candle_q_interval_contains
           (candle_q_dim_jet_f (candle_q_dim_jet_sqrt_with s a))
           (sqrt value)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_sqrt_domain_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_dim_jet_sqrt_with_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  MESON_TAC[candle_q_interval_sqrt_certificate_sound]);;

let candle_q_dim_jet_sqrt_gradient_sound = prove
 (`!n s a value gradient hessian i.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_sqrt_domain s a /\
     candle_q_dim_jet_contains_components n a value gradient hessian /\
     i < n
     ==> candle_q_interval_contains
           (candle_q_dim_jet_gradient_at
             (candle_q_dim_jet_sqrt_with s a) i)
           (inv (sqrt value + sqrt value) * gradient i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_sqrt_domain_def;
              candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[candle_q_dim_jet_sqrt_gradient_at;
                candle_q_dim_jet_sqrt_d_sound;
                candle_q_interval_mul_normalized_sound]);;

let candle_q_dim_jet_sqrt_hessian_sound = prove
 (`!n s a value gradient hessian i j.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_sqrt_domain s a /\
     candle_q_dim_jet_contains_components n a value gradient hessian /\
     i < n /\ j < n
     ==> candle_q_interval_contains
           (candle_q_dim_jet_hessian_at
             (candle_q_dim_jet_sqrt_with s a) i j)
           ((--inv ((sqrt value + sqrt value) * (value + value))) *
              (gradient i * gradient j) +
            inv (sqrt value + sqrt value) * hessian i j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_sqrt_domain_def;
              candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[candle_q_dim_jet_sqrt_hessian_at;
                candle_q_dim_jet_sqrt_d_sound;
                candle_q_dim_jet_sqrt_dd_sound;
                candle_q_interval_mul_normalized_sound;
                candle_q_interval_add_normalized_sound]);;

let candle_q_dim_jet_sqrt_components_sound = prove
 (`!n s a value gradient hessian.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_sqrt_domain s a /\
     candle_q_dim_jet_contains_components n a value gradient hessian
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_jet_sqrt_with s a)
           (sqrt value)
           (\i. inv (sqrt value + sqrt value) * gradient i)
           (\i j.
              (--inv ((sqrt value + sqrt value) * (value + value))) *
                (gradient i * gradient j) +
              inv (sqrt value + sqrt value) * hessian i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[candle_q_dim_jet_sqrt_value_sound];
    ASM_MESON_TAC[candle_q_dim_jet_sqrt_gradient_sound];
    ASM_MESON_TAC[candle_q_dim_jet_sqrt_hessian_sound]]);;

end;;
