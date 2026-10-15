(* ========================================================================== *)
(* Guarded crossing-zero [matan] for dimension-generic reflected jets.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The exact value, first-derivative, and        *)
(* second-derivative intervals come from the reusable [matan] series packet.  *)
(* This layer applies the ordinary unary chain rule to a complete interval    *)
(* jet and proves the reflected cval implementation represents it exactly.   *)
(* ========================================================================== *)

(* Loaded after [cv_compute_exact_interval_matan_series_program.ml] from the
   stable action-296 analytic checkpoint. *)

module Candle_cv_analytic_dim_jet_matan = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_exact_interval_matan_series;;
open Candle_cv_exact_interval_matan_series_program;;

let candle_q_dim_jet_matan_with_def = new_definition
 `candle_q_dim_jet_matan_with value_interval d_interval dd_interval a =
    candle_q_dim_jet_make value_interval
      (candle_q_dim_interval_list_scale_normalized d_interval
        (candle_q_dim_jet_gradient a))
      (candle_q_dim_interval_matrix_add_normalized
        (candle_q_dim_interval_matrix_scale_normalized dd_interval
          (candle_q_dim_interval_outer_normalized
            (candle_q_dim_jet_gradient a)
            (candle_q_dim_jet_gradient a)))
        (candle_q_dim_interval_matrix_scale_normalized d_interval
          (candle_q_dim_jet_hessian a)))`;;

let candle_q_dim_jet_matan_def = new_definition
 `candle_q_dim_jet_matan a =
    candle_q_dim_jet_matan_with
      (candle_q_interval_matan_series (candle_q_dim_jet_f a))
      (candle_q_interval_dmatan_series (candle_q_dim_jet_f a))
      (candle_q_interval_ddmatan_series (candle_q_dim_jet_f a)) a`;;

let candle_q_dim_jet_matan_domain_def = new_definition
 `candle_q_dim_jet_matan_domain a <=>
    candle_q_interval_matan_series_domain (candle_q_dim_jet_f a)`;;

let candle_cv_q_dim_jet_matan_with_def = new_definition
 `candle_cv_q_dim_jet_matan_with value_interval d_interval dd_interval a =
    candle_cv_q_dim_jet_make value_interval
      (candle_cv_q_dim_interval_list_scale d_interval
        (candle_cv_q_dim_jet_gradient a))
      (candle_cv_q_dim_interval_matrix_add
        (candle_cv_q_dim_interval_matrix_scale dd_interval
          (candle_cv_q_dim_interval_outer
            (candle_cv_q_dim_jet_gradient a)
            (candle_cv_q_dim_jet_gradient a)))
        (candle_cv_q_dim_interval_matrix_scale d_interval
          (candle_cv_q_dim_jet_hessian a)))`;;

let candle_cv_q_dim_jet_matan_def = new_definition
 `candle_cv_q_dim_jet_matan a =
    candle_cv_q_dim_jet_matan_with
      (candle_cv_q_interval_matan_series (candle_cv_q_dim_jet_f a))
      (candle_cv_q_interval_dmatan_series (candle_cv_q_dim_jet_f a))
      (candle_cv_q_interval_ddmatan_series (candle_cv_q_dim_jet_f a)) a`;;

let candle_cv_q_dim_jet_matan_domain_def = new_definition
 `candle_cv_q_dim_jet_matan_domain a =
    candle_cv_q_interval_matan_series_domain
      (candle_cv_q_dim_jet_f a)`;;

let candle_cv_q_dim_jet_matan_compute_eqs =
  union candle_cv_q_dim_jet_compute_eqs
   (union candle_cv_q_matan_series_compute_eqs
     (map SPEC_ALL
       [candle_cv_q_dim_jet_matan_with_def;
        candle_cv_q_dim_jet_matan_def;
        candle_cv_q_dim_jet_matan_domain_def]));;

let candle_cv_q_dim_jet_matan_with_correct = prove
 (`!value_interval d_interval dd_interval a.
     candle_cv_q_dim_jet_matan_with
       (candle_cv_q_interval value_interval)
       (candle_cv_q_interval d_interval)
       (candle_cv_q_interval dd_interval)
       (candle_cv_q_dim_jet_encode a) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_jet_matan_with
         value_interval d_interval dd_interval a)`,
  REWRITE_TAC[candle_cv_q_dim_jet_matan_with_def;
              candle_q_dim_jet_matan_with_def;
              candle_cv_q_dim_jet_gradient_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_dim_interval_list_scale_correct;
              candle_cv_q_dim_interval_outer_correct;
              candle_cv_q_dim_interval_matrix_scale_correct;
              candle_cv_q_dim_interval_matrix_add_correct;
              candle_cv_q_dim_jet_make_correct]);;

let candle_cv_q_dim_jet_matan_correct = prove
 (`!a.
     candle_cv_q_dim_jet_matan (candle_cv_q_dim_jet_encode a) =
     candle_cv_q_dim_jet_encode (candle_q_dim_jet_matan a)`,
  REWRITE_TAC[candle_cv_q_dim_jet_matan_def;
              candle_q_dim_jet_matan_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_interval_matan_series_correct;
              candle_cv_q_interval_dmatan_series_correct;
              candle_cv_q_interval_ddmatan_series_correct;
              candle_cv_q_dim_jet_matan_with_correct]);;

let candle_cv_q_dim_jet_matan_domain_correct = prove
 (`!a.
     candle_cv_q_dim_jet_matan_domain (candle_cv_q_dim_jet_encode a) =
     Cexp_num (if candle_q_dim_jet_matan_domain a then 1 else 0)`,
  REWRITE_TAC[candle_cv_q_dim_jet_matan_domain_def;
              candle_q_dim_jet_matan_domain_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_interval_matan_series_domain_correct]);;

let candle_q_dim_jet_matan_shape = prove
 (`!n a.
     candle_q_dim_jet_shape n a
     ==> candle_q_dim_jet_shape n (candle_q_dim_jet_matan a)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_matan_def;
              candle_q_dim_jet_matan_with_def;
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

let candle_q_dim_jet_matan_gradient_at = prove
 (`!n a i.
     candle_q_dim_jet_shape n a /\ i < n
     ==> candle_q_dim_jet_gradient_at (candle_q_dim_jet_matan a) i =
         candle_q_interval_mul_normalized
           (candle_q_interval_dmatan_series (candle_q_dim_jet_f a))
           (candle_q_dim_jet_gradient_at a i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_matan_def;
              candle_q_dim_jet_matan_with_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_scale_lookup]);;

let candle_q_dim_jet_matan_hessian_at = prove
 (`!n a i j.
     candle_q_dim_jet_shape n a /\ i < n /\ j < n
     ==> candle_q_dim_jet_hessian_at (candle_q_dim_jet_matan a) i j =
         candle_q_interval_add_normalized
           (candle_q_interval_mul_normalized
             (candle_q_interval_ddmatan_series (candle_q_dim_jet_f a))
             (candle_q_interval_mul_normalized
               (candle_q_dim_jet_gradient_at a i)
               (candle_q_dim_jet_gradient_at a j)))
           (candle_q_interval_mul_normalized
             (candle_q_interval_dmatan_series (candle_q_dim_jet_f a))
             (candle_q_dim_jet_hessian_at a i j))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_jet_matan_def;
              candle_q_dim_jet_matan_with_def;
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

let candle_q_dim_jet_matan_value_sound = prove
 (`!n a value gradient hessian.
     candle_q_dim_jet_matan_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian
     ==> candle_q_interval_contains
           (candle_q_dim_jet_f (candle_q_dim_jet_matan a)) (matan value)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_matan_domain_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_dim_jet_matan_def;
              candle_q_dim_jet_matan_with_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  MESON_TAC[candle_q_interval_matan_series_sound]);;

let candle_q_dim_jet_matan_gradient_sound = prove
 (`!n a value gradient hessian i.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_matan_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian /\
     i < n
     ==> candle_q_interval_contains
           (candle_q_dim_jet_gradient_at (candle_q_dim_jet_matan a) i)
           (dmatan value * gradient i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_matan_domain_def;
              candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[candle_q_dim_jet_matan_gradient_at;
                candle_q_interval_dmatan_series_sound;
                candle_q_interval_mul_normalized_sound]);;

let candle_q_dim_jet_matan_hessian_sound = prove
 (`!n a value gradient hessian i j.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_matan_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian /\
     i < n /\ j < n
     ==> candle_q_interval_contains
           (candle_q_dim_jet_hessian_at (candle_q_dim_jet_matan a) i j)
           (ddmatan value * (gradient i * gradient j) +
            dmatan value * hessian i j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_matan_domain_def;
              candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[candle_q_dim_jet_matan_hessian_at;
                candle_q_interval_dmatan_series_sound;
                candle_q_interval_ddmatan_series_sound;
                candle_q_interval_mul_normalized_sound;
                candle_q_interval_add_normalized_sound]);;

let candle_q_dim_jet_matan_components_sound = prove
 (`!n a value gradient hessian.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_matan_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian
     ==> candle_q_dim_jet_contains_components n
           (candle_q_dim_jet_matan a)
           (matan value)
           (\i. dmatan value * gradient i)
           (\i j.
              ddmatan value * (gradient i * gradient j) +
              dmatan value * hessian i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[candle_q_dim_jet_matan_value_sound];
    ASM_MESON_TAC[candle_q_dim_jet_matan_gradient_sound];
    ASM_MESON_TAC[candle_q_dim_jet_matan_hessian_sound]]);;

end;;
