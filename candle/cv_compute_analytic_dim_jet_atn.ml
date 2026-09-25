(* ========================================================================== *)
(* Guarded arctangent for dimension-generic reflected interval jets.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The value enclosure is supplied by the exact *)
(* alternating-series checker.  First and second derivative factors are      *)
(* computed once from the input interval and applied to the existing jet.    *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_atn_series.ml";;
needs "candle/cv_compute_exact_interval_square_core.ml";;
needs "candle/cv_compute_analytic_dim_jet_inv.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_rational_normalize;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_inv_core;;
open Candle_cv_exact_interval_square_core;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;

let candle_q_atn_one_interval_def = new_definition
 `candle_q_atn_one_interval =
    (candle_q_atn_one,candle_q_atn_one):
      ((num#num)#num)#((num#num)#num)`;;

let candle_q_dim_jet_atn_denominator_def = new_definition
 `candle_q_dim_jet_atn_denominator input =
    candle_q_interval_add_normalized candle_q_atn_one_interval
      (candle_q_interval_normalize (candle_q_interval_square input))`;;

let candle_q_dim_jet_atn_d_def = new_definition
 `candle_q_dim_jet_atn_d input =
    candle_q_interval_inv (candle_q_dim_jet_atn_denominator input)`;;

let candle_q_dim_jet_atn_dd_def = new_definition
 `candle_q_dim_jet_atn_dd input =
    candle_q_interval_neg
      (candle_q_interval_mul_normalized
        (candle_q_interval_add_normalized input input)
        (candle_q_interval_mul_normalized
          (candle_q_dim_jet_atn_d input)
          (candle_q_dim_jet_atn_d input)))`;;

let candle_q_dim_jet_atn_with_def = new_definition
 `candle_q_dim_jet_atn_with value_interval a =
    candle_q_dim_jet_make value_interval
      (candle_q_dim_interval_list_scale_normalized
        (candle_q_dim_jet_atn_d (candle_q_dim_jet_f a))
        (candle_q_dim_jet_gradient a))
      (candle_q_dim_interval_matrix_add_normalized
        (candle_q_dim_interval_matrix_scale_normalized
          (candle_q_dim_jet_atn_dd (candle_q_dim_jet_f a))
          (candle_q_dim_interval_outer_normalized
            (candle_q_dim_jet_gradient a)
            (candle_q_dim_jet_gradient a)))
        (candle_q_dim_interval_matrix_scale_normalized
          (candle_q_dim_jet_atn_d (candle_q_dim_jet_f a))
          (candle_q_dim_jet_hessian a)))`;;

let candle_q_dim_jet_atn_def = new_definition
 `candle_q_dim_jet_atn a =
    candle_q_dim_jet_atn_with
      (candle_q_interval_atn_series (candle_q_dim_jet_f a)) a`;;

let candle_q_dim_jet_atn_domain_def = new_definition
 `candle_q_dim_jet_atn_domain a <=>
    candle_q_interval_atn_series_domain (candle_q_dim_jet_f a) /\
    candle_q_interval_not_zero
      (candle_q_dim_jet_atn_denominator (candle_q_dim_jet_f a))`;;

let candle_cv_q_atn_one_interval_def = new_definition
 `candle_cv_q_atn_one_interval =
    Cexp_pair candle_cv_q_atn_one candle_cv_q_atn_one`;;

let candle_cv_q_dim_jet_atn_denominator_def = new_definition
 `candle_cv_q_dim_jet_atn_denominator input =
    candle_cv_q_interval_add_normalized candle_cv_q_atn_one_interval
      (candle_cv_q_interval_normalize (candle_cv_q_interval_square input))`;;

let candle_cv_q_dim_jet_atn_d_def = new_definition
 `candle_cv_q_dim_jet_atn_d input =
    candle_cv_q_interval_inv (candle_cv_q_dim_jet_atn_denominator input)`;;

let candle_cv_q_dim_jet_atn_dd_def = new_definition
 `candle_cv_q_dim_jet_atn_dd input =
    candle_cv_q_interval_neg
      (candle_cv_q_interval_mul_normalized
        (candle_cv_q_interval_add_normalized input input)
        (candle_cv_q_interval_mul_normalized
          (candle_cv_q_dim_jet_atn_d input)
          (candle_cv_q_dim_jet_atn_d input)))`;;

let candle_cv_q_dim_jet_atn_with_def = new_definition
 `candle_cv_q_dim_jet_atn_with value_interval a =
    candle_cv_q_dim_jet_make value_interval
      (candle_cv_q_dim_interval_list_scale
        (candle_cv_q_dim_jet_atn_d (candle_cv_q_dim_jet_f a))
        (candle_cv_q_dim_jet_gradient a))
      (candle_cv_q_dim_interval_matrix_add
        (candle_cv_q_dim_interval_matrix_scale
          (candle_cv_q_dim_jet_atn_dd (candle_cv_q_dim_jet_f a))
          (candle_cv_q_dim_interval_outer
            (candle_cv_q_dim_jet_gradient a)
            (candle_cv_q_dim_jet_gradient a)))
        (candle_cv_q_dim_interval_matrix_scale
          (candle_cv_q_dim_jet_atn_d (candle_cv_q_dim_jet_f a))
          (candle_cv_q_dim_jet_hessian a)))`;;

let candle_cv_q_dim_jet_atn_def = new_definition
 `candle_cv_q_dim_jet_atn a =
    candle_cv_q_dim_jet_atn_with
      (candle_cv_q_interval_atn_series (candle_cv_q_dim_jet_f a)) a`;;

let candle_cv_q_dim_jet_atn_domain_def = new_definition
 `candle_cv_q_dim_jet_atn_domain a =
    Cexp_if
      (candle_cv_q_interval_atn_series_domain (candle_cv_q_dim_jet_f a))
      (candle_cv_q_interval_not_zero
        (candle_cv_q_dim_jet_atn_denominator (candle_cv_q_dim_jet_f a)))
      (Cexp_num 0)`;;

let candle_cv_q_dim_jet_atn_compute_eqs =
  candle_cv_q_dim_jet_inv_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_atn_zero_compute; candle_cv_q_atn_one_compute;
    candle_cv_q_atn_neg_one_compute; candle_cv_q_atn_third_compute;
    candle_cv_q_atn_fifth_compute; candle_cv_q_atn_seventh_compute;
    candle_cv_q_atn_ninth_compute; candle_cv_q_atn_eleventh_compute;
    candle_cv_q_atn_thirteenth_compute;
    candle_cv_q_atn_pos_lower_compute; candle_cv_q_atn_pos_upper_compute;
    candle_cv_q_atn_lower_def; candle_cv_q_atn_upper_def;
    candle_cv_q_interval_atn_series_def;
    candle_cv_q_interval_atn_series_domain_def;
    candle_cv_q_atn_one_interval_def;
    candle_cv_q_dim_jet_atn_denominator_def;
    candle_cv_q_dim_jet_atn_d_def;
    candle_cv_q_dim_jet_atn_dd_def;
    candle_cv_q_dim_jet_atn_with_def;
    candle_cv_q_dim_jet_atn_def;
    candle_cv_q_dim_jet_atn_domain_def];;

let candle_cv_q_atn_one_interval_correct = prove
 (`candle_cv_q_atn_one_interval =
   candle_cv_q_interval candle_q_atn_one_interval`,
  REWRITE_TAC[candle_cv_q_atn_one_interval_def;
              candle_q_atn_one_interval_def;
              candle_cv_q_atn_one_def;
              candle_cv_q_interval_def; FST; SND]);;

let candle_cv_q_dim_jet_atn_denominator_correct = prove
 (`!input.
     candle_cv_q_dim_jet_atn_denominator (candle_cv_q_interval input) =
     candle_cv_q_interval (candle_q_dim_jet_atn_denominator input)`,
  REWRITE_TAC[candle_cv_q_dim_jet_atn_denominator_def;
              candle_q_dim_jet_atn_denominator_def;
              candle_cv_q_atn_one_interval_correct;
              candle_cv_q_interval_square_correct;
              candle_cv_q_interval_normalize_correct;
              candle_cv_q_interval_add_normalized_correct]);;

let candle_cv_q_dim_jet_atn_d_correct = prove
 (`!input.
     candle_cv_q_dim_jet_atn_d (candle_cv_q_interval input) =
     candle_cv_q_interval (candle_q_dim_jet_atn_d input)`,
  REWRITE_TAC[candle_cv_q_dim_jet_atn_d_def;
              candle_q_dim_jet_atn_d_def;
              candle_cv_q_dim_jet_atn_denominator_correct;
              candle_cv_q_interval_inv_correct]);;

let candle_cv_q_dim_jet_atn_dd_correct = prove
 (`!input.
     candle_cv_q_dim_jet_atn_dd (candle_cv_q_interval input) =
     candle_cv_q_interval (candle_q_dim_jet_atn_dd input)`,
  REWRITE_TAC[candle_cv_q_dim_jet_atn_dd_def;
              candle_q_dim_jet_atn_dd_def;
              candle_cv_q_interval_add_normalized_correct;
              candle_cv_q_dim_jet_atn_d_correct;
              candle_cv_q_interval_mul_normalized_correct;
              candle_cv_q_interval_neg_correct]);;

let candle_cv_q_dim_jet_atn_with_correct = prove
 (`!value_interval a.
     candle_cv_q_dim_jet_atn_with
       (candle_cv_q_interval value_interval)
       (candle_cv_q_dim_jet_encode a) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_jet_atn_with value_interval a)`,
  REWRITE_TAC[candle_cv_q_dim_jet_atn_with_def;
              candle_q_dim_jet_atn_with_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_dim_jet_gradient_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_dim_jet_atn_d_correct;
              candle_cv_q_dim_jet_atn_dd_correct;
              candle_cv_q_dim_interval_list_scale_correct;
              candle_cv_q_dim_interval_outer_correct;
              candle_cv_q_dim_interval_matrix_scale_correct;
              candle_cv_q_dim_interval_matrix_add_correct;
              candle_cv_q_dim_jet_make_correct]);;

let candle_cv_q_dim_jet_atn_correct = prove
 (`!a.
     candle_cv_q_dim_jet_atn (candle_cv_q_dim_jet_encode a) =
     candle_cv_q_dim_jet_encode (candle_q_dim_jet_atn a)`,
  REWRITE_TAC[candle_cv_q_dim_jet_atn_def;
              candle_q_dim_jet_atn_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_interval_atn_series_correct;
              candle_cv_q_dim_jet_atn_with_correct]);;

let candle_cv_q_dim_jet_atn_if_one = prove
 (`!p q. Cexp_if (Cexp_num 1) p q = p`,
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; cexp_if_def]);;

let candle_cv_q_dim_jet_atn_domain_correct = prove
 (`!a.
     candle_cv_q_dim_jet_atn_domain (candle_cv_q_dim_jet_encode a) =
     Cexp_num (if candle_q_dim_jet_atn_domain a then 1 else 0)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_atn_domain_def;
              candle_q_dim_jet_atn_domain_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_interval_atn_series_domain_correct;
              candle_cv_q_dim_jet_atn_denominator_correct;
              candle_cv_q_interval_not_zero_correct] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]) THEN
  REWRITE_TAC[candle_cv_q_dim_jet_atn_if_one]);;

let candle_q_dim_jet_atn_shape = prove
 (`!n a.
     candle_q_dim_jet_shape n a
     ==> candle_q_dim_jet_shape n (candle_q_dim_jet_atn a)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_atn_def;
              candle_q_dim_jet_atn_with_def;
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

let candle_q_dim_jet_atn_gradient_at = prove
 (`!n a i.
     candle_q_dim_jet_shape n a /\ i < n
     ==> candle_q_dim_jet_gradient_at (candle_q_dim_jet_atn a) i =
         candle_q_interval_mul_normalized
           (candle_q_dim_jet_atn_d (candle_q_dim_jet_f a))
           (candle_q_dim_jet_gradient_at a i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_atn_def;
              candle_q_dim_jet_atn_with_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_scale_lookup]);;

let candle_q_dim_jet_atn_hessian_at = prove
 (`!n a i j.
     candle_q_dim_jet_shape n a /\ i < n /\ j < n
     ==> candle_q_dim_jet_hessian_at (candle_q_dim_jet_atn a) i j =
         candle_q_interval_add_normalized
           (candle_q_interval_mul_normalized
             (candle_q_dim_jet_atn_dd (candle_q_dim_jet_f a))
             (candle_q_interval_mul_normalized
               (candle_q_dim_jet_gradient_at a i)
               (candle_q_dim_jet_gradient_at a j)))
           (candle_q_interval_mul_normalized
             (candle_q_dim_jet_atn_d (candle_q_dim_jet_f a))
             (candle_q_dim_jet_hessian_at a i j))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_jet_atn_def;
              candle_q_dim_jet_atn_with_def;
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

let candle_q_atn_one_interval_sound = prove
 (`candle_q_interval_contains candle_q_atn_one_interval (&1)`,
  REWRITE_TAC[candle_q_atn_one_interval_def;
              candle_q_interval_contains_def; FST; SND;
              candle_q_atn_one_real; REAL_LE_REFL]);;

let candle_q_dim_jet_atn_square_sound = prove
 (`!input x.
     candle_q_interval_contains input x
     ==> candle_q_interval_contains
           (candle_q_interval_normalize (candle_q_interval_square input))
           (x * x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_normalize_contains] THEN
  MATCH_ACCEPT_TAC candle_q_interval_square_sound);;

let candle_q_dim_jet_atn_denominator_sound = prove
 (`!input x.
     candle_q_interval_contains input x
     ==> candle_q_interval_contains
           (candle_q_dim_jet_atn_denominator input) (&1 + x * x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_atn_denominator_def] THEN
  MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
  ASM_MESON_TAC[candle_q_atn_one_interval_sound;
                candle_q_dim_jet_atn_square_sound]);;

let candle_q_dim_jet_atn_d_sound = prove
 (`!input x.
     candle_q_interval_not_zero (candle_q_dim_jet_atn_denominator input) /\
     candle_q_interval_contains input x
     ==> candle_q_interval_contains (candle_q_dim_jet_atn_d input)
           (inv (&1 + x * x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_atn_d_def] THEN
  STRIP_TAC THEN MATCH_MP_TAC candle_q_interval_inv_sound THEN
  ASM_MESON_TAC[candle_q_dim_jet_atn_denominator_sound]);;

let candle_q_dim_jet_atn_dd_sound = prove
 (`!input x.
     candle_q_interval_not_zero (candle_q_dim_jet_atn_denominator input) /\
     candle_q_interval_contains input x
     ==> candle_q_interval_contains (candle_q_dim_jet_atn_dd input)
           (--((x + x) *
                (inv (&1 + x * x) * inv (&1 + x * x))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_atn_dd_def] THEN
  STRIP_TAC THEN MATCH_MP_TAC candle_q_interval_neg_sound THEN
  MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_q_interval_add_normalized_sound THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_interval_mul_normalized_sound THEN
    CONJ_TAC THEN MATCH_MP_TAC candle_q_dim_jet_atn_d_sound THEN
    ASM_REWRITE_TAC[]]);;

let candle_q_dim_jet_atn_value_sound = prove
 (`!n a value gradient hessian.
     candle_q_dim_jet_atn_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian
     ==> candle_q_interval_contains
           (candle_q_dim_jet_f (candle_q_dim_jet_atn a)) (atn value)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_atn_domain_def;
              candle_q_dim_jet_contains_components_def;
              candle_q_dim_jet_atn_def;
              candle_q_dim_jet_atn_with_def;
              candle_q_dim_jet_f_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  MESON_TAC[candle_q_interval_atn_series_sound]);;

let candle_q_dim_jet_atn_gradient_sound = prove
 (`!n a value gradient hessian i.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_atn_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian /\
     i < n
     ==> candle_q_interval_contains
           (candle_q_dim_jet_gradient_at (candle_q_dim_jet_atn a) i)
           (inv (&1 + value * value) * gradient i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_atn_domain_def;
              candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[candle_q_dim_jet_atn_gradient_at;
                candle_q_dim_jet_atn_d_sound;
                candle_q_interval_mul_normalized_sound]);;

let candle_q_dim_jet_atn_hessian_sound = prove
 (`!n a value gradient hessian i j.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_atn_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian /\
     i < n /\ j < n
     ==> candle_q_interval_contains
           (candle_q_dim_jet_hessian_at (candle_q_dim_jet_atn a) i j)
           ((--((value + value) *
                 (inv (&1 + value * value) *
                  inv (&1 + value * value)))) *
              (gradient i * gradient j) +
            inv (&1 + value * value) * hessian i j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_atn_domain_def;
              candle_q_dim_jet_contains_components_def] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[candle_q_dim_jet_atn_hessian_at;
                candle_q_dim_jet_atn_d_sound;
                candle_q_dim_jet_atn_dd_sound;
                candle_q_interval_mul_normalized_sound;
                candle_q_interval_add_normalized_sound]);;

let candle_q_dim_jet_atn_components_sound = prove
 (`!n a value gradient hessian.
     candle_q_dim_jet_shape n a /\
     candle_q_dim_jet_atn_domain a /\
     candle_q_dim_jet_contains_components n a value gradient hessian
     ==> candle_q_dim_jet_contains_components n (candle_q_dim_jet_atn a)
           (atn value)
           (\i. inv (&1 + value * value) * gradient i)
           (\i j.
              (--((value + value) *
                   (inv (&1 + value * value) *
                    inv (&1 + value * value)))) *
                (gradient i * gradient j) +
              inv (&1 + value * value) * hessian i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[candle_q_dim_jet_atn_value_sound];
    ASM_MESON_TAC[candle_q_dim_jet_atn_gradient_sound];
    ASM_MESON_TAC[candle_q_dim_jet_atn_hessian_sound]]);;
