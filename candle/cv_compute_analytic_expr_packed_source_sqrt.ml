(* ========================================================================== *)
(* Certificate-driven unary and square-root jets for the packed source path. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The packed checker supplies outward-rounded  *)
(* value, first-derivative, and second-derivative intervals.  This ordinary  *)
(* Candle layer checks their exact semantic certificates and applies one     *)
(* source-independent chain-rule constructor.                                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_dim_jet_sqrt.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certificate_core.ml";;

module Candle_cv_analytic_expr_packed_source_sqrt = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_sqrt_certificate;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_core;;

let candle_q_dim_jet_unary_with_def = new_definition
 `candle_q_dim_jet_unary_with value d_interval dd_interval jet =
    candle_q_dim_jet_make value
      (candle_q_dim_interval_list_scale_normalized d_interval
        (candle_q_dim_jet_gradient jet))
      (candle_q_dim_interval_matrix_add_normalized
        (candle_q_dim_interval_matrix_scale_normalized dd_interval
          (candle_q_dim_interval_outer_normalized
            (candle_q_dim_jet_gradient jet)
            (candle_q_dim_jet_gradient jet)))
        (candle_q_dim_interval_matrix_scale_normalized d_interval
          (candle_q_dim_jet_hessian jet)))`;;

let candle_cv_q_dim_jet_unary_with_def = new_definition
 `candle_cv_q_dim_jet_unary_with value d_interval dd_interval jet =
    candle_cv_q_dim_jet_make value
      (candle_cv_q_dim_interval_list_scale d_interval
        (candle_cv_q_dim_jet_gradient jet))
      (candle_cv_q_dim_interval_matrix_add
        (candle_cv_q_dim_interval_matrix_scale dd_interval
          (candle_cv_q_dim_interval_outer
            (candle_cv_q_dim_jet_gradient jet)
            (candle_cv_q_dim_jet_gradient jet)))
        (candle_cv_q_dim_interval_matrix_scale d_interval
          (candle_cv_q_dim_jet_hessian jet)))`;;

let candle_cv_q_dim_jet_unary_with_correct = prove
 (`!value derivative second jet.
     candle_cv_q_dim_jet_unary_with
       (candle_cv_q_interval value)
       (candle_cv_q_interval derivative)
       (candle_cv_q_interval second)
       (candle_cv_q_dim_jet_encode jet) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_jet_unary_with value derivative second jet)`,
  REWRITE_TAC[candle_cv_q_dim_jet_unary_with_def;
              candle_q_dim_jet_unary_with_def;
              candle_cv_q_dim_jet_gradient_correct;
              candle_cv_q_dim_jet_hessian_correct;
              candle_cv_q_dim_interval_list_scale_correct;
              candle_cv_q_dim_interval_outer_correct;
              candle_cv_q_dim_interval_matrix_scale_correct;
              candle_cv_q_dim_interval_matrix_add_correct;
              candle_cv_q_dim_jet_make_correct]);;

let candle_q_dim_jet_unary_with_shape = prove
 (`!n value derivative second jet.
     candle_q_dim_jet_shape n jet
     ==> candle_q_dim_jet_shape n
           (candle_q_dim_jet_unary_with value derivative second jet)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_unary_with_def;
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

let candle_q_dim_jet_unary_with_gradient_at = prove
 (`!n value derivative second jet i.
     candle_q_dim_jet_shape n jet /\ i < n
     ==>
     candle_q_dim_jet_gradient_at
       (candle_q_dim_jet_unary_with value derivative second jet) i =
     candle_q_interval_mul_normalized derivative
       (candle_q_dim_jet_gradient_at jet i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_jet_unary_with_def;
              candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_list_scale_lookup]);;

let candle_q_dim_jet_unary_with_hessian_at = prove
 (`!n value derivative second jet i j.
     candle_q_dim_jet_shape n jet /\ i < n /\ j < n
     ==>
     candle_q_dim_jet_hessian_at
       (candle_q_dim_jet_unary_with value derivative second jet) i j =
     candle_q_interval_add_normalized
       (candle_q_interval_mul_normalized second
         (candle_q_interval_mul_normalized
           (candle_q_dim_jet_gradient_at jet i)
           (candle_q_dim_jet_gradient_at jet j)))
       (candle_q_interval_mul_normalized derivative
         (candle_q_dim_jet_hessian_at jet i j))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_shape_def;
              candle_q_dim_interval_matrix_shape_def;
              candle_q_dim_jet_unary_with_def;
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

let candle_q_dim_jet_unary_with_components_sound = prove
 (`!n output derivative second jet value gradient hessian
      output_value derivative_value second_value.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_jet_contains_components n jet value gradient hessian /\
     candle_q_interval_contains output output_value /\
     candle_q_interval_contains derivative derivative_value /\
     candle_q_interval_contains second second_value
     ==>
     candle_q_dim_jet_contains_components n
       (candle_q_dim_jet_unary_with output derivative second jet)
       output_value
       (\i. derivative_value * gradient i)
       (\i j.
          second_value * (gradient i * gradient j) +
          derivative_value * hessian i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_contains_components_def] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_jet_unary_with_def;
                candle_q_dim_jet_f_def;
                candle_q_dim_jet_make_def; FST; SND] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[candle_q_dim_jet_unary_with_gradient_at;
                  candle_q_interval_mul_normalized_sound;
                  candle_q_dim_jet_contains_components_def];
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[candle_q_dim_jet_unary_with_hessian_at;
                  candle_q_interval_mul_normalized_sound;
                  candle_q_interval_add_normalized_sound;
                  candle_q_dim_jet_contains_components_def]]);;

let candle_q_dim_jet_sqrt_certificates_def = new_definition
 `candle_q_dim_jet_sqrt_certificates input root_interval d_interval
      second_reciprocal <=>
    candle_q_interval_sqrt_certificate input root_interval /\
    candle_q_interval_inv_certificate
      (candle_q_interval_add_normalized root_interval root_interval)
      d_interval /\
    candle_q_interval_inv_certificate
      (candle_q_interval_mul_normalized
        (candle_q_interval_add_normalized root_interval root_interval)
        (candle_q_interval_add_normalized input input))
      second_reciprocal`;;

let candle_cv_q_dim_jet_sqrt_certificates_def = new_definition
 `candle_cv_q_dim_jet_sqrt_certificates
      input root_interval d_interval second_reciprocal =
    candle_cv_bool_and
      (candle_cv_q_interval_sqrt_certificate input root_interval)
      (candle_cv_bool_and
        (candle_cv_q_interval_inv_certificate
          (candle_cv_q_interval_add_normalized
            root_interval root_interval) d_interval)
        (candle_cv_q_interval_inv_certificate
          (candle_cv_q_interval_mul_normalized
            (candle_cv_q_interval_add_normalized
              root_interval root_interval)
            (candle_cv_q_interval_add_normalized input input))
          second_reciprocal))`;;

let candle_cv_q_interval_sqrt_certificate_bool_correct = prove
 (`!input output.
     candle_cv_q_interval_sqrt_certificate
       (candle_cv_q_interval input) (candle_cv_q_interval output) =
     candle_cv_bool (candle_q_interval_sqrt_certificate input output)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_sqrt_certificate_correct;
              candle_cv_bool_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 = SUC 0`]);;

let candle_cv_q_dim_jet_sqrt_certificates_correct = prove
 (`!input root derivative second_reciprocal.
     candle_cv_q_dim_jet_sqrt_certificates
       (candle_cv_q_interval input)
       (candle_cv_q_interval root)
       (candle_cv_q_interval derivative)
       (candle_cv_q_interval second_reciprocal) =
     candle_cv_bool
       (candle_q_dim_jet_sqrt_certificates
         input root derivative second_reciprocal)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_sqrt_certificates_def;
              candle_q_dim_jet_sqrt_certificates_def;
              candle_cv_q_interval_sqrt_certificate_bool_correct;
              candle_cv_q_interval_add_normalized_correct;
              candle_cv_q_interval_mul_normalized_correct;
              candle_cv_q_interval_inv_certificate_correct;
              candle_cv_bool_and_correct]);;

let candle_q_dim_jet_sqrt_certified_def = new_definition
 `candle_q_dim_jet_sqrt_certified
      root_interval d_interval second_reciprocal jet =
    candle_q_dim_jet_unary_with root_interval d_interval
      (candle_q_interval_neg second_reciprocal) jet`;;

let candle_cv_q_dim_jet_sqrt_certified_def = new_definition
 `candle_cv_q_dim_jet_sqrt_certified
      root_interval d_interval second_reciprocal jet =
    candle_cv_q_dim_jet_unary_with root_interval d_interval
      (candle_cv_q_interval_neg second_reciprocal) jet`;;

let candle_cv_q_dim_jet_sqrt_certified_correct = prove
 (`!root derivative second_reciprocal jet.
     candle_cv_q_dim_jet_sqrt_certified
       (candle_cv_q_interval root)
       (candle_cv_q_interval derivative)
       (candle_cv_q_interval second_reciprocal)
       (candle_cv_q_dim_jet_encode jet) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_jet_sqrt_certified
         root derivative second_reciprocal jet)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_sqrt_certified_def;
              candle_q_dim_jet_sqrt_certified_def;
              candle_cv_q_interval_neg_correct;
              candle_cv_q_dim_jet_unary_with_correct]);;

let candle_q_dim_jet_sqrt_certified_components_sound = prove
 (`!n root_interval d_interval second_reciprocal jet value gradient hessian.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_jet_sqrt_certificates
       (candle_q_dim_jet_f jet) root_interval d_interval
       second_reciprocal /\
     candle_q_dim_jet_contains_components n jet value gradient hessian
     ==>
     candle_q_dim_jet_contains_components n
       (candle_q_dim_jet_sqrt_certified
         root_interval d_interval second_reciprocal jet)
       (sqrt value)
       (\i. inv (sqrt value + sqrt value) * gradient i)
       (\i j.
          (--inv ((sqrt value + sqrt value) * (value + value))) *
            (gradient i * gradient j) +
          inv (sqrt value + sqrt value) * hessian i j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_sqrt_certificates_def] THEN
  STRIP_TAC THEN
  let input_contains = CONJUNCT1
    (REWRITE_RULE[candle_q_dim_jet_contains_components_def]
      (ASSUME
        `candle_q_dim_jet_contains_components n jet
          value gradient hessian`)) in
  let root_contains = MATCH_MP
    (ISPECL
      [`candle_q_dim_jet_f jet`;
       `root_interval:((num#num)#num)#((num#num)#num)`;
       `value:real`]
      candle_q_interval_sqrt_certificate_sound)
    (CONJ
      (ASSUME
        `candle_q_interval_sqrt_certificate
          (candle_q_dim_jet_f jet) root_interval`)
      input_contains) in
  let root_twice_contains = MATCH_MP
    (ISPECL
      [`root_interval:((num#num)#num)#((num#num)#num)`;
       `root_interval:((num#num)#num)#((num#num)#num)`;
       `sqrt value`; `sqrt value`]
      candle_q_interval_add_normalized_sound)
    (CONJ root_contains root_contains) in
  let input_twice_contains = MATCH_MP
    (ISPECL
      [`candle_q_dim_jet_f jet`; `candle_q_dim_jet_f jet`;
       `value:real`; `value:real`]
      candle_q_interval_add_normalized_sound)
    (CONJ input_contains input_contains) in
  let derivative_contains = MATCH_MP
    (ISPECL
      [`candle_q_interval_add_normalized root_interval root_interval`;
       `d_interval:((num#num)#num)#((num#num)#num)`;
       `sqrt value + sqrt value`]
      candle_q_interval_inv_certificate_sound)
    (CONJ
      (ASSUME
        `candle_q_interval_inv_certificate
          (candle_q_interval_add_normalized root_interval root_interval)
          d_interval`)
      root_twice_contains) in
  let denominator_contains = MATCH_MP
    (ISPECL
      [`candle_q_interval_add_normalized root_interval root_interval`;
       `candle_q_interval_add_normalized
          (candle_q_dim_jet_f jet) (candle_q_dim_jet_f jet)`;
       `sqrt value + sqrt value`; `value + value`]
      candle_q_interval_mul_normalized_sound)
    (CONJ root_twice_contains input_twice_contains) in
  let second_reciprocal_contains = MATCH_MP
    (ISPECL
      [`candle_q_interval_mul_normalized
          (candle_q_interval_add_normalized root_interval root_interval)
          (candle_q_interval_add_normalized
            (candle_q_dim_jet_f jet) (candle_q_dim_jet_f jet))`;
       `second_reciprocal:((num#num)#num)#((num#num)#num)`;
       `(sqrt value + sqrt value) * (value + value)`]
      candle_q_interval_inv_certificate_sound)
    (CONJ
      (ASSUME
        `candle_q_interval_inv_certificate
          (candle_q_interval_mul_normalized
            (candle_q_interval_add_normalized root_interval root_interval)
            (candle_q_interval_add_normalized
              (candle_q_dim_jet_f jet) (candle_q_dim_jet_f jet)))
          second_reciprocal`)
      denominator_contains) in
  let second_contains = MATCH_MP
    (ISPECL
      [`second_reciprocal:((num#num)#num)#((num#num)#num)`;
       `inv ((sqrt value + sqrt value) * (value + value))`]
      candle_q_interval_neg_sound)
    second_reciprocal_contains in
  let unary_th = MATCH_MP
    (ISPECL
      [`n:num`;
       `root_interval:((num#num)#num)#((num#num)#num)`;
       `d_interval:((num#num)#num)#((num#num)#num)`;
       `candle_q_interval_neg second_reciprocal`;
       `jet:((((num#num)#num)#((num#num)#num))#
             ((((num#num)#num)#((num#num)#num))list)#
             ((((num#num)#num)#((num#num)#num))list)list)`;
       `value:real`; `gradient:num->real`; `hessian:num->num->real`;
       `sqrt value`; `inv (sqrt value + sqrt value)`;
       `--inv ((sqrt value + sqrt value) * (value + value))`]
      candle_q_dim_jet_unary_with_components_sound)
    (end_itlist CONJ
      [ASSUME `candle_q_dim_jet_shape n jet`;
       ASSUME
        `candle_q_dim_jet_contains_components n jet
          value gradient hessian`;
       root_contains; derivative_contains; second_contains]) in
  let final_th = REWRITE_RULE[GSYM REAL_MUL_ASSOC] unary_th in
  REWRITE_TAC[candle_q_dim_jet_sqrt_certified_def] THEN
  ACCEPT_TAC final_th);;

let candle_cv_q_packed_source_sqrt_compute_eqs =
  candle_cv_q_packed_source_certificate_core_compute_eqs @
  map SPEC_ALL
    [candle_cv_q_dim_jet_unary_with_def;
     candle_cv_q_dim_jet_sqrt_certificates_def;
     candle_cv_q_dim_jet_sqrt_certified_def];;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_dim_jet_unary_with_correct;
     candle_q_dim_jet_unary_with_shape;
     candle_q_dim_jet_unary_with_gradient_at;
     candle_q_dim_jet_unary_with_hessian_at;
     candle_q_dim_jet_unary_with_components_sound;
     candle_cv_q_interval_sqrt_certificate_bool_correct;
     candle_cv_q_dim_jet_sqrt_certificates_correct;
     candle_cv_q_dim_jet_sqrt_certified_correct;
     candle_q_dim_jet_sqrt_certified_components_sound] then
  failwith "packed source sqrt: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_SQRT_OK DEVELOPMENT_NON_RELEASE";;

end;;
