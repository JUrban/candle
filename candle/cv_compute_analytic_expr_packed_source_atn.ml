(* ========================================================================== *)
(* Certificate-driven arctangent jets for the packed analytic source path.   *)
(*                                                                            *)
(* The fast word evaluator uses outward-rounded alternating-series/range-    *)
(* reduction results and reciprocal derivative certificates.  The ordinary  *)
(* Candle entry checks that the supplied value encloses the existing exact   *)
(* rational arctangent range and that the supplied first derivative encloses *)
(* the reciprocal of 1 + x^2.  The universal unary constructor then gives    *)
(* the complete value, gradient, and Hessian source semantics.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_dim_jet_atn.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_sqrt.ml";;

module Candle_cv_analytic_expr_packed_source_atn = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_packed_source_certificate_core;;
open Candle_cv_analytic_expr_packed_source_sqrt;;

(* The value certificate deliberately refers to the existing exact rational *)
(* range calculation.  Thus the word evaluator must refine this predicate;  *)
(* two independently sound but unrelated intervals are not conflated.       *)

let candle_q_interval_atn_certificate_def = new_definition
 `candle_q_interval_atn_certificate input output <=>
    candle_q_interval_atn_range_domain input /\
    candle_q_interval_encloses output
      (candle_q_interval_atn_range input)`;;

let candle_q_interval_atn_certificate_sound = prove
 (`!input output x.
     candle_q_interval_atn_certificate input output /\
     candle_q_interval_contains input x
     ==> candle_q_interval_contains output (atn x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_atn_certificate_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC candle_q_interval_encloses_contains THEN
  EXISTS_TAC `candle_q_interval_atn_range input` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC candle_q_interval_atn_range_sound THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_q_interval_atn_certificate_def = new_definition
 `candle_cv_q_interval_atn_certificate input output =
    candle_cv_bool_and
      (candle_cv_q_interval_atn_range_domain input)
      (candle_cv_q_interval_encloses output
        (candle_cv_q_interval_atn_range input))`;;

let candle_cv_q_interval_atn_range_domain_bool_correct = prove
 (`!input.
     candle_cv_q_interval_atn_range_domain
       (candle_cv_q_interval input) =
     candle_cv_bool (candle_q_interval_atn_range_domain input)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_atn_range_domain_correct;
              candle_cv_bool_def; ARITH_RULE `1 = SUC 0`] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_q_interval_atn_certificate_correct = prove
 (`!input output.
     candle_cv_q_interval_atn_certificate
       (candle_cv_q_interval input) (candle_cv_q_interval output) =
     candle_cv_bool (candle_q_interval_atn_certificate input output)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_atn_certificate_def;
              candle_q_interval_atn_certificate_def;
              candle_cv_q_interval_atn_range_domain_bool_correct;
              candle_cv_q_interval_atn_range_correct;
              candle_cv_q_interval_encloses_correct;
              candle_cv_bool_and_correct]);;

let candle_q_dim_jet_atn_certificates_def = new_definition
 `candle_q_dim_jet_atn_certificates input output d_interval <=>
    candle_q_interval_atn_certificate input output /\
    candle_q_interval_inv_certificate
      (candle_q_dim_jet_atn_denominator input) d_interval`;;

let candle_cv_q_dim_jet_atn_certificates_def = new_definition
 `candle_cv_q_dim_jet_atn_certificates input output d_interval =
    candle_cv_bool_and
      (candle_cv_q_interval_atn_certificate input output)
      (candle_cv_q_interval_inv_certificate
        (candle_cv_q_dim_jet_atn_denominator input) d_interval)`;;

let candle_cv_q_dim_jet_atn_certificates_correct = prove
 (`!input output d_interval.
     candle_cv_q_dim_jet_atn_certificates
       (candle_cv_q_interval input)
       (candle_cv_q_interval output)
       (candle_cv_q_interval d_interval) =
     candle_cv_bool
       (candle_q_dim_jet_atn_certificates input output d_interval)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_atn_certificates_def;
              candle_q_dim_jet_atn_certificates_def;
              candle_cv_q_interval_atn_certificate_correct;
              candle_cv_q_dim_jet_atn_denominator_correct;
              candle_cv_q_interval_inv_certificate_correct;
              candle_cv_bool_and_correct]);;

let candle_q_dim_jet_atn_second_with_def = new_definition
 `candle_q_dim_jet_atn_second_with input d_interval =
    candle_q_interval_neg
      (candle_q_interval_mul_normalized
        (candle_q_interval_add_normalized input input)
        (candle_q_interval_mul_normalized d_interval d_interval))`;;

let candle_cv_q_dim_jet_atn_second_with_def = new_definition
 `candle_cv_q_dim_jet_atn_second_with input d_interval =
    candle_cv_q_interval_neg
      (candle_cv_q_interval_mul_normalized
        (candle_cv_q_interval_add_normalized input input)
        (candle_cv_q_interval_mul_normalized d_interval d_interval))`;;

let candle_cv_q_dim_jet_atn_second_with_correct = prove
 (`!input d_interval.
     candle_cv_q_dim_jet_atn_second_with
       (candle_cv_q_interval input) (candle_cv_q_interval d_interval) =
     candle_cv_q_interval
       (candle_q_dim_jet_atn_second_with input d_interval)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_atn_second_with_def;
              candle_q_dim_jet_atn_second_with_def;
              candle_cv_q_interval_add_normalized_correct;
              candle_cv_q_interval_mul_normalized_correct;
              candle_cv_q_interval_neg_correct]);;

let candle_q_dim_jet_atn_second_with_sound = prove
 (`!input d_interval x.
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator input) d_interval /\
     candle_q_interval_contains input x
     ==> candle_q_interval_contains
           (candle_q_dim_jet_atn_second_with input d_interval)
           (--((x + x) *
                (inv (&1 + x * x) * inv (&1 + x * x))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_atn_second_with_def] THEN
  ASM_MESON_TAC[candle_q_interval_inv_certificate_sound;
                candle_q_dim_jet_atn_denominator_sound;
                candle_q_interval_add_normalized_sound;
                candle_q_interval_mul_normalized_sound;
                candle_q_interval_neg_sound]);;

let candle_q_dim_jet_atn_certified_def = new_definition
 `candle_q_dim_jet_atn_certified output d_interval jet =
    candle_q_dim_jet_unary_with output d_interval
      (candle_q_dim_jet_atn_second_with
        (candle_q_dim_jet_f jet) d_interval) jet`;;

let candle_cv_q_dim_jet_atn_certified_def = new_definition
 `candle_cv_q_dim_jet_atn_certified output d_interval jet =
    candle_cv_q_dim_jet_unary_with output d_interval
      (candle_cv_q_dim_jet_atn_second_with
        (candle_cv_q_dim_jet_f jet) d_interval) jet`;;

let candle_cv_q_dim_jet_atn_certified_correct = prove
 (`!output d_interval jet.
     candle_cv_q_dim_jet_atn_certified
       (candle_cv_q_interval output)
       (candle_cv_q_interval d_interval)
       (candle_cv_q_dim_jet_encode jet) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_jet_atn_certified output d_interval jet)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_dim_jet_atn_certified_def;
              candle_q_dim_jet_atn_certified_def;
              candle_cv_q_dim_jet_f_correct;
              candle_cv_q_dim_jet_atn_second_with_correct;
              candle_cv_q_dim_jet_unary_with_correct]);;

let candle_q_dim_jet_atn_certified_components_sound = prove
 (`!n output d_interval jet value gradient hessian.
     candle_q_dim_jet_shape n jet /\
     candle_q_dim_jet_atn_certificates
       (candle_q_dim_jet_f jet) output d_interval /\
     candle_q_dim_jet_contains_components n jet value gradient hessian
     ==>
     candle_q_dim_jet_contains_components n
       (candle_q_dim_jet_atn_certified output d_interval jet)
       (atn value)
       (\i. inv (&1 + value * value) * gradient i)
       (\i j.
          (--((value + value) *
               (inv (&1 + value * value) *
                inv (&1 + value * value)))) *
            (gradient i * gradient j) +
          inv (&1 + value * value) * hessian i j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_atn_certificates_def;
              candle_q_dim_jet_atn_certified_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `candle_q_interval_contains (candle_q_dim_jet_f jet) value`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_dim_jet_contains_components_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `candle_q_interval_contains output (atn value)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_interval_atn_certificate_sound];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `candle_q_interval_contains d_interval (inv (&1 + value * value))`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_interval_inv_certificate_sound;
                  candle_q_dim_jet_atn_denominator_sound];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `candle_q_interval_contains
       (candle_q_dim_jet_atn_second_with
         (candle_q_dim_jet_f jet) d_interval)
       (--((value + value) *
            (inv (&1 + value * value) *
             inv (&1 + value * value))))`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_dim_jet_atn_second_with_sound];
    ALL_TAC] THEN
  let unary_th = MATCH_MP
    (ISPECL
      [`n:num`;
       `output:((num#num)#num)#((num#num)#num)`;
       `d_interval:((num#num)#num)#((num#num)#num)`;
       `candle_q_dim_jet_atn_second_with
          (candle_q_dim_jet_f jet) d_interval`;
       `jet:((((num#num)#num)#((num#num)#num))#
             ((((num#num)#num)#((num#num)#num))list)#
             ((((num#num)#num)#((num#num)#num))list)list)`;
       `value:real`; `gradient:num->real`; `hessian:num->num->real`;
       `atn value`;
       `inv (&1 + value * value)`;
       `--((value + value) *
           (inv (&1 + value * value) *
            inv (&1 + value * value)))`]
      candle_q_dim_jet_unary_with_components_sound)
    (end_itlist CONJ
      [ASSUME `candle_q_dim_jet_shape n jet`;
       ASSUME
        `candle_q_dim_jet_contains_components n jet
          value gradient hessian`;
       ASSUME `candle_q_interval_contains output (atn value)`;
       ASSUME
        `candle_q_interval_contains d_interval
          (inv (&1 + value * value))`;
       ASSUME
        `candle_q_interval_contains
          (candle_q_dim_jet_atn_second_with
            (candle_q_dim_jet_f jet) d_interval)
          (--((value + value) *
               (inv (&1 + value * value) *
                inv (&1 + value * value))))`]) in
  let final_th = REWRITE_RULE[GSYM REAL_MUL_ASSOC] unary_th in
  ACCEPT_TAC final_th);;

let candle_cv_q_packed_source_atn_compute_eqs =
  union candle_cv_q_dim_jet_atn_compute_eqs
   (union candle_cv_q_packed_source_sqrt_compute_eqs
     (map SPEC_ALL
       [candle_cv_q_interval_atn_certificate_def;
        candle_cv_q_dim_jet_atn_certificates_def;
        candle_cv_q_dim_jet_atn_second_with_def;
        candle_cv_q_dim_jet_atn_certified_def]));;

if exists (fun theorem -> hyp theorem <> [])
     [candle_q_interval_atn_certificate_sound;
      candle_cv_q_interval_atn_range_domain_bool_correct;
      candle_cv_q_interval_atn_certificate_correct;
      candle_cv_q_dim_jet_atn_certificates_correct;
      candle_cv_q_dim_jet_atn_second_with_correct;
      candle_q_dim_jet_atn_second_with_sound;
      candle_cv_q_dim_jet_atn_certified_correct;
      candle_q_dim_jet_atn_certified_components_sound] then
  failwith "packed source atan: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_ATN_OK DEVELOPMENT_NON_RELEASE";;

end;;
