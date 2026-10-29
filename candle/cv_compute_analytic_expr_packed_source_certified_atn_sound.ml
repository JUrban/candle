(* ========================================================================== *)
(* Certificate-faithful arctangent Taylor results for packed source replay.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fixed-word checker squares the center     *)
(* and whole-box inputs separately, forms reciprocal derivative intervals,   *)
(* and then squares the whole-box derivative interval once more before       *)
(* constructing the second-derivative coefficient.  The ordinary semantic   *)
(* entry below retains that exact dependency structure.                      *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_item_operations_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_atn.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_certified_sqrt_sound.ml";;

module Candle_cv_analytic_expr_packed_source_certified_atn_sound = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_square_core;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_polynomial_expr_dim_check;;
open Candle_cv_whole_box_dim_taylor_sound;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_core;;
open Candle_cv_analytic_expr_packed_source_sqrt;;
open Candle_cv_analytic_expr_packed_source_atn;;
open Candle_cv_analytic_expr_packed_source_certified_sqrt_sound;;
open Candle_cv_analytic_expr_packed_source_item_invariant;;
open Candle_cv_analytic_expr_packed_source_item_operations_sound;;

(* [word_input] is the decoded fixed-word interval actually squared by the  *)
(* fast checker.  It may be wider than the semantic source interval.         *)

let candle_q_interval_square_outer_certificate_def = new_definition
 `candle_q_interval_square_outer_certificate
      source_input word_input output <=>
    candle_q_interval_encloses word_input source_input /\
    candle_q_interval_encloses output
      (candle_q_interval_normalize
        (candle_q_interval_square word_input))`;;

let candle_q_interval_square_outer_certificate_sound = prove
 (`!source_input word_input output x.
     candle_q_interval_square_outer_certificate
       source_input word_input output /\
     candle_q_interval_contains source_input x
     ==>
     candle_q_interval_contains output (x * x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_square_outer_certificate_def] THEN
  STRIP_TAC THEN
  let word_contains = MATCH_MP
    (ISPECL
      [`word_input:((num#num)#num)#((num#num)#num)`;
       `source_input:((num#num)#num)#((num#num)#num)`;
       `x:real`]
      candle_q_interval_encloses_contains)
    (CONJ
      (ASSUME `candle_q_interval_encloses word_input source_input`)
      (ASSUME `candle_q_interval_contains source_input x`)) in
  let square_contains_raw = MATCH_MP
    (ISPECL
      [`word_input:((num#num)#num)#((num#num)#num)`; `x:real`]
      candle_q_interval_square_sound)
    word_contains in
  let square_contains = EQ_MP
    (SYM
      (ISPECL
        [`candle_q_interval_square word_input`; `x * x`]
        candle_q_interval_normalize_contains))
    square_contains_raw in
  MATCH_MP_TAC candle_q_interval_encloses_contains THEN
  EXISTS_TAC
    `candle_q_interval_normalize
      (candle_q_interval_square word_input)` THEN
  ASM_REWRITE_TAC[] THEN
  ACCEPT_TAC square_contains);;


let candle_cv_q_interval_square_outer_certificate_def = new_definition
 `candle_cv_q_interval_square_outer_certificate
      source_input word_input output =
    candle_cv_bool_and
      (candle_cv_q_interval_encloses word_input source_input)
      (candle_cv_q_interval_encloses output
        (candle_cv_q_interval_normalize
          (candle_cv_q_interval_square word_input)))`;;

let candle_cv_q_interval_square_outer_certificate_correct = prove
 (`!source_input word_input output.
     candle_cv_q_interval_square_outer_certificate
       (candle_cv_q_interval source_input)
       (candle_cv_q_interval word_input)
       (candle_cv_q_interval output) =
     candle_cv_bool
       (candle_q_interval_square_outer_certificate
         source_input word_input output)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_square_outer_certificate_def;
              candle_q_interval_square_outer_certificate_def;
              candle_cv_q_interval_encloses_correct;
              candle_cv_q_interval_square_correct;
              candle_cv_q_interval_normalize_correct;
              candle_cv_bool_and_correct]);;


(* The center arctangent range is evaluated on the decoded word interval,   *)
(* while the semantic center value may inhabit a narrower source interval.  *)

let candle_q_interval_atn_outer_certificate_def = new_definition
 `candle_q_interval_atn_outer_certificate
      source_input word_input output <=>
    candle_q_interval_encloses word_input source_input /\
    candle_q_interval_atn_certificate word_input output`;;

let candle_q_interval_atn_outer_certificate_sound = prove
 (`!source_input word_input output x.
     candle_q_interval_atn_outer_certificate
       source_input word_input output /\
     candle_q_interval_contains source_input x
     ==>
     candle_q_interval_contains output (atn x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_atn_outer_certificate_def] THEN
  STRIP_TAC THEN
  let word_contains = MATCH_MP
    (ISPECL
      [`word_input:((num#num)#num)#((num#num)#num)`;
       `source_input:((num#num)#num)#((num#num)#num)`; `x:real`]
      candle_q_interval_encloses_contains)
    (CONJ
      (ASSUME `candle_q_interval_encloses word_input source_input`)
      (ASSUME `candle_q_interval_contains source_input x`)) in
  let output_contains = MATCH_MP
    (ISPECL
      [`word_input:((num#num)#num)#((num#num)#num)`;
       `output:((num#num)#num)#((num#num)#num)`; `x:real`]
      candle_q_interval_atn_certificate_sound)
    (CONJ
      (ASSUME `candle_q_interval_atn_certificate word_input output`)
      word_contains) in
  ACCEPT_TAC output_contains);;


let candle_cv_q_interval_atn_outer_certificate_def = new_definition
 `candle_cv_q_interval_atn_outer_certificate
      source_input word_input output =
    candle_cv_bool_and
      (candle_cv_q_interval_encloses word_input source_input)
      (candle_cv_q_interval_atn_certificate word_input output)`;;

let candle_cv_q_interval_atn_outer_certificate_correct = prove
 (`!source_input word_input output.
     candle_cv_q_interval_atn_outer_certificate
       (candle_cv_q_interval source_input)
       (candle_cv_q_interval word_input)
       (candle_cv_q_interval output) =
     candle_cv_bool
       (candle_q_interval_atn_outer_certificate
         source_input word_input output)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_atn_outer_certificate_def;
              candle_q_interval_atn_outer_certificate_def;
              candle_cv_q_interval_encloses_correct;
              candle_cv_q_interval_atn_certificate_correct;
              candle_cv_bool_and_correct]);;


let candle_q_dim_jet_atn_denominator_with_square_def = new_definition
 `candle_q_dim_jet_atn_denominator_with_square square =
    candle_q_interval_add_normalized candle_q_atn_one_interval square`;;

let candle_q_dim_jet_atn_second_with_square_def = new_definition
 `candle_q_dim_jet_atn_second_with_square input derivative_square =
    candle_q_interval_neg
      (candle_q_interval_mul_normalized
        (candle_q_interval_add_normalized input input)
        derivative_square)`;;

let candle_q_dim_jet_atn_derivative_outer_certificate_sound = prove
 (`!source_input word_input square derivative x.
     candle_q_interval_square_outer_certificate
       source_input word_input square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square square) derivative /\
     candle_q_interval_contains source_input x
     ==>
     candle_q_interval_contains derivative (inv (&1 + x * x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let square_contains = MATCH_MP
    (ISPECL
      [`source_input:((num#num)#num)#((num#num)#num)`;
       `word_input:((num#num)#num)#((num#num)#num)`;
       `square:((num#num)#num)#((num#num)#num)`; `x:real`]
      candle_q_interval_square_outer_certificate_sound)
    (CONJ
      (ASSUME
        `candle_q_interval_square_outer_certificate
          source_input word_input square`)
      (ASSUME `candle_q_interval_contains source_input x`)) in
  let denominator_contains = MATCH_MP
    (ISPECL
      [`candle_q_atn_one_interval`;
       `square:((num#num)#num)#((num#num)#num)`;
       `&1`; `x * x`]
      candle_q_interval_add_normalized_sound)
    (CONJ candle_q_atn_one_interval_sound square_contains) in
  MATCH_MP_TAC candle_q_interval_inv_certificate_sound THEN
  EXISTS_TAC
    `candle_q_dim_jet_atn_denominator_with_square square` THEN
  ASM_REWRITE_TAC[candle_q_dim_jet_atn_denominator_with_square_def] THEN
  ACCEPT_TAC denominator_contains);;


let candle_q_dim_jet_atn_second_with_square_sound = prove
 (`!source_input word_input square d_interval derivative_square x.
     candle_q_interval_square_outer_certificate
       source_input word_input square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square square) d_interval /\
     candle_q_interval_square_outer_certificate
       d_interval d_interval derivative_square /\
     candle_q_interval_contains source_input x
     ==>
     candle_q_interval_contains
       (candle_q_dim_jet_atn_second_with_square
         word_input derivative_square)
       (--((x + x) *
            (inv (&1 + x * x) * inv (&1 + x * x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let derivative_contains = MATCH_MP
    (ISPECL
      [`source_input:((num#num)#num)#((num#num)#num)`;
       `word_input:((num#num)#num)#((num#num)#num)`;
       `square:((num#num)#num)#((num#num)#num)`;
       `d_interval:((num#num)#num)#((num#num)#num)`; `x:real`]
      candle_q_dim_jet_atn_derivative_outer_certificate_sound)
    (end_itlist CONJ
      [ASSUME
        `candle_q_interval_square_outer_certificate
          source_input word_input square`;
       ASSUME
        `candle_q_interval_inv_certificate
          (candle_q_dim_jet_atn_denominator_with_square square) d_interval`;
       ASSUME `candle_q_interval_contains source_input x`]) in
  let derivative_square_contains = MATCH_MP
    (ISPECL
      [`d_interval:((num#num)#num)#((num#num)#num)`;
       `d_interval:((num#num)#num)#((num#num)#num)`;
       `derivative_square:((num#num)#num)#((num#num)#num)`;
       `inv (&1 + x * x)`]
      candle_q_interval_square_outer_certificate_sound)
    (CONJ
      (ASSUME
        `candle_q_interval_square_outer_certificate
          d_interval d_interval derivative_square`)
      derivative_contains) in
  let word_contains = MATCH_MP
    (ISPECL
      [`word_input:((num#num)#num)#((num#num)#num)`;
       `source_input:((num#num)#num)#((num#num)#num)`; `x:real`]
      candle_q_interval_encloses_contains)
    (CONJ
      (CONJUNCT1
        (REWRITE_RULE[candle_q_interval_square_outer_certificate_def]
          (ASSUME
            `candle_q_interval_square_outer_certificate
              source_input word_input square`)))
      (ASSUME `candle_q_interval_contains source_input x`)) in
  let twice_contains = MATCH_MP
    (ISPECL
      [`word_input:((num#num)#num)#((num#num)#num)`;
       `word_input:((num#num)#num)#((num#num)#num)`; `x:real`; `x:real`]
      candle_q_interval_add_normalized_sound)
    (CONJ word_contains word_contains) in
  let magnitude_contains = MATCH_MP
    (ISPECL
      [`candle_q_interval_add_normalized word_input word_input`;
       `derivative_square:((num#num)#num)#((num#num)#num)`;
       `x + x`; `inv (&1 + x * x) * inv (&1 + x * x)`]
      candle_q_interval_mul_normalized_sound)
    (CONJ twice_contains derivative_square_contains) in
  REWRITE_TAC[candle_q_dim_jet_atn_second_with_square_def] THEN
  MATCH_MP_TAC candle_q_interval_neg_sound THEN
  ACCEPT_TAC magnitude_contains);;


let candle_q_atn_universal_interval_def = new_definition
 `candle_q_atn_universal_interval =
    (candle_q_neg (SND candle_q_atn_pi_half_interval),
     SND candle_q_atn_pi_half_interval)`;;

let candle_q_atn_universal_interval_sound = prove
 (`!x. candle_q_interval_contains candle_q_atn_universal_interval (atn x)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_q_atn_universal_interval_def;
              candle_q_interval_contains_def; FST; SND;
              candle_q_real_neg] THEN
  MP_TAC candle_q_atn_pi_half_interval_sound THEN
  REWRITE_TAC[candle_q_interval_contains_def] THEN
  MP_TAC (SPEC `x:real` ATN_BOUNDS) THEN
  REAL_ARITH_TAC);;


let candle_q_dim_jet_atn_faithful_def = new_definition
 `candle_q_dim_jet_atn_faithful
      output d_interval second_input derivative_square jet =
    candle_q_dim_jet_unary_with output d_interval
      (candle_q_dim_jet_atn_second_with_square
        second_input derivative_square) jet`;;

let candle_q_dim_jet_atn_faithful_shape = prove
 (`!n output d_interval second_input derivative_square jet.
     candle_q_dim_jet_shape n jet
     ==>
     candle_q_dim_jet_shape n
       (candle_q_dim_jet_atn_faithful
         output d_interval second_input derivative_square jet)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_atn_faithful_def] THEN
  MATCH_ACCEPT_TAC candle_q_dim_jet_unary_with_shape);;


let candle_q_dim_jet_atn_split_faithful_components_sound = prove
 (`!n center_input box_input center_result center_square center_derivative
      box_square box_derivative box_derivative_square center_jet box_jet
      value gradient hessian.
     candle_q_dim_jet_shape n center_jet /\
     candle_q_dim_jet_contains_components
       n center_jet value gradient hessian /\
     candle_q_dim_jet_contains_components
       n box_jet value gradient hessian /\
     candle_q_interval_atn_outer_certificate
       (candle_q_dim_jet_f center_jet) center_input center_result /\
     candle_q_interval_square_outer_certificate
       (candle_q_dim_jet_f center_jet) center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square center_square)
       center_derivative /\
     candle_q_interval_square_outer_certificate
       (candle_q_dim_jet_f box_jet) box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square
     ==>
     candle_q_dim_jet_contains_components n
       (candle_q_dim_jet_atn_faithful center_result center_derivative
         box_input box_derivative_square center_jet)
       (atn value)
       (\i. inv (&1 + value * value) * gradient i)
       (\i j.
          (--((value + value) *
               (inv (&1 + value * value) *
                inv (&1 + value * value)))) *
            (gradient i * gradient j) +
          inv (&1 + value * value) * hessian i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let center_input_contains = CONJUNCT1
    (REWRITE_RULE[candle_q_dim_jet_contains_components_def]
      (ASSUME
        `candle_q_dim_jet_contains_components
          n center_jet value gradient hessian`)) in
  let box_input_contains = CONJUNCT1
    (REWRITE_RULE[candle_q_dim_jet_contains_components_def]
      (ASSUME
        `candle_q_dim_jet_contains_components
          n box_jet value gradient hessian`)) in
  let output_contains = MATCH_MP
    (ISPECL
      [`candle_q_dim_jet_f center_jet`;
       `center_input:((num#num)#num)#((num#num)#num)`;
       `center_result:((num#num)#num)#((num#num)#num)`; `value:real`]
      candle_q_interval_atn_outer_certificate_sound)
    (CONJ
      (ASSUME
        `candle_q_interval_atn_outer_certificate
          (candle_q_dim_jet_f center_jet) center_input center_result`)
      center_input_contains) in
  let center_derivative_contains = MATCH_MP
    (ISPECL
      [`candle_q_dim_jet_f center_jet`;
       `center_input:((num#num)#num)#((num#num)#num)`;
       `center_square:((num#num)#num)#((num#num)#num)`;
       `center_derivative:((num#num)#num)#((num#num)#num)`; `value:real`]
      candle_q_dim_jet_atn_derivative_outer_certificate_sound)
    (end_itlist CONJ
      [ASSUME
        `candle_q_interval_square_outer_certificate
          (candle_q_dim_jet_f center_jet) center_input center_square`;
       ASSUME
        `candle_q_interval_inv_certificate
          (candle_q_dim_jet_atn_denominator_with_square center_square)
          center_derivative`;
       center_input_contains]) in
  let second_contains = MATCH_MP
    (ISPECL
      [`candle_q_dim_jet_f box_jet`;
       `box_input:((num#num)#num)#((num#num)#num)`;
       `box_square:((num#num)#num)#((num#num)#num)`;
       `box_derivative:((num#num)#num)#((num#num)#num)`;
       `box_derivative_square:((num#num)#num)#((num#num)#num)`;
       `value:real`]
      candle_q_dim_jet_atn_second_with_square_sound)
    (end_itlist CONJ
      [ASSUME
        `candle_q_interval_square_outer_certificate
          (candle_q_dim_jet_f box_jet) box_input box_square`;
       ASSUME
        `candle_q_interval_inv_certificate
          (candle_q_dim_jet_atn_denominator_with_square box_square)
          box_derivative`;
       ASSUME
        `candle_q_interval_square_outer_certificate
          box_derivative box_derivative box_derivative_square`;
       box_input_contains]) in
  let unary_th = MATCH_MP
    (ISPECL
      [`n:num`; `center_result:((num#num)#num)#((num#num)#num)`;
       `center_derivative:((num#num)#num)#((num#num)#num)`;
       `candle_q_dim_jet_atn_second_with_square
          box_input box_derivative_square`;
       `center_jet:((((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list)#
          ((((num#num)#num)#((num#num)#num))list)list)`;
       `value:real`; `gradient:num->real`; `hessian:num->num->real`;
       `atn value`; `inv (&1 + value * value)`;
       `--((value + value) *
          (inv (&1 + value * value) * inv (&1 + value * value)))`]
      candle_q_dim_jet_unary_with_components_sound)
    (end_itlist CONJ
      [ASSUME `candle_q_dim_jet_shape n center_jet`;
       ASSUME
        `candle_q_dim_jet_contains_components
          n center_jet value gradient hessian`;
       output_contains; center_derivative_contains; second_contains]) in
  REWRITE_TAC[candle_q_dim_jet_atn_faithful_def] THEN
  ACCEPT_TAC (REWRITE_RULE[GSYM REAL_MUL_ASSOC] unary_th));;


let candle_q_dim_jet_atn_box_faithful_components_sound = prove
 (`!n box_input box_square box_derivative box_derivative_square box_jet
      value gradient hessian.
     candle_q_dim_jet_shape n box_jet /\
     candle_q_dim_jet_contains_components
       n box_jet value gradient hessian /\
     candle_q_interval_square_outer_certificate
       (candle_q_dim_jet_f box_jet) box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square
     ==>
     candle_q_dim_jet_contains_components n
       (candle_q_dim_jet_atn_faithful candle_q_atn_universal_interval
         box_derivative box_input box_derivative_square box_jet)
       (atn value)
       (\i. inv (&1 + value * value) * gradient i)
       (\i j.
          (--((value + value) *
               (inv (&1 + value * value) *
                inv (&1 + value * value)))) *
            (gradient i * gradient j) +
          inv (&1 + value * value) * hessian i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let input_contains = CONJUNCT1
    (REWRITE_RULE[candle_q_dim_jet_contains_components_def]
      (ASSUME
        `candle_q_dim_jet_contains_components
          n box_jet value gradient hessian`)) in
  let derivative_contains = MATCH_MP
    (ISPECL
      [`candle_q_dim_jet_f box_jet`;
       `box_input:((num#num)#num)#((num#num)#num)`;
       `box_square:((num#num)#num)#((num#num)#num)`;
       `box_derivative:((num#num)#num)#((num#num)#num)`; `value:real`]
      candle_q_dim_jet_atn_derivative_outer_certificate_sound)
    (end_itlist CONJ
      [ASSUME
        `candle_q_interval_square_outer_certificate
          (candle_q_dim_jet_f box_jet) box_input box_square`;
       ASSUME
        `candle_q_interval_inv_certificate
          (candle_q_dim_jet_atn_denominator_with_square box_square)
          box_derivative`;
       input_contains]) in
  let second_contains = MATCH_MP
    (ISPECL
      [`candle_q_dim_jet_f box_jet`;
       `box_input:((num#num)#num)#((num#num)#num)`;
       `box_square:((num#num)#num)#((num#num)#num)`;
       `box_derivative:((num#num)#num)#((num#num)#num)`;
       `box_derivative_square:((num#num)#num)#((num#num)#num)`;
       `value:real`]
      candle_q_dim_jet_atn_second_with_square_sound)
    (end_itlist CONJ
      [ASSUME
        `candle_q_interval_square_outer_certificate
          (candle_q_dim_jet_f box_jet) box_input box_square`;
       ASSUME
        `candle_q_interval_inv_certificate
          (candle_q_dim_jet_atn_denominator_with_square box_square)
          box_derivative`;
       ASSUME
        `candle_q_interval_square_outer_certificate
          box_derivative box_derivative box_derivative_square`;
       input_contains]) in
  let unary_th = MATCH_MP
    (ISPECL
      [`n:num`; `candle_q_atn_universal_interval`;
       `box_derivative:((num#num)#num)#((num#num)#num)`;
       `candle_q_dim_jet_atn_second_with_square
          box_input box_derivative_square`;
       `box_jet:((((num#num)#num)#((num#num)#num))#
          ((((num#num)#num)#((num#num)#num))list)#
          ((((num#num)#num)#((num#num)#num))list)list)`;
       `value:real`; `gradient:num->real`; `hessian:num->num->real`;
       `atn value`; `inv (&1 + value * value)`;
       `--((value + value) *
          (inv (&1 + value * value) * inv (&1 + value * value)))`]
      candle_q_dim_jet_unary_with_components_sound)
    (end_itlist CONJ
      [ASSUME `candle_q_dim_jet_shape n box_jet`;
       ASSUME
        `candle_q_dim_jet_contains_components
          n box_jet value gradient hessian`;
       SPEC `value:real` candle_q_atn_universal_interval_sound;
       derivative_contains; second_contains]) in
  REWRITE_TAC[candle_q_dim_jet_atn_faithful_def] THEN
  ACCEPT_TAC (REWRITE_RULE[GSYM REAL_MUL_ASSOC] unary_th));;



let candle_q_dim_taylor_model_result_atn_faithful_def = new_definition
 `candle_q_dim_taylor_model_result_atn_faithful radii box_input
      center_result center_derivative box_derivative box_derivative_square
      result =
    candle_q_dim_taylor_model_result_complete radii
      (candle_q_dim_taylor_model_result_domain result)
      (candle_q_dim_jet_atn_faithful center_result center_derivative
        box_input box_derivative_square
        (candle_q_dim_taylor_model_result_center result))
      (candle_q_dim_jet_hessian
        (candle_q_dim_jet_atn_faithful candle_q_atn_universal_interval
          box_derivative box_input box_derivative_square
          (candle_q_dim_taylor_model_proxy result)))`;;

let candle_q_dim_taylor_model_result_atn_faithful_analytic_invariant = prove
 (`!center_e box_e boxes result center_input box_input center_result
      center_square center_derivative box_square box_derivative
      box_derivative_square (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes result center_e box_e /\
     candle_q_interval_atn_outer_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center result))
       center_input center_result /\
     candle_q_interval_square_outer_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center result))
       center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square center_square)
       center_derivative /\
     candle_q_interval_square_outer_certificate
       (candle_q_dim_jet_f (candle_q_dim_taylor_model_proxy result))
       box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_q_dim_taylor_model_result_atn_faithful
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         box_input center_result center_derivative box_derivative
         box_derivative_square result)
       (Candle_analytic_atn center_e) (Candle_analytic_atn box_e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "erasure_equal")
        (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 (LABEL_TAC "input_invariant")
              (CONJUNCTS_THEN2 (LABEL_TAC "center_atn_certificate")
                (CONJUNCTS_THEN2 (LABEL_TAC "center_square_certificate")
                  (CONJUNCTS_THEN2 (LABEL_TAC "center_derivative_certificate")
                    (CONJUNCTS_THEN2 (LABEL_TAC "box_square_certificate")
                      (CONJUNCTS_THEN2 (LABEL_TAC "box_derivative_certificate")
                        (LABEL_TAC "box_derivative_square_certificate"))))))))))) THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_atn_faithful_def] THEN
  MATCH_MP_TAC candle_q_dim_taylor_model_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    USE_THEN "input_invariant" MP_TAC THEN
    REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "center_regular")
        (CONJUNCTS_THEN2 (LABEL_TAC "box_regular")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_shape")
            (CONJUNCTS_THEN2 (LABEL_TAC "center_contains")
              (CONJUNCTS_THEN2 (LABEL_TAC "proxy_shape")
                (LABEL_TAC "box_contains_all")))))) THEN
    let center_point = `candle_q_box_center_vector boxes:real^N` in
    SUBGOAL_THEN
      `(candle_q_box_center_vector boxes : real^N) IN
        interval
          [candle_q_box_lower_vector boxes,
           candle_q_box_upper_vector boxes]`
      (LABEL_TAC "center_point_in_box") THENL
     [MATCH_MP_TAC candle_q_box_center_vector_in_interval THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    let center_point_in_box =
      ASSUME
        `(candle_q_box_center_vector boxes : real^N) IN
          interval
            [candle_q_box_lower_vector boxes,
             candle_q_box_upper_vector boxes]` in
    USE_THEN "box_contains_all" (fun th ->
      LABEL_TAC "proxy_contains_center"
        (MP (SPEC center_point th) center_point_in_box)) THEN
    USE_THEN "proxy_contains_center" (fun proxy_contains_box_e ->
      let proxy_contains_erased_box =
        ONCE_REWRITE_RULE
          [GSYM candle_q_dim_analytic_contains_erase]
          proxy_contains_box_e in
      USE_THEN "erasure_equal" (fun erasure_equal ->
        let proxy_contains_erased_center =
          SUBS [SYM erasure_equal] proxy_contains_erased_box in
        let proxy_contains_center_e =
          ONCE_REWRITE_RULE
            [candle_q_dim_analytic_contains_erase]
            proxy_contains_erased_center in
        LABEL_TAC "proxy_contains_center_e" proxy_contains_center_e)) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_regular_at_def] THEN
      USE_THEN "center_regular" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `p:real^N` THEN
      DISCH_THEN (LABEL_TAC "regular_p_in_box") THEN
      REWRITE_TAC[candle_analytic_regular_at_def] THEN
      USE_THEN "box_regular" (fun th ->
        USE_THEN "regular_p_in_box" (fun p_in_box ->
          ACCEPT_TAC (MP (SPEC `p:real^N` th) p_in_box)));
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_jet_atn_faithful_shape THEN
      USE_THEN "center_shape" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "center_contains" (fun center_contains_center_e ->
        USE_THEN "proxy_contains_center_e" (fun proxy_contains_center_e ->
          let center_components =
            REWRITE_RULE[candle_q_dim_analytic_contains_def]
              center_contains_center_e in
          let proxy_components =
            REWRITE_RULE[candle_q_dim_analytic_contains_def]
              proxy_contains_center_e in
          let proxy_application,_ = dest_comb (concl proxy_components) in
          let proxy_application,_ = dest_comb proxy_application in
          let proxy_application,_ = dest_comb proxy_application in
          let _,proxy_jet = dest_comb proxy_application in
          REWRITE_TAC[candle_q_dim_analytic_contains_def;
                      candle_analytic_value_def;
                      candle_analytic_d_def;
                      candle_analytic_dd_def] THEN
          MATCH_MP_TAC
            candle_q_dim_jet_atn_split_faithful_components_sound THEN
          MAP_EVERY EXISTS_TAC
            [`center_input:((num#num)#num)#((num#num)#num)`;
             `center_square:((num#num)#num)#((num#num)#num)`;
             `box_square:((num#num)#num)#((num#num)#num)`;
             `box_derivative:((num#num)#num)#((num#num)#num)`] THEN
          EXISTS_TAC proxy_jet THEN
          REPEAT CONJ_TAC THENL
           [USE_THEN "center_shape" MATCH_ACCEPT_TAC;
            MATCH_ACCEPT_TAC center_components;
            MATCH_ACCEPT_TAC proxy_components;
            USE_THEN "center_atn_certificate" MATCH_ACCEPT_TAC;
            USE_THEN "center_square_certificate" MATCH_ACCEPT_TAC;
            USE_THEN "center_derivative_certificate" MATCH_ACCEPT_TAC;
            USE_THEN "box_square_certificate" MATCH_ACCEPT_TAC;
            USE_THEN "box_derivative_certificate" MATCH_ACCEPT_TAC;
            USE_THEN "box_derivative_square_certificate"
              MATCH_ACCEPT_TAC]));
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_dim_jet_atn_faithful_shape THEN
      USE_THEN "proxy_shape" MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `p:real^N` THEN
    DISCH_THEN (LABEL_TAC "final_p_in_box") THEN
    USE_THEN "box_contains_all" (fun th ->
      USE_THEN "final_p_in_box" (fun p_in_box ->
        let contains_at_p = MP (SPEC `p:real^N` th) p_in_box in
        let components_at_p =
          REWRITE_RULE[candle_q_dim_analytic_contains_def]
            contains_at_p in
        REWRITE_TAC[candle_q_dim_analytic_contains_def;
                    candle_analytic_value_def;
                    candle_analytic_d_def;
                    candle_analytic_dd_def] THEN
        MATCH_MP_TAC candle_q_dim_jet_atn_box_faithful_components_sound THEN
        EXISTS_TAC `box_square:((num#num)#num)#((num#num)#num)` THEN
        REPEAT CONJ_TAC THENL
         [USE_THEN "proxy_shape" MATCH_ACCEPT_TAC;
          MATCH_ACCEPT_TAC components_at_p;
          USE_THEN "box_square_certificate" MATCH_ACCEPT_TAC;
          USE_THEN "box_derivative_certificate" MATCH_ACCEPT_TAC;
          USE_THEN "box_derivative_square_certificate"
            MATCH_ACCEPT_TAC]))]);;


let candle_q_packed_source_item_atn_faithful_def = new_definition
 `candle_q_packed_source_item_atn_faithful boxes
      center_input box_input center_result center_square center_derivative
      box_square box_derivative box_derivative_square item =
    candle_q_packed_source_item_make
      (candle_q_dim_taylor_model_result_atn_faithful
        (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
        box_input center_result center_derivative box_derivative
        box_derivative_square
        (candle_q_packed_source_item_result item))
      (Candle_analytic_atn
        (candle_q_packed_source_item_center_expr item))
      (Candle_analytic_atn
        (candle_q_packed_source_item_box_expr item))`;;

let candle_q_packed_source_item_atn_faithful_analytic_invariant = prove
 (`!boxes center_input box_input center_result center_square
      center_derivative box_square box_derivative box_derivative_square item.
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_q_packed_source_item_analytic_invariant boxes item /\
     candle_q_interval_atn_outer_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item)))
       center_input center_result /\
     candle_q_interval_square_outer_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_result_center
           (candle_q_packed_source_item_result item)))
       center_input center_square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square center_square)
       center_derivative /\
     candle_q_interval_square_outer_certificate
       (candle_q_dim_jet_f
         (candle_q_dim_taylor_model_proxy
           (candle_q_packed_source_item_result item)))
       box_input box_square /\
     candle_q_interval_inv_certificate
       (candle_q_dim_jet_atn_denominator_with_square box_square)
       box_derivative /\
     candle_q_interval_square_outer_certificate
       box_derivative box_derivative box_derivative_square
     ==>
     candle_q_packed_source_item_analytic_invariant boxes
       (candle_q_packed_source_item_atn_faithful boxes
         center_input box_input center_result center_square center_derivative
         box_square box_derivative box_derivative_square item)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "item_invariant")
          (CONJUNCTS_THEN2 (LABEL_TAC "center_atn_certificate")
            (CONJUNCTS_THEN2 (LABEL_TAC "center_square_certificate")
              (CONJUNCTS_THEN2 (LABEL_TAC "center_derivative_certificate")
                (CONJUNCTS_THEN2 (LABEL_TAC "box_square_certificate")
                  (CONJUNCTS_THEN2 (LABEL_TAC "box_derivative_certificate")
                    (LABEL_TAC
                      "box_derivative_square_certificate"))))))))) THEN
  USE_THEN "item_invariant" MP_TAC THEN
  REWRITE_TAC[candle_q_packed_source_item_analytic_invariant_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_packed_source_item_result_def;
                  candle_q_packed_source_item_center_expr_def;
                  candle_q_packed_source_item_box_expr_def]) THEN
  REWRITE_TAC[candle_q_packed_source_item_atn_faithful_def;
              candle_q_packed_source_item_analytic_invariant_def;
              candle_q_packed_source_item_make_def;
              candle_q_packed_source_item_result_def;
              candle_q_packed_source_item_center_expr_def;
              candle_q_packed_source_item_box_expr_def; FST; SND] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    MATCH_MP_TAC
      (CONV_RULE (DEPTH_CONV DIMINDEX_CONV)
        (INST_TYPE [`:6`,`:N`]
          candle_q_dim_taylor_model_result_atn_faithful_analytic_invariant)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC
      [`center_input:((num#num)#num)#((num#num)#num)`;
       `center_square:((num#num)#num)#((num#num)#num)`;
       `box_square:((num#num)#num)#((num#num)#num)`] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "center_atn_certificate" MATCH_ACCEPT_TAC;
      USE_THEN "center_square_certificate" MATCH_ACCEPT_TAC;
      USE_THEN "center_derivative_certificate" MATCH_ACCEPT_TAC;
      USE_THEN "box_square_certificate" MATCH_ACCEPT_TAC;
      USE_THEN "box_derivative_certificate" MATCH_ACCEPT_TAC]]);;


if exists (fun theorem -> hyp theorem <> [])
    [candle_q_interval_square_outer_certificate_sound;
     candle_cv_q_interval_square_outer_certificate_correct;
     candle_q_interval_atn_outer_certificate_sound;
     candle_cv_q_interval_atn_outer_certificate_correct;
     candle_q_dim_jet_atn_derivative_outer_certificate_sound;
     candle_q_dim_jet_atn_second_with_square_sound;
     candle_q_atn_universal_interval_sound;
     candle_q_dim_jet_atn_faithful_shape;
     candle_q_dim_jet_atn_split_faithful_components_sound;
     candle_q_dim_jet_atn_box_faithful_components_sound;
     candle_q_dim_taylor_model_result_atn_faithful_analytic_invariant;
     candle_q_packed_source_item_atn_faithful_analytic_invariant] then
  failwith "packed source certified atan: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_CERTIFIED_ATN_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
