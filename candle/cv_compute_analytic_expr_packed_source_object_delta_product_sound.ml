(* ========================================================================== *)
(* Exact object-q invariant for the optimized [4 * x_i * delta] shortcuts.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Production first faithfully completes the    *)
(* shared delta gradient on the whole box.  The product Hessian consumes that *)
(* completed gradient, rather than the older direct outer-delta gradient.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_delta_base_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_delta_product_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_packed_source_delta_gradient;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_product_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_product_state_complete_sound;;
open Candle_cv_analytic_expr_packed_source_delta_product_jet_sound;;
open Candle_cv_analytic_expr_packed_source_delta_specialized_result_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_taylor_model_packed_object_gradient_sound;;
open Candle_cv_analytic_expr_packed_source_object_invariant;;
open Candle_cv_analytic_expr_packed_source_object_recomplete_sound;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_delta_base_sound;;

let candle_q_packed_object_delta_product_hessian_def = new_definition
 `candle_q_packed_object_delta_product_hessian
      radii center_boxes outer_boxes coordinate =
    let delta_hessian =
      candle_q_packed_delta_hessian_six
        (candle_q_interval_lookup 0 outer_boxes)
        (candle_q_interval_lookup 1 outer_boxes)
        (candle_q_interval_lookup 2 outer_boxes)
        (candle_q_interval_lookup 3 outer_boxes)
        (candle_q_interval_lookup 4 outer_boxes)
        (candle_q_interval_lookup 5 outer_boxes) in
    let delta_gradient =
      candle_q_packed_object_gradient_complete6 radii
        (candle_q_dim_jet_gradient
          (candle_q_packed_delta_jet_environment center_boxes))
        delta_hessian in
    candle_q_packed_delta_product_hessian_six coordinate
      (candle_q_interval_lookup coordinate outer_boxes)
      delta_gradient delta_hessian`;;

let candle_q_packed_object_delta_product_hessian_contains = prove
 (`!center_boxes outer_boxes radii environment coordinate.
     LENGTH center_boxes = 6 /\ LENGTH outer_boxes = 6 /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_stack_contains outer_boxes environment /\
     coordinate < 3
     ==>
     candle_q_stack_contains
       (candle_q_packed_object_delta_product_hessian
         radii center_boxes outer_boxes coordinate)
       (candle_q_packed_hessian6_values
         (\rowindex colindex.
           candle_analytic_dd rowindex colindex environment
             (candle_packed_delta_product_expr coordinate)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (environment:real list) = 6` ASSUME_TAC THENL
   [MP_TAC
      (ASSUME
        `candle_q_stack_contains
          (outer_boxes:
            ((((num#num)#num)#((num#num)#num))list)) environment`) THEN
    REWRITE_TAC[candle_q_stack_contains_all2] THEN
    DISCH_THEN (MP_TAC o MATCH_MP candle_all2_length) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  let contains index =
    MATCH_MP
      (SPECL
        [index;
         `outer_boxes:
            ((((num#num)#num)#((num#num)#num))list)`;
         `environment:real list`]
        candle_q_stack_lookup_contains)
      (ASSUME
        `candle_q_stack_contains outer_boxes environment`) in
  let environment_six =
    MATCH_MP
      (ISPEC `environment:real list` candle_q_six_real_lookup_list)
      (ASSUME `LENGTH (environment:real list) = 6`) in
  let explicit_environment =
    `[candle_q_real_lookup 0 environment;
      candle_q_real_lookup 1 environment;
      candle_q_real_lookup 2 environment;
      candle_q_real_lookup 3 environment;
      candle_q_real_lookup 4 environment;
      candle_q_real_lookup 5 environment]:real list` in
  let outer_stack_explicit =
    EQ_MP
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (AP_TERM
          `(\values:real list.
             candle_q_stack_contains outer_boxes values)`
          environment_six))
      (ASSUME
        `candle_q_stack_contains
          (outer_boxes:
            ((((num#num)#num)#((num#num)#num))list)) environment`) in
  let gradient_contains =
    MATCH_MP
      (SPECL
        [`center_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:
           ((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`;
         explicit_environment]
        candle_q_packed_object_delta_completed_gradient_contains)
      (end_itlist CONJ
        [ASSUME
           `LENGTH
             (center_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
           `LENGTH
             (outer_boxes:
               ((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME
           `candle_q_packed_source_correspondence
             outer_boxes center_boxes outer_boxes radii`;
         outer_stack_explicit]) in
  let gradient_contains =
    REWRITE_RULE
      [num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
       num_CONV `2`; num_CONV `1`; list_of_seq; APPEND]
      gradient_contains in
  let gradient_contains =
    REWRITE_RULE
      [GSYM (num_CONV `1`); GSYM (num_CONV `2`);
       GSYM (num_CONV `3`); GSYM (num_CONV `4`);
       GSYM (num_CONV `5`); GSYM (num_CONV `6`)]
      gradient_contains in
  let real_values =
    [`candle_q_real_lookup 0 environment`;
     `candle_q_real_lookup 1 environment`;
     `candle_q_real_lookup 2 environment`;
     `candle_q_real_lookup 3 environment`;
     `candle_q_real_lookup 4 environment`;
     `candle_q_real_lookup 5 environment`] in
  let explicit_gradient_to_real =
    TRANS
      (SYM
        (SPECL real_values
          candle_real_packed_delta_analytic_gradient_six_def))
      (SYM
        (SPECL real_values
          candle_real_packed_delta_gradient_six_analytic)) in
  let gradient_predicate_equal =
    CONV_RULE (DEPTH_CONV BETA_CONV)
        (AP_TERM
          `(\values:real list.
             candle_q_stack_contains
               (candle_q_packed_object_gradient_complete6 radii
                 (candle_q_dim_jet_gradient
                   (candle_q_packed_delta_jet_environment center_boxes))
                 (candle_q_packed_delta_hessian_six
                   (candle_q_interval_lookup 0 outer_boxes)
                   (candle_q_interval_lookup 1 outer_boxes)
                   (candle_q_interval_lookup 2 outer_boxes)
                   (candle_q_interval_lookup 3 outer_boxes)
                   (candle_q_interval_lookup 4 outer_boxes)
                   (candle_q_interval_lookup 5 outer_boxes)))
               values)`
          explicit_gradient_to_real) in
  let gradient_contains =
    EQ_MP gradient_predicate_equal
      gradient_contains in
  let coordinate_lookup_equal =
    AP_TERM
      `(\values:real list.
         candle_q_real_lookup coordinate values)`
      environment_six in
  let coordinate_predicate_equal =
    CONV_RULE (DEPTH_CONV BETA_CONV)
      (AP_TERM
          `(\value:real.
             candle_q_interval_contains
               (candle_q_interval_lookup coordinate outer_boxes) value)`
        coordinate_lookup_equal) in
  let coordinate_contains =
    EQ_MP coordinate_predicate_equal
      (contains `coordinate:num`) in
  let hessian_contains =
    MATCH_MP
      (SPECL
        [`candle_q_interval_lookup 0 outer_boxes`;
         `candle_q_interval_lookup 1 outer_boxes`;
         `candle_q_interval_lookup 2 outer_boxes`;
         `candle_q_interval_lookup 3 outer_boxes`;
         `candle_q_interval_lookup 4 outer_boxes`;
         `candle_q_interval_lookup 5 outer_boxes`;
         `candle_q_real_lookup 0 environment`;
         `candle_q_real_lookup 1 environment`;
         `candle_q_real_lookup 2 environment`;
         `candle_q_real_lookup 3 environment`;
         `candle_q_real_lookup 4 environment`;
         `candle_q_real_lookup 5 environment`]
        candle_q_packed_delta_hessian_six_sound)
      (end_itlist CONJ
        [contains `0`; contains `1`; contains `2`;
         contains `3`; contains `4`; contains `5`]) in
  REWRITE_TAC[candle_q_packed_object_delta_product_hessian_def;
              LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[environment_six] THEN
  MATCH_MP_TAC candle_q_packed_delta_product_hessian_six_sound THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ACCEPT_TAC coordinate_contains;
    ACCEPT_TAC gradient_contains;
    REWRITE_TAC[candle_q_stack_contains_all2] THEN
    ACCEPT_TAC hessian_contains]);;

if hyp candle_q_packed_object_delta_product_hessian_contains <> [] then
  failwith "packed object delta product Hessian sound: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_OBJECT_DELTA_PRODUCT_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
