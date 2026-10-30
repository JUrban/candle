(* ========================================================================== *)
(* Executable exact result for the three optimized negative-delta steps.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The fixed-word checker recognizes these      *)
(* source instructions, but the ordinary full-source entry must still name  *)
(* their exact rational Taylor state.  This file encodes that state directly *)
(* and proves representation equality for coordinates 3, 4, and 5.          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_certificate_step_compute.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_specialized_result_sound.ml";;

module Candle_cv_analytic_expr_packed_source_delta_neg_derivative_result_compute = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_first_jet_representation;;
open Candle_cv_whole_box_jet;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_packed_hessian_sound;;
open Candle_cv_analytic_expr_packed_source_delta_value;;
open Candle_cv_analytic_expr_packed_source_delta_gradient;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_state_sound;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_state_complete_sound;;
open Candle_cv_analytic_expr_packed_source_delta_neg_derivative_jet_sound;;
open Candle_cv_analytic_expr_packed_source_delta_specialized_result_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_step_compute;;

(* The full analytic Taylor invariant consumes a 6-by-6 symmetric matrix,   *)
(* while both fast and exact optimized states retain its 21 upper entries.   *)

let candle_cv_q_packed_hessian6_expand_def = new_definition
 `candle_cv_q_packed_hessian6_expand packed =
    candle_cv_q_packed_delta_six
      (candle_cv_q_packed_delta_six
        (candle_cv_q_interval_lookup (Cexp_num 0) packed)
        (candle_cv_q_interval_lookup (Cexp_num 1) packed)
        (candle_cv_q_interval_lookup (Cexp_num 2) packed)
        (candle_cv_q_interval_lookup (Cexp_num 3) packed)
        (candle_cv_q_interval_lookup (Cexp_num 4) packed)
        (candle_cv_q_interval_lookup (Cexp_num 5) packed))
      (candle_cv_q_packed_delta_six
        (candle_cv_q_interval_lookup (Cexp_num 1) packed)
        (candle_cv_q_interval_lookup (Cexp_num 6) packed)
        (candle_cv_q_interval_lookup (Cexp_num 7) packed)
        (candle_cv_q_interval_lookup (Cexp_num 8) packed)
        (candle_cv_q_interval_lookup (Cexp_num 9) packed)
        (candle_cv_q_interval_lookup (Cexp_num 10) packed))
      (candle_cv_q_packed_delta_six
        (candle_cv_q_interval_lookup (Cexp_num 2) packed)
        (candle_cv_q_interval_lookup (Cexp_num 7) packed)
        (candle_cv_q_interval_lookup (Cexp_num 11) packed)
        (candle_cv_q_interval_lookup (Cexp_num 12) packed)
        (candle_cv_q_interval_lookup (Cexp_num 13) packed)
        (candle_cv_q_interval_lookup (Cexp_num 14) packed))
      (candle_cv_q_packed_delta_six
        (candle_cv_q_interval_lookup (Cexp_num 3) packed)
        (candle_cv_q_interval_lookup (Cexp_num 8) packed)
        (candle_cv_q_interval_lookup (Cexp_num 12) packed)
        (candle_cv_q_interval_lookup (Cexp_num 15) packed)
        (candle_cv_q_interval_lookup (Cexp_num 16) packed)
        (candle_cv_q_interval_lookup (Cexp_num 17) packed))
      (candle_cv_q_packed_delta_six
        (candle_cv_q_interval_lookup (Cexp_num 4) packed)
        (candle_cv_q_interval_lookup (Cexp_num 9) packed)
        (candle_cv_q_interval_lookup (Cexp_num 13) packed)
        (candle_cv_q_interval_lookup (Cexp_num 16) packed)
        (candle_cv_q_interval_lookup (Cexp_num 18) packed)
        (candle_cv_q_interval_lookup (Cexp_num 19) packed))
      (candle_cv_q_packed_delta_six
        (candle_cv_q_interval_lookup (Cexp_num 5) packed)
        (candle_cv_q_interval_lookup (Cexp_num 10) packed)
        (candle_cv_q_interval_lookup (Cexp_num 14) packed)
        (candle_cv_q_interval_lookup (Cexp_num 17) packed)
        (candle_cv_q_interval_lookup (Cexp_num 19) packed)
        (candle_cv_q_interval_lookup (Cexp_num 20) packed))`;;

let candle_cv_q_interval_lookup_21_correct = prove
 (`!index packed.
     LENGTH packed = 21 /\ index < 21
     ==>
     candle_cv_q_interval_lookup (Cexp_num index)
       (candle_cv_q_interval_list packed) =
     candle_cv_q_interval (EL index packed)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_lookup_correct] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC candle_q_interval_lookup_in_range THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE lookup";;

let candle_cv_q_packed_hessian6_expand_correct = prove
 (`!packed.
     LENGTH packed = 21
     ==>
     candle_cv_q_packed_hessian6_expand
       (candle_cv_q_interval_list packed) =
     candle_cv_q_interval_matrix
       (candle_q_packed_hessian6_expand packed)`,
  REPEAT STRIP_TAC THEN
  let packed_length =
    ASSUME
      `LENGTH
        (packed:((((num#num)#num)#((num#num)#num))list)) = 21` in
  let lookup index bound =
    MATCH_MP
      (SPECL
        [index;
         `packed:((((num#num)#num)#((num#num)#num))list)`]
        candle_cv_q_interval_lookup_21_correct)
      (CONJ packed_length bound) in
  let lookups =
    [lookup `0` (ARITH_RULE `0 < 21`);
     lookup `1` (ARITH_RULE `1 < 21`);
     lookup `2` (ARITH_RULE `2 < 21`);
     lookup `3` (ARITH_RULE `3 < 21`);
     lookup `4` (ARITH_RULE `4 < 21`);
     lookup `5` (ARITH_RULE `5 < 21`);
     lookup `6` (ARITH_RULE `6 < 21`);
     lookup `7` (ARITH_RULE `7 < 21`);
     lookup `8` (ARITH_RULE `8 < 21`);
     lookup `9` (ARITH_RULE `9 < 21`);
     lookup `10` (ARITH_RULE `10 < 21`);
     lookup `11` (ARITH_RULE `11 < 21`);
     lookup `12` (ARITH_RULE `12 < 21`);
     lookup `13` (ARITH_RULE `13 < 21`);
     lookup `14` (ARITH_RULE `14 < 21`);
     lookup `15` (ARITH_RULE `15 < 21`);
     lookup `16` (ARITH_RULE `16 < 21`);
     lookup `17` (ARITH_RULE `17 < 21`);
     lookup `18` (ARITH_RULE `18 < 21`);
     lookup `19` (ARITH_RULE `19 < 21`);
     lookup `20` (ARITH_RULE `20 < 21`)] in
  REWRITE_TAC[candle_cv_q_packed_hessian6_expand_def] THEN
  EVERY (map (fun theorem -> REWRITE_TAC[theorem]) lookups) THEN
  REWRITE_TAC[candle_cv_q_packed_delta_six_correct] THEN
  REWRITE_TAC
    [candle_q_packed_hessian6_expand_def;
     candle_cv_q_packed_delta_six_def;
     candle_cv_q_interval_matrix_def;
     candle_cv_q_interval_list_def]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE expand";;

(* Selecting one row is useful for the center gradient of -d(delta)/dx_i.  *)

let candle_cv_q_interval_matrix_row_lookup_correct = prove
 (`!coordinate rows.
     coordinate < LENGTH rows
     ==>
     candle_cv_q_interval_lookup (Cexp_num coordinate)
       (candle_cv_q_interval_matrix rows) =
     candle_cv_q_interval_list (EL coordinate rows)`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [LENGTH; LT; LT_SUC; EL; HD; TL;
     candle_cv_q_interval_lookup_def;
     candle_cv_q_interval_matrix_def]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE matrix-row";;

let candle_q_packed_hessian6_expand_length = prove
 (`!packed.
     LENGTH (candle_q_packed_hessian6_expand packed) = 6`,
  REWRITE_TAC[candle_q_packed_hessian6_expand_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_hessian6_row_def = new_definition
 `candle_cv_q_packed_hessian6_row coordinate packed =
    candle_cv_q_interval_lookup coordinate
      (candle_cv_q_packed_hessian6_expand packed)`;;

let candle_cv_q_packed_hessian6_row_correct = prove
  (`!coordinate packed.
     coordinate < 6 /\ LENGTH packed = 21
     ==>
     candle_cv_q_packed_hessian6_row (Cexp_num coordinate)
       (candle_cv_q_interval_list packed) =
     candle_cv_q_interval_list
       (EL coordinate (candle_q_packed_hessian6_expand packed))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let expansion =
    MATCH_MP
      (ISPEC
        `packed:((((num#num)#num)#((num#num)#num))list)`
        candle_cv_q_packed_hessian6_expand_correct)
      (ASSUME
        `LENGTH
          (packed:((((num#num)#num)#((num#num)#num))list)) = 21`) in
  REWRITE_TAC[candle_cv_q_packed_hessian6_row_def] THEN
  ONCE_REWRITE_TAC[expansion] THEN
  MATCH_MP_TAC candle_cv_q_interval_matrix_row_lookup_correct THEN
  ASM_REWRITE_TAC[candle_q_packed_hessian6_expand_length]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE row";;

let candle_cv_q_packed_delta_basis_six_def = new_definition
 `candle_cv_q_packed_delta_basis_six coordinate =
    candle_cv_q_packed_delta_six
      (Cexp_if (Cexp_eq coordinate (Cexp_num 0))
        candle_cv_q_one_interval candle_cv_q_zero_interval)
      (Cexp_if (Cexp_eq coordinate (Cexp_num 1))
        candle_cv_q_one_interval candle_cv_q_zero_interval)
      (Cexp_if (Cexp_eq coordinate (Cexp_num 2))
        candle_cv_q_one_interval candle_cv_q_zero_interval)
      (Cexp_if (Cexp_eq coordinate (Cexp_num 3))
        candle_cv_q_one_interval candle_cv_q_zero_interval)
      (Cexp_if (Cexp_eq coordinate (Cexp_num 4))
        candle_cv_q_one_interval candle_cv_q_zero_interval)
      (Cexp_if (Cexp_eq coordinate (Cexp_num 5))
        candle_cv_q_one_interval candle_cv_q_zero_interval)`;;

let candle_cv_if_num_eq_correct = prove
 (`!left right consequent alternative.
     Cexp_if (Cexp_eq (Cexp_num left) (Cexp_num right))
       consequent alternative =
     if left = right then consequent else alternative`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cexp_eq_def] THEN
  REWRITE_TAC[injectivity "cval"] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[cexp_if_def]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE if-helper";;

let candle_cv_q_interval_if_correct = prove
 (`!guard consequent alternative.
     (if guard
      then candle_cv_q_interval consequent
      else candle_cv_q_interval alternative) =
     candle_cv_q_interval
       (if guard then consequent else alternative)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `guard:bool` THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_q_packed_delta_basis_six_correct = prove
 (`!coordinate.
     candle_cv_q_packed_delta_basis_six (Cexp_num coordinate) =
     candle_cv_q_interval_list
       (candle_q_packed_delta_basis_six coordinate)`,
  GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_delta_basis_six_def;
     candle_q_packed_delta_basis_six_def;
     candle_cv_q_packed_delta_six_def;
     candle_cv_q_interval_list_def;
     candle_cv_q_one_interval_correct;
     candle_cv_q_zero_interval_correct;
     candle_cv_if_num_eq_correct;
     candle_cv_q_interval_if_correct]);;

let candle_q_packed_delta_basis_six_length = prove
 (`!coordinate.
     LENGTH (candle_q_packed_delta_basis_six coordinate) = 6`,
  REWRITE_TAC[candle_q_packed_delta_basis_six_def; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_packed_delta_basis_six_lookup = prove
 (`!coordinate index.
     index < 6
     ==>
     candle_q_interval_lookup index
       (candle_q_packed_delta_basis_six coordinate) =
     EL index (candle_q_packed_delta_basis_six coordinate)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC candle_q_interval_lookup_in_range THEN
  ASM_REWRITE_TAC[candle_q_packed_delta_basis_six_length]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE basis";;

let candle_cv_q_packed_delta_neg_derivative_center_value_def = new_definition
 `candle_cv_q_packed_delta_neg_derivative_center_value coordinate
      x0 x1 x2 x3 x4 x5 =
    candle_cv_q_interval_neg
      (candle_cv_q_interval_lookup coordinate
        (candle_cv_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5))`;;

let candle_cv_q_packed_delta_neg_derivative_center_value_correct = prove
 (`!coordinate x0 x1 x2 x3 x4 x5.
     candle_cv_q_packed_delta_neg_derivative_center_value
       (Cexp_num coordinate)
       (candle_cv_q_interval x0) (candle_cv_q_interval x1)
       (candle_cv_q_interval x2) (candle_cv_q_interval x3)
       (candle_cv_q_interval x4) (candle_cv_q_interval x5) =
     candle_cv_q_interval
       (candle_q_packed_delta_neg_derivative_center_value coordinate
         x0 x1 x2 x3 x4 x5)`,
  REWRITE_TAC
    [candle_cv_q_packed_delta_neg_derivative_center_value_def;
     candle_q_packed_delta_neg_derivative_center_value_def;
     candle_cv_q_packed_delta_gradient_six_correct;
     candle_cv_q_interval_lookup_correct;
     candle_cv_q_interval_neg_correct]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE center-value";;

let candle_q_packed_delta_hessian_six_length = prove
 (`!x0 x1 x2 x3 x4 x5.
     LENGTH (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5) = 21`,
  REWRITE_TAC
    [candle_q_packed_delta_hessian_six_def;
     candle_q_packed_delta_hessian_rows_six_def;
     candle_q_packed_delta_sums_def;
     LET_DEF; LET_END_DEF; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_packed_delta_neg_derivative_center_gradient_def =
  new_definition
 `candle_cv_q_packed_delta_neg_derivative_center_gradient coordinate
      x0 x1 x2 x3 x4 x5 =
    candle_cv_q_dim_interval_list_neg
      (candle_cv_q_packed_hessian6_row coordinate
        (candle_cv_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5))`;;

let candle_cv_q_packed_delta_neg_derivative_center_gradient_correct = prove
 (`!coordinate x0 x1 x2 x3 x4 x5.
     coordinate < 6
     ==>
     candle_cv_q_packed_delta_neg_derivative_center_gradient
       (Cexp_num coordinate)
       (candle_cv_q_interval x0) (candle_cv_q_interval x1)
       (candle_cv_q_interval x2) (candle_cv_q_interval x3)
       (candle_cv_q_interval x4) (candle_cv_q_interval x5) =
     candle_cv_q_interval_list
       (candle_q_packed_delta_neg_derivative_center_gradient coordinate
         x0 x1 x2 x3 x4 x5)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_delta_neg_derivative_center_gradient_def;
     candle_q_packed_delta_neg_derivative_center_gradient_def;
     candle_cv_q_packed_delta_hessian_six_correct] THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_hessian6_row (Cexp_num coordinate)
      (candle_cv_q_interval_list
        (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)) =
    candle_cv_q_interval_list
      (EL coordinate
        (candle_q_packed_hessian6_expand
          (candle_q_packed_delta_hessian_six x0 x1 x2 x3 x4 x5)))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_cv_q_packed_hessian6_row_correct THEN
    ASM_REWRITE_TAC[candle_q_packed_delta_hessian_six_length];
    ASM_REWRITE_TAC[candle_cv_q_dim_interval_list_neg_correct]]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE center-gradient";;

let candle_cv_q_packed_delta_neg_derivative_hessian_six_def =
  new_definition
 `candle_cv_q_packed_delta_neg_derivative_hessian_six coordinate =
    let basis = candle_cv_q_packed_delta_basis_six coordinate in
    candle_cv_q_dim_interval_list_neg
      (candle_cv_q_packed_delta_hessian_six
        (candle_cv_q_interval_lookup (Cexp_num 0) basis)
        (candle_cv_q_interval_lookup (Cexp_num 1) basis)
        (candle_cv_q_interval_lookup (Cexp_num 2) basis)
        (candle_cv_q_interval_lookup (Cexp_num 3) basis)
        (candle_cv_q_interval_lookup (Cexp_num 4) basis)
        (candle_cv_q_interval_lookup (Cexp_num 5) basis))`;;

let candle_cv_q_packed_delta_neg_derivative_hessian_six_correct = prove
 (`!coordinate.
     candle_cv_q_packed_delta_neg_derivative_hessian_six
       (Cexp_num coordinate) =
     candle_cv_q_interval_list
       (candle_q_packed_delta_neg_derivative_hessian_six coordinate)`,
  GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_delta_neg_derivative_hessian_six_def;
     candle_q_packed_delta_neg_derivative_hessian_six_def;
     candle_cv_q_packed_delta_basis_six_correct;
     candle_cv_q_interval_lookup_correct;
     candle_cv_q_packed_delta_hessian_six_correct;
     candle_cv_q_dim_interval_list_neg_correct;
     LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC
    [MATCH_MP
       (SPECL [`coordinate:num`; `0`]
         candle_q_packed_delta_basis_six_lookup)
       (ARITH_RULE `0 < 6`);
     MATCH_MP
       (SPECL [`coordinate:num`; `1`]
         candle_q_packed_delta_basis_six_lookup)
       (ARITH_RULE `1 < 6`);
     MATCH_MP
       (SPECL [`coordinate:num`; `2`]
         candle_q_packed_delta_basis_six_lookup)
       (ARITH_RULE `2 < 6`);
     MATCH_MP
       (SPECL [`coordinate:num`; `3`]
         candle_q_packed_delta_basis_six_lookup)
       (ARITH_RULE `3 < 6`);
     MATCH_MP
       (SPECL [`coordinate:num`; `4`]
         candle_q_packed_delta_basis_six_lookup)
       (ARITH_RULE `4 < 6`);
     MATCH_MP
       (SPECL [`coordinate:num`; `5`]
         candle_q_packed_delta_basis_six_lookup)
       (ARITH_RULE `5 < 6`)]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE hessian";;

let candle_q_packed_delta_neg_derivative_hessian_six_length = prove
 (`!coordinate.
     LENGTH
       (candle_q_packed_delta_neg_derivative_hessian_six coordinate) = 21`,
  REWRITE_TAC
    [candle_q_packed_delta_neg_derivative_hessian_six_def;
     candle_q_dim_interval_list_neg_length;
     candle_q_packed_delta_hessian_six_length;
     LET_DEF; LET_END_DEF]);;

let candle_cv_q_packed_delta_neg_derivative_jet_six_def = new_definition
 `candle_cv_q_packed_delta_neg_derivative_jet_six coordinate
      x0 x1 x2 x3 x4 x5 =
    candle_cv_q_dim_jet_make
      (candle_cv_q_packed_delta_neg_derivative_center_value coordinate
        x0 x1 x2 x3 x4 x5)
      (candle_cv_q_packed_delta_neg_derivative_center_gradient coordinate
        x0 x1 x2 x3 x4 x5)
      (candle_cv_q_packed_hessian6_expand
        (candle_cv_q_packed_delta_neg_derivative_hessian_six coordinate))`;;

let candle_cv_q_packed_delta_neg_derivative_jet_six_correct = prove
 (`!coordinate x0 x1 x2 x3 x4 x5.
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_cv_q_packed_delta_neg_derivative_jet_six
       (Cexp_num coordinate)
       (candle_cv_q_interval x0) (candle_cv_q_interval x1)
       (candle_cv_q_interval x2) (candle_cv_q_interval x3)
       (candle_cv_q_interval x4) (candle_cv_q_interval x5) =
     candle_cv_q_dim_jet_encode
       (candle_q_packed_delta_neg_derivative_jet_six coordinate
         x0 x1 x2 x3 x4 x5)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `coordinate < 6` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_hessian6_expand
      (candle_cv_q_interval_list
        (candle_q_packed_delta_neg_derivative_hessian_six coordinate)) =
    candle_cv_q_interval_matrix
      (candle_q_packed_hessian6_expand
        (candle_q_packed_delta_neg_derivative_hessian_six coordinate))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC candle_cv_q_packed_hessian6_expand_correct THEN
    REWRITE_TAC[candle_q_packed_delta_neg_derivative_hessian_six_length];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_delta_neg_derivative_center_gradient
      (Cexp_num coordinate)
      (candle_cv_q_interval x0) (candle_cv_q_interval x1)
      (candle_cv_q_interval x2) (candle_cv_q_interval x3)
      (candle_cv_q_interval x4) (candle_cv_q_interval x5) =
    candle_cv_q_interval_list
      (candle_q_packed_delta_neg_derivative_center_gradient coordinate
        x0 x1 x2 x3 x4 x5)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC
      candle_cv_q_packed_delta_neg_derivative_center_gradient_correct THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC
    [candle_cv_q_packed_delta_neg_derivative_jet_six_def;
     candle_q_packed_delta_neg_derivative_jet_six_def] THEN
  ASM_REWRITE_TAC
    [candle_cv_q_packed_delta_neg_derivative_center_value_correct;
     candle_cv_q_packed_delta_neg_derivative_hessian_six_correct;
     candle_cv_q_dim_jet_make_correct]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE jet";;

let candle_cv_q_packed_delta_neg_derivative_jet_environment_def =
  new_definition
 `candle_cv_q_packed_delta_neg_derivative_jet_environment coordinate
      environment =
    candle_cv_q_packed_delta_neg_derivative_jet_six coordinate
      (candle_cv_q_interval_lookup (Cexp_num 0) environment)
      (candle_cv_q_interval_lookup (Cexp_num 1) environment)
      (candle_cv_q_interval_lookup (Cexp_num 2) environment)
      (candle_cv_q_interval_lookup (Cexp_num 3) environment)
      (candle_cv_q_interval_lookup (Cexp_num 4) environment)
      (candle_cv_q_interval_lookup (Cexp_num 5) environment)`;;

let candle_cv_q_packed_delta_neg_derivative_jet_environment_correct = prove
 (`!coordinate environment.
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_cv_q_packed_delta_neg_derivative_jet_environment
       (Cexp_num coordinate) (candle_cv_q_interval_list environment) =
     candle_cv_q_dim_jet_encode
       (candle_q_packed_delta_neg_derivative_jet_environment
         coordinate environment)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_delta_neg_derivative_jet_environment_def;
     candle_q_packed_delta_neg_derivative_jet_environment_def;
     candle_cv_q_interval_lookup_correct] THEN
  MATCH_MP_TAC candle_cv_q_packed_delta_neg_derivative_jet_six_correct THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE environment";;

let candle_cv_q_packed_delta_neg_derivative_result_def = new_definition
 `candle_cv_q_packed_delta_neg_derivative_result boxes coordinate =
    let center_jet =
      candle_cv_q_packed_delta_neg_derivative_jet_environment coordinate
        (candle_cv_q_center_environment_list boxes) in
    let box_jet =
      candle_cv_q_packed_delta_neg_derivative_jet_environment coordinate
        boxes in
    candle_cv_q_dim_taylor_model_result_complete
      (candle_cv_q_fixed_list_round_upper (candle_cv_q_radius_list boxes))
      (Cexp_num 1)
      (candle_cv_q_dim_jet_first_projection center_jet)
      (candle_cv_q_dim_jet_hessian box_jet)`;;

let candle_cv_q_packed_delta_neg_derivative_result_correct = prove
 (`!boxes coordinate.
     (coordinate = 3 \/ coordinate = 4 \/ coordinate = 5)
     ==>
     candle_cv_q_packed_delta_neg_derivative_result
       (candle_cv_q_interval_list boxes) (Cexp_num coordinate) =
     candle_cv_q_dim_taylor_model_result_encode
       (candle_q_packed_delta_neg_derivative_result boxes coordinate)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_delta_neg_derivative_jet_environment
      (Cexp_num coordinate)
      (candle_cv_q_interval_list
        (candle_q_center_environment_list boxes)) =
    candle_cv_q_dim_jet_encode
      (candle_q_packed_delta_neg_derivative_jet_environment coordinate
        (candle_q_center_environment_list boxes))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC
      candle_cv_q_packed_delta_neg_derivative_jet_environment_correct THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_delta_neg_derivative_jet_environment
      (Cexp_num coordinate) (candle_cv_q_interval_list boxes) =
    candle_cv_q_dim_jet_encode
      (candle_q_packed_delta_neg_derivative_jet_environment
        coordinate boxes)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC
      candle_cv_q_packed_delta_neg_derivative_jet_environment_correct THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_cv_q_dim_jet_first_projection
      (candle_cv_q_packed_delta_neg_derivative_jet_environment
        (Cexp_num coordinate)
        (candle_cv_q_interval_list
          (candle_q_center_environment_list boxes))) =
    candle_cv_q_dim_first_jet_encode
      (candle_q_packed_delta_neg_derivative_jet_environment coordinate
        (candle_q_center_environment_list boxes))`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM candle_cv_q_dim_first_jet_encode_projection];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_cv_q_dim_jet_hessian
      (candle_cv_q_packed_delta_neg_derivative_jet_environment
        (Cexp_num coordinate) (candle_cv_q_interval_list boxes)) =
    candle_cv_q_interval_matrix
      (candle_q_dim_jet_hessian
        (candle_q_packed_delta_neg_derivative_jet_environment
          coordinate boxes))`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[candle_cv_q_dim_jet_hessian_correct];
    ALL_TAC] THEN
  REWRITE_TAC
    [candle_cv_q_packed_delta_neg_derivative_result_def;
     candle_q_packed_delta_neg_derivative_result_def;
     candle_cv_q_center_environment_list_correct;
     candle_cv_q_radius_list_correct;
     candle_cv_q_fixed_list_round_upper_correct;
     LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[candle_cv_bool_true_encoding] THEN
  REWRITE_TAC[candle_cv_q_dim_taylor_model_result_complete_correct]);;

let _ = print_endline "CANDLE_NEG_DELTA_RESULT_STAGE result";;

let candle_cv_q_packed_source_delta_neg_derivative_result_compute_eqs =
  union
    candle_cv_q_packed_source_certificate_step_compute_eqs
    (map SPEC_ALL
      [candle_cv_q_packed_hessian6_expand_def;
       candle_cv_q_packed_hessian6_row_def;
       candle_cv_q_packed_delta_basis_six_def;
       candle_cv_q_packed_delta_neg_derivative_center_value_def;
       candle_cv_q_packed_delta_neg_derivative_center_gradient_def;
       candle_cv_q_packed_delta_neg_derivative_hessian_six_def;
       candle_cv_q_packed_delta_neg_derivative_jet_six_def;
       candle_cv_q_packed_delta_neg_derivative_jet_environment_def;
       candle_cv_q_packed_delta_neg_derivative_result_def]);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_cv_q_packed_hessian6_expand_correct;
     candle_cv_q_interval_lookup_21_correct;
     candle_cv_q_interval_matrix_row_lookup_correct;
     candle_q_packed_hessian6_expand_length;
     candle_cv_q_packed_hessian6_row_correct;
     candle_cv_if_num_eq_correct;
     candle_cv_q_interval_if_correct;
     candle_cv_q_packed_delta_basis_six_correct;
     candle_q_packed_delta_basis_six_length;
     candle_q_packed_delta_basis_six_lookup;
     candle_cv_q_packed_delta_neg_derivative_center_value_correct;
     candle_cv_q_packed_delta_neg_derivative_center_gradient_correct;
     candle_cv_q_packed_delta_neg_derivative_hessian_six_correct;
     candle_q_packed_delta_hessian_six_length;
     candle_q_packed_delta_neg_derivative_hessian_six_length;
     candle_cv_q_packed_delta_neg_derivative_jet_six_correct;
     candle_cv_q_packed_delta_neg_derivative_jet_environment_correct;
     candle_cv_q_packed_delta_neg_derivative_result_correct] then
  failwith "packed negative delta derivative result compute: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_NEG_DERIVATIVE_RESULT_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
