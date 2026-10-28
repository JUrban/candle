(* ========================================================================== *)
(* Analytic product identities for the optimized [4 * x_i * delta] family.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  These theorems connect the exact packed       *)
(* value/gradient/Hessian formulas to one coordinate-parametric analytic     *)
(* expression.  No case-10173 theorem literal occurs in this layer.          *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_calculus.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_analytic.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_product_hessian.ml";;

module Candle_cv_analytic_expr_packed_source_delta_product_analytic = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_packed_source_delta_gradient;;
open Candle_cv_analytic_expr_packed_source_delta_analytic;;
open Candle_cv_analytic_expr_packed_source_delta_product_hessian;;

let candle_packed_four_expr_def = new_definition
 `candle_packed_four_expr =
    Candle_analytic_poly (Candle_poly_const 4 0 0)`;;

let candle_packed_coordinate_expr_def = new_definition
 `candle_packed_coordinate_expr coordinate =
    Candle_analytic_poly (Candle_poly_var coordinate)`;;

let candle_packed_delta_product_expr_def = new_definition
 `candle_packed_delta_product_expr coordinate =
    Candle_analytic_mul candle_packed_four_expr
      (Candle_analytic_mul (candle_packed_coordinate_expr coordinate)
        candle_packed_delta_expr)`;;

let candle_real_packed_delta_product_value_def = new_definition
 `candle_real_packed_delta_product_value coordinate_value delta_value =
    candle_real_packed_delta_scale4 (coordinate_value * delta_value)`;;

let candle_real_packed_delta_product_gradient_entry_def = new_definition
 `candle_real_packed_delta_product_gradient_entry coordinate coordinate_value
      delta_value delta_gradient derivative_coordinate =
    let base = coordinate_value *
      EL derivative_coordinate delta_gradient in
    let complete =
      if derivative_coordinate = coordinate then base + delta_value
      else base in
    candle_real_packed_delta_scale4 complete`;;

let candle_real_packed_delta_gradient_six_length = prove
 (`!v0 v1 v2 v3 v4 v5.
     LENGTH
       (candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5) = 6`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_real_packed_delta_gradient_six_def;
              LET_DEF; LET_END_DEF; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_q_real_lookup_packed_delta_gradient_six = prove
 (`!v0 v1 v2 v3 v4 v5 coordinate.
     coordinate < 6
     ==> candle_q_real_lookup coordinate
           (candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5) =
         EL coordinate
           (candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC candle_q_real_lookup_in_range THEN
  ASM_REWRITE_TAC[candle_real_packed_delta_gradient_six_length]);;

let candle_packed_delta_product_analytic_value = prove
 (`!v0 v1 v2 v3 v4 v5 coordinate.
     coordinate < 6
     ==> candle_analytic_value [v0;v1;v2;v3;v4;v5]
           (candle_packed_delta_product_expr coordinate) =
         candle_real_packed_delta_product_value
           (candle_q_real_lookup coordinate [v0;v1;v2;v3;v4;v5])
           (candle_packed_delta_real v0 v1 v2 v3 v4 v5)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_packed_delta_product_expr_def;
              candle_packed_four_expr_def;
              candle_packed_coordinate_expr_def;
              candle_real_packed_delta_product_value_def;
              candle_real_packed_delta_scale4_def;
              candle_analytic_value_def; candle_poly_value_list_def;
              candle_packed_delta_value_analytic;
              candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND; LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN
  CONV_TAC REAL_RING);;

let candle_packed_delta_product_analytic_d = prove
 (`!v0 v1 v2 v3 v4 v5 coordinate derivative_coordinate.
     coordinate < 6 /\ derivative_coordinate < 6
     ==> candle_analytic_d derivative_coordinate [v0;v1;v2;v3;v4;v5]
           (candle_packed_delta_product_expr coordinate) =
         candle_real_packed_delta_product_gradient_entry coordinate
           (candle_q_real_lookup coordinate [v0;v1;v2;v3;v4;v5])
           (candle_packed_delta_real v0 v1 v2 v3 v4 v5)
           (candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5)
           derivative_coordinate`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC
    (MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `derivative_coordinate:num`]
        candle_packed_delta_analytic_d)
      (ASSUME `derivative_coordinate < 6`)) THEN
  ASM_CASES_TAC `(derivative_coordinate:num) = coordinate` THENL
   [POP_ASSUM SUBST_ALL_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[candle_packed_delta_product_expr_def;
                  candle_packed_four_expr_def;
                  candle_packed_coordinate_expr_def;
                  candle_real_packed_delta_product_gradient_entry_def;
                  candle_real_packed_delta_scale4_def;
                  candle_analytic_value_def; candle_analytic_d_def;
                  candle_poly_value_list_def; candle_poly_d_list_def;
                  candle_packed_delta_value_analytic;
                  candle_packed_delta_analytic_d;
                  LENGTH;
                  LET_DEF; LET_END_DEF;
                  candle_q_real_def; candle_q_den_def;
                  candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN
  CONV_TAC REAL_RING);;

let candle_packed_delta_product_analytic_dd_upper = prove
 (`!v0 v1 v2 v3 v4 v5 coordinate rowindex colindex.
     coordinate < 6 /\ rowindex < 6 /\ rowindex <= colindex /\
     colindex < 6
     ==> candle_analytic_dd rowindex colindex [v0;v1;v2;v3;v4;v5]
           (candle_packed_delta_product_expr coordinate) =
         candle_real_packed_delta_product_hessian_entry coordinate
           (candle_q_real_lookup coordinate [v0;v1;v2;v3;v4;v5])
           (candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5)
           rowindex colindex
           (EL (candle_packed_delta_hessian_upper_index rowindex colindex)
             (candle_real_packed_delta_hessian_six v0 v1 v2 v3 v4 v5))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
       `rowindex:num`]
      candle_packed_delta_analytic_d) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
       `colindex:num`]
      candle_packed_delta_analytic_d) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
       `rowindex:num`;`colindex:num`]
      candle_packed_delta_analytic_dd_upper) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASSUME_TAC
    (MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `rowindex:num`]
        candle_q_real_lookup_packed_delta_gradient_six)
      (ASSUME `rowindex < 6`)) THEN
  ASSUME_TAC
    (MATCH_MP
      (SPECL
        [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;`v5:real`;
         `colindex:num`]
        candle_q_real_lookup_packed_delta_gradient_six)
      (ASSUME `colindex < 6`)) THEN
  (ASM_CASES_TAC `(rowindex:num) = coordinate` THENL
    [POP_ASSUM SUBST_ALL_TAC;
     ALL_TAC]) THEN
  (ASM_CASES_TAC `(colindex:num) = coordinate` THENL
    [POP_ASSUM SUBST_ALL_TAC;
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[candle_packed_delta_product_expr_def;
                  candle_packed_four_expr_def;
                  candle_packed_coordinate_expr_def;
                  candle_real_packed_delta_product_hessian_entry_def;
                  candle_real_packed_delta_scale4_def;
                  candle_analytic_value_def; candle_analytic_d_def;
                  candle_analytic_dd_def; candle_poly_value_list_def;
                  candle_poly_d_list_def; candle_poly_dd_list_def;
                  candle_packed_delta_value_analytic;
                  candle_packed_delta_analytic_d;
                  candle_packed_delta_analytic_dd_upper;
                  candle_real_packed_delta_gradient_six_length;
                  candle_q_real_lookup_in_range; LENGTH;
                  LET_DEF; LET_END_DEF;
                  candle_q_real_def; candle_q_den_def;
                  candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN
  CONV_TAC REAL_RING);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_real_packed_delta_gradient_six_length;
     candle_q_real_lookup_packed_delta_gradient_six;
     candle_packed_delta_product_analytic_value;
     candle_packed_delta_product_analytic_d;
     candle_packed_delta_product_analytic_dd_upper] then
  failwith "packed source delta product analytic: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_PRODUCT_ANALYTIC_OK DEVELOPMENT_NON_RELEASE";;

end;;
