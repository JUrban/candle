(* ========================================================================== *)
(* Analytic identities for the optimized Flyspeck delta tables.              *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The packed checker evaluates compact value,   *)
(* gradient, and upper-triangular Hessian tables.  These theorems identify    *)
(* those exact real tables with the value and formal derivatives of one      *)
(* source-generic analytic polynomial.                                       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_delta_gradient.ml";;

module Candle_cv_analytic_expr_packed_source_delta_analytic = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_packed_source_delta_value;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;
open Candle_cv_analytic_expr_packed_source_delta_gradient;;

let candle_packed_delta_poly_def = new_definition
 `candle_packed_delta_poly =
    Candle_poly_add
      (Candle_poly_mul (Candle_poly_var 0)
        (Candle_poly_mul (Candle_poly_var 3)
          (Candle_poly_add (Candle_poly_neg (Candle_poly_var 0))
            (Candle_poly_add (Candle_poly_var 1)
              (Candle_poly_add
                (Candle_poly_add (Candle_poly_var 2)
                  (Candle_poly_neg (Candle_poly_var 3)))
                (Candle_poly_add (Candle_poly_var 4)
                  (Candle_poly_var 5)))))))
      (Candle_poly_add
        (Candle_poly_mul (Candle_poly_var 1)
          (Candle_poly_mul (Candle_poly_var 4)
            (Candle_poly_add
              (Candle_poly_add (Candle_poly_var 0)
                (Candle_poly_neg (Candle_poly_var 1)))
              (Candle_poly_add (Candle_poly_var 2)
                (Candle_poly_add
                  (Candle_poly_add (Candle_poly_var 3)
                    (Candle_poly_neg (Candle_poly_var 4)))
                  (Candle_poly_var 5))))))
        (Candle_poly_add
          (Candle_poly_add
            (Candle_poly_add
              (Candle_poly_add
                (Candle_poly_mul (Candle_poly_var 2)
                  (Candle_poly_mul (Candle_poly_var 5)
                    (Candle_poly_add (Candle_poly_var 0)
                      (Candle_poly_add
                        (Candle_poly_add (Candle_poly_var 1)
                          (Candle_poly_neg (Candle_poly_var 2)))
                        (Candle_poly_add (Candle_poly_var 3)
                          (Candle_poly_add (Candle_poly_var 4)
                            (Candle_poly_neg (Candle_poly_var 5))))))))
                (Candle_poly_neg
                  (Candle_poly_mul (Candle_poly_var 1)
                    (Candle_poly_mul (Candle_poly_var 2)
                      (Candle_poly_var 3)))))
              (Candle_poly_neg
                (Candle_poly_mul (Candle_poly_var 0)
                  (Candle_poly_mul (Candle_poly_var 2)
                    (Candle_poly_var 4)))))
            (Candle_poly_neg
              (Candle_poly_mul (Candle_poly_var 0)
                (Candle_poly_mul (Candle_poly_var 1)
                  (Candle_poly_var 5)))))
          (Candle_poly_neg
            (Candle_poly_mul (Candle_poly_var 3)
              (Candle_poly_mul (Candle_poly_var 4)
                (Candle_poly_var 5))))))`;;

let candle_packed_delta_expr_def = new_definition
 `candle_packed_delta_expr = Candle_analytic_poly candle_packed_delta_poly`;;

let candle_packed_delta_poly_valid = prove
 (`candle_poly_valid_dim 6 candle_packed_delta_poly`,
  REWRITE_TAC[candle_packed_delta_poly_def; candle_poly_valid_dim_def] THEN
  ARITH_TAC);;

let candle_packed_delta_value_analytic = prove
 (`!v0 v1 v2 v3 v4 v5.
     candle_analytic_value [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr =
     candle_packed_delta_real v0 v1 v2 v3 v4 v5`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_packed_delta_expr_def; candle_packed_delta_poly_def;
              candle_analytic_value_def; candle_poly_value_list_def;
              candle_packed_delta_real_def;
              ITLIST] THEN
  REWRITE_TAC[num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; candle_q_real_lookup_def] THEN
  CONV_TAC REAL_RING);;

let candle_real_packed_delta_analytic_gradient_six_def = new_definition
 `candle_real_packed_delta_analytic_gradient_six v0 v1 v2 v3 v4 v5 =
    [candle_analytic_d 0 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_d 1 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_d 2 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_d 3 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_d 4 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_d 5 [v0;v1;v2;v3;v4;v5]
     candle_packed_delta_expr]`;;

let candle_packed_delta_analytic_d = prove
 (`!v0 v1 v2 v3 v4 v5 coordinate.
     coordinate < 6
     ==> candle_analytic_d coordinate [v0;v1;v2;v3;v4;v5]
           candle_packed_delta_expr =
         EL coordinate
           (candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2 \/
    coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`
  MP_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[candle_real_packed_delta_gradient_six_def;
              candle_packed_delta_expr_def; candle_packed_delta_poly_def;
              candle_analytic_d_def; candle_poly_d_list_def;
              candle_poly_value_list_def;
              candle_real_packed_delta_sum_def;
              candle_real_packed_delta_sum_aux_def;
              LET_DEF; LET_END_DEF; ITLIST] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; candle_q_real_lookup_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING);;

let candle_real_packed_delta_gradient_six_analytic = prove
 (`!v0 v1 v2 v3 v4 v5.
     candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5 =
     candle_real_packed_delta_analytic_gradient_six v0 v1 v2 v3 v4 v5`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;
                 `v5:real`;`0`] candle_packed_delta_analytic_d) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  MP_TAC (SPECL [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;
                 `v5:real`;`1`] candle_packed_delta_analytic_d) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  MP_TAC (SPECL [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;
                 `v5:real`;`2`] candle_packed_delta_analytic_d) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  MP_TAC (SPECL [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;
                 `v5:real`;`3`] candle_packed_delta_analytic_d) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  MP_TAC (SPECL [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;
                 `v5:real`;`4`] candle_packed_delta_analytic_d) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  MP_TAC (SPECL [`v0:real`;`v1:real`;`v2:real`;`v3:real`;`v4:real`;
                 `v5:real`;`5`] candle_packed_delta_analytic_d) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[candle_real_packed_delta_analytic_gradient_six_def] THEN
  REWRITE_TAC[candle_real_packed_delta_gradient_six_def;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  REFL_TAC);;

let candle_real_packed_delta_analytic_hessian_six_def = new_definition
 `candle_real_packed_delta_analytic_hessian_six v0 v1 v2 v3 v4 v5 =
    [candle_analytic_dd 0 0 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 0 1 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 0 2 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 0 3 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 0 4 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 0 5 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 1 1 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 1 2 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 1 3 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 1 4 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 1 5 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 2 2 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 2 3 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 2 4 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 2 5 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 3 3 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 3 4 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 3 5 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 4 4 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 4 5 [v0;v1;v2;v3;v4;v5]
       candle_packed_delta_expr;
     candle_analytic_dd 5 5 [v0;v1;v2;v3;v4;v5]
     candle_packed_delta_expr]`;;

let candle_packed_delta_hessian_upper_index_def = new_definition
 `candle_packed_delta_hessian_upper_index rowindex colindex =
    if rowindex = 0 then colindex
    else if rowindex = 1 then 5 + colindex
    else if rowindex = 2 then 9 + colindex
    else if rowindex = 3 then 12 + colindex
    else if rowindex = 4 then 14 + colindex
    else 15 + colindex`;;

let candle_packed_delta_analytic_dd_upper = prove
 (`!v0 v1 v2 v3 v4 v5 rowindex colindex.
     rowindex < 6 /\ rowindex <= colindex /\ colindex < 6
     ==> candle_analytic_dd rowindex colindex [v0;v1;v2;v3;v4;v5]
           candle_packed_delta_expr =
         EL (candle_packed_delta_hessian_upper_index rowindex colindex)
           (candle_real_packed_delta_hessian_six v0 v1 v2 v3 v4 v5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
   (ARITH_RULE
     `rowindex < 6
      ==> rowindex = 0 \/ rowindex = 1 \/ rowindex = 2 \/
          rowindex = 3 \/ rowindex = 4 \/ rowindex = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  MP_TAC
   (ARITH_RULE
     `colindex < 6
      ==> colindex = 0 \/ colindex = 1 \/ colindex = 2 \/
          colindex = 3 \/ colindex = 4 \/ colindex = 5`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  TRY ASM_ARITH_TAC THEN
  REWRITE_TAC[candle_packed_delta_hessian_upper_index_def;
              candle_real_packed_delta_hessian_six_def;
              candle_real_packed_delta_hessian_rows_six_def;
              candle_real_packed_delta_sums_def;
              candle_real_packed_delta_sum_def;
              candle_real_packed_delta_sum_aux_def;
              candle_packed_delta_expr_def; candle_packed_delta_poly_def;
              candle_analytic_dd_def; candle_poly_dd_list_def;
              candle_poly_d_list_def; candle_poly_value_list_def;
              LET_DEF; LET_END_DEF; ITLIST] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[num_CONV `20`; num_CONV `19`; num_CONV `18`;
              num_CONV `17`; num_CONV `16`; num_CONV `15`;
              num_CONV `14`; num_CONV `13`; num_CONV `12`;
              num_CONV `11`; num_CONV `10`; num_CONV `9`;
              num_CONV `8`; num_CONV `7`; num_CONV `6`;
              num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; candle_q_real_lookup_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  CONV_TAC REAL_RING);;

let candle_real_packed_delta_hessian_six_analytic = prove
 (`!v0 v1 v2 v3 v4 v5.
     candle_real_packed_delta_hessian_six v0 v1 v2 v3 v4 v5 =
     candle_real_packed_delta_analytic_hessian_six v0 v1 v2 v3 v4 v5`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_real_packed_delta_hessian_six_def;
              candle_real_packed_delta_hessian_rows_six_def;
              candle_real_packed_delta_sums_def;
              candle_real_packed_delta_analytic_hessian_six_def;
              LET_DEF; LET_END_DEF; CONS_11] THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[candle_real_packed_delta_sum_def;
              candle_real_packed_delta_sum_aux_def;
              candle_packed_delta_expr_def; candle_packed_delta_poly_def;
              candle_analytic_dd_def; candle_poly_dd_list_def;
              candle_poly_d_list_def; candle_poly_value_list_def;
              ITLIST] THEN
  REWRITE_TAC[num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; candle_q_real_lookup_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING);;

if exists (fun theorem -> hyp theorem <> [])
    [candle_packed_delta_poly_valid;
     candle_packed_delta_value_analytic;
     candle_packed_delta_analytic_d;
     candle_real_packed_delta_gradient_six_analytic;
     candle_packed_delta_analytic_dd_upper;
     candle_real_packed_delta_hessian_six_analytic] then
  failwith "packed source delta analytic: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_ANALYTIC_OK DEVELOPMENT_NON_RELEASE";;

end;;
