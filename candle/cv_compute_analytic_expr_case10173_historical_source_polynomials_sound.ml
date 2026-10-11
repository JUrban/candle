(* ========================================================================== *)
(* Case-10173 source polynomials for the historical-dihedral splice.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_sqrt_factorization_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_source_polynomials_sound = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_root_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_delta_x4_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_root_four_x0_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sqrt_factorization_sound;;

(* These ASTs are the positive [delta_x4], [delta], and [4*x0] subterms in
   the authenticated case-10173 source expression.  The source program pushes
   [--delta_x4] and [4*x0*delta]; the historical instruction applies the
   numerator negation internally and factors the latter square root. *)

let candle_case10173_hist_delta_x4_poly_def = new_definition
 `candle_case10173_hist_delta_x4_poly =
    Candle_poly_add
      (Candle_poly_add
        (Candle_poly_mul (Candle_poly_neg (Candle_poly_var 1))
          (Candle_poly_var 2))
        (Candle_poly_neg
          (Candle_poly_mul (Candle_poly_var 0) (Candle_poly_var 3))))
      (Candle_poly_add
        (Candle_poly_mul (Candle_poly_var 1) (Candle_poly_var 4))
        (Candle_poly_add
          (Candle_poly_add
            (Candle_poly_mul (Candle_poly_var 2) (Candle_poly_var 5))
            (Candle_poly_neg
              (Candle_poly_mul (Candle_poly_var 4) (Candle_poly_var 5))))
          (Candle_poly_mul (Candle_poly_var 0)
            (Candle_poly_add (Candle_poly_neg (Candle_poly_var 0))
              (Candle_poly_add (Candle_poly_var 1)
                (Candle_poly_add
                  (Candle_poly_add (Candle_poly_var 2)
                    (Candle_poly_neg (Candle_poly_var 3)))
                  (Candle_poly_add (Candle_poly_var 4)
                    (Candle_poly_var 5))))))))`;;

let candle_case10173_hist_delta_poly_def = new_definition
 `candle_case10173_hist_delta_poly =
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

let candle_case10173_hist_four_x0_poly_def = new_definition
 `candle_case10173_hist_four_x0_poly =
    Candle_poly_mul (Candle_poly_const 4 0 0) (Candle_poly_var 0)`;;

let candle_case10173_hist_source_radical_poly_def = new_definition
 `candle_case10173_hist_source_radical_poly =
    Candle_poly_mul (Candle_poly_const 4 0 0)
      (Candle_poly_mul (Candle_poly_var 0)
        candle_case10173_hist_delta_poly)`;;

let candle_case10173_hist_delta_x4_expr_def = new_definition
 `candle_case10173_hist_delta_x4_expr =
    Candle_analytic_poly candle_case10173_hist_delta_x4_poly`;;

let candle_case10173_hist_delta_expr_def = new_definition
 `candle_case10173_hist_delta_expr =
    Candle_analytic_poly candle_case10173_hist_delta_poly`;;

let candle_case10173_hist_four_x0_expr_def = new_definition
 `candle_case10173_hist_four_x0_expr =
    Candle_analytic_poly candle_case10173_hist_four_x0_poly`;;

let candle_case10173_hist_source_radical_expr_def = new_definition
 `candle_case10173_hist_source_radical_expr =
    Candle_analytic_poly candle_case10173_hist_source_radical_poly`;;

let candle_case10173_hist_delta_x4_poly_valid = prove
 (`candle_poly_valid_dim 6 candle_case10173_hist_delta_x4_poly`,
  REWRITE_TAC[candle_case10173_hist_delta_x4_poly_def;
              candle_poly_valid_dim_def] THEN ARITH_TAC);;

let candle_case10173_hist_delta_poly_valid = prove
 (`candle_poly_valid_dim 6 candle_case10173_hist_delta_poly`,
  REWRITE_TAC[candle_case10173_hist_delta_poly_def;
              candle_poly_valid_dim_def] THEN ARITH_TAC);;

let candle_case10173_hist_four_x0_poly_valid = prove
 (`candle_poly_valid_dim 6 candle_case10173_hist_four_x0_poly`,
  REWRITE_TAC[candle_case10173_hist_four_x0_poly_def;
              candle_poly_valid_dim_def] THEN ARITH_TAC);;

let candle_case10173_hist_source_radical_poly_valid = prove
 (`candle_poly_valid_dim 6 candle_case10173_hist_source_radical_poly`,
  REWRITE_TAC[candle_case10173_hist_source_radical_poly_def;
              candle_case10173_hist_delta_poly_valid;
              candle_poly_valid_dim_def] THEN ARITH_TAC);;

let candle_case10173_hist_delta_x4_value = prove
 (`!values.
     candle_analytic_value (list_of_seq values 6)
       candle_case10173_hist_delta_x4_expr =
     candle_fs_hist_delta_x4_real values`,
  GEN_TAC THEN
  REWRITE_TAC[candle_case10173_hist_delta_x4_expr_def;
              candle_case10173_hist_delta_x4_poly_def;
              candle_analytic_value_def; candle_poly_value_list_def;
              candle_fs_hist_delta_x4_real_def;
              LET_DEF; LET_END_DEF; ITLIST] THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND;
              candle_q_real_lookup_def] THEN
  CONV_TAC REAL_RING);;

let candle_case10173_hist_delta_value = prove
 (`!values.
     candle_analytic_value (list_of_seq values 6)
       candle_case10173_hist_delta_expr =
     candle_fs_hist_delta_real values`,
  GEN_TAC THEN
  REWRITE_TAC[candle_case10173_hist_delta_expr_def;
              candle_case10173_hist_delta_poly_def;
              candle_analytic_value_def; candle_poly_value_list_def;
              candle_fs_hist_delta_real_def;
              LET_DEF; LET_END_DEF; ITLIST] THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND;
              candle_q_real_lookup_def] THEN
  CONV_TAC REAL_RING);;

let candle_case10173_hist_four_x0_value = prove
 (`!values.
     candle_analytic_value (list_of_seq values 6)
       candle_case10173_hist_four_x0_expr =
     candle_fs_hist_four_x0_real values`,
  GEN_TAC THEN
  REWRITE_TAC[candle_case10173_hist_four_x0_expr_def;
              candle_case10173_hist_four_x0_poly_def;
              candle_analytic_value_def; candle_poly_value_list_def;
              candle_fs_hist_four_x0_real_def] THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND;
              candle_q_real_lookup_def] THEN
  REWRITE_TAC[candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN
  REAL_ARITH_TAC);;

let candle_case10173_hist_source_radical_value = prove
 (`!values.
     candle_analytic_value (list_of_seq values 6)
       candle_case10173_hist_source_radical_expr =
     candle_fs_hist_four_x0_real values *
       candle_fs_hist_delta_real values`,
  GEN_TAC THEN
  REWRITE_TAC[candle_case10173_hist_source_radical_expr_def;
              candle_case10173_hist_source_radical_poly_def;
              candle_case10173_hist_delta_poly_def;
              candle_analytic_value_def; candle_poly_value_list_def;
              candle_fs_hist_four_x0_real_def;
              candle_fs_hist_delta_real_def;
              LET_DEF; LET_END_DEF; ITLIST] THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND;
              candle_q_real_lookup_def] THEN
  REWRITE_TAC[candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN
  CONV_TAC REAL_RING);;

let candle_case10173_hist_delta_x4_d = prove
 (`!values coordinate.
     coordinate < 6
     ==> candle_analytic_d coordinate (list_of_seq values 6)
           candle_case10173_hist_delta_x4_expr =
         candle_fs_hist_delta_x4_derivative values coordinate`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2 \/
    coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`
  MP_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[candle_case10173_hist_delta_x4_expr_def;
              candle_case10173_hist_delta_x4_poly_def;
              candle_analytic_d_def; candle_poly_d_list_def;
              candle_poly_value_list_def;
              candle_fs_hist_delta_x4_derivative_def] THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND;
              candle_q_real_lookup_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING);;

let candle_case10173_hist_delta_d = prove
 (`!values coordinate.
     coordinate < 6
     ==> candle_analytic_d coordinate (list_of_seq values 6)
           candle_case10173_hist_delta_expr =
         EL coordinate (candle_fs_hist_delta_gradient_real values)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2 \/
    coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`
  MP_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[candle_case10173_hist_delta_expr_def;
              candle_case10173_hist_delta_poly_def;
              candle_analytic_d_def; candle_poly_d_list_def;
              candle_poly_value_list_def;
              candle_fs_hist_delta_gradient_real_def;
              LET_DEF; LET_END_DEF; ITLIST] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND;
              candle_q_real_lookup_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING);;

let candle_case10173_hist_four_x0_d = prove
 (`!values coordinate.
     coordinate < 6
     ==> candle_analytic_d coordinate (list_of_seq values 6)
           candle_case10173_hist_four_x0_expr =
         candle_fs_hist_four_x0_gradient_real coordinate`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2 \/
    coordinate = 3 \/ coordinate = 4 \/ coordinate = 5`
  MP_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[candle_case10173_hist_four_x0_expr_def;
              candle_case10173_hist_four_x0_poly_def;
              candle_analytic_d_def; candle_poly_d_list_def;
              candle_poly_value_list_def;
              candle_fs_hist_four_x0_gradient_real_def] THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND;
              candle_q_real_lookup_def;
              candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN
  CONV_TAC REAL_RING);;

let candle_case10173_hist_delta_x4_dd = prove
 (`!values (rowindex:num) colindex.
     rowindex < 6 /\ colindex < 6
     ==> candle_analytic_dd rowindex colindex (list_of_seq values 6)
           candle_case10173_hist_delta_x4_expr =
         candle_fs_hist_delta_x4_hessian_component_real rowindex colindex`,
  REPEAT STRIP_TAC THEN
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
  REWRITE_TAC[candle_case10173_hist_delta_x4_expr_def;
              candle_case10173_hist_delta_x4_poly_def;
              candle_analytic_dd_def; candle_poly_dd_list_def;
              candle_poly_d_list_def; candle_poly_value_list_def;
              candle_fs_hist_delta_x4_hessian_component_real_def;
              candle_fs_hist_delta_x4_hessian_real_def] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND;
              candle_q_real_lookup_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING);;

let candle_case10173_hist_delta_dd = prove
 (`!values (rowindex:num) colindex.
     rowindex < 6 /\ colindex < 6
     ==> candle_analytic_dd rowindex colindex (list_of_seq values 6)
           candle_case10173_hist_delta_expr =
         candle_fs_hist_delta_hessian_component_real
           values rowindex colindex`,
  REPEAT STRIP_TAC THEN
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
  REWRITE_TAC[candle_case10173_hist_delta_expr_def;
              candle_case10173_hist_delta_poly_def;
              candle_analytic_dd_def; candle_poly_dd_list_def;
              candle_poly_d_list_def; candle_poly_value_list_def;
              candle_fs_hist_delta_hessian_component_real_def;
              candle_fs_hist_delta_hessian_real_def;
              LET_DEF; LET_END_DEF; ITLIST] THEN
  CONV_TAC (DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; list_of_seq; APPEND;
              candle_q_real_lookup_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING);;

let candle_case10173_hist_four_x0_dd = prove
 (`!values rowindex colindex.
     candle_analytic_dd rowindex colindex (list_of_seq values 6)
       candle_case10173_hist_four_x0_expr =
     candle_fs_hist_four_x0_hessian_real rowindex colindex`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_case10173_hist_four_x0_expr_def;
              candle_case10173_hist_four_x0_poly_def;
              candle_analytic_dd_def; candle_poly_dd_list_def;
              candle_poly_d_list_def; candle_poly_value_list_def;
              candle_fs_hist_four_x0_hessian_real_def;
              REAL_MUL_LZERO; REAL_MUL_RZERO;
              REAL_ADD_LID; REAL_ADD_RID]);;

end;;
