(* ========================================================================== *)
(* Case-10173 historical inputs against the authenticated analytic jets.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_source_polynomials_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_source_jet_sound = struct

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_composition_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_reference_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_optimized_analytic_bridge_sound;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_sqrt_factorization_sound;;
open Candle_cv_analytic_expr_case10173_historical_source_polynomials_sound;;

let candle_case10173_hist_source_numerator_expr_def = new_definition
 `candle_case10173_hist_source_numerator_expr =
    Candle_analytic_poly
      (Candle_poly_neg candle_case10173_hist_delta_x4_poly)`;;

(* The authenticated source associates [4 * (x0 * delta)], whereas the
   historical checker supplies the two factors [4*x0] and [delta].  This is
   a full formal-jet identity for arbitrary environments. *)

let candle_case10173_hist_source_radical_real_jet = prove
 (`!env.
     candle_hist_analytic_real_jet env
       candle_case10173_hist_source_radical_expr =
     candle_hist_analytic_real_jet env
       (Candle_analytic_mul
         candle_case10173_hist_four_x0_expr
         candle_case10173_hist_delta_expr)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def; PAIR_EQ; FUN_EQ_THM;
              candle_case10173_hist_source_radical_expr_def;
              candle_case10173_hist_source_radical_poly_def;
              candle_case10173_hist_four_x0_expr_def;
              candle_case10173_hist_four_x0_poly_def;
              candle_case10173_hist_delta_expr_def;
              candle_analytic_value_def; candle_analytic_d_def;
              candle_analytic_dd_def; candle_poly_value_list_def;
              candle_poly_d_list_def; candle_poly_dd_list_def] THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO;
              REAL_ADD_LID; REAL_ADD_RID; REAL_NEG_0;
              REAL_ADD_LDISTRIB; REAL_MUL_AC; REAL_ADD_AC]);;

let candle_case10173_hist_source_numerator_real_jet = prove
 (`!env.
     candle_hist_analytic_real_jet env
       candle_case10173_hist_source_numerator_expr =
     candle_hist_analytic_real_jet env
       (Candle_analytic_neg candle_case10173_hist_delta_x4_expr)`,
  GEN_TAC THEN
  REWRITE_TAC[candle_hist_analytic_real_jet_def;
              candle_hist_real_jet_make_def; PAIR_EQ; FUN_EQ_THM;
              candle_case10173_hist_source_numerator_expr_def;
              candle_case10173_hist_delta_x4_expr_def;
              candle_analytic_value_def; candle_analytic_d_def;
              candle_analytic_dd_def; candle_poly_value_list_def;
              candle_poly_d_list_def; candle_poly_dd_list_def]);;

let candle_case10173_hist_delta_x4_jet_value = prove
 (`!values.
     candle_hist_real_jet_value
       (candle_fs_hist_delta_x4_real_jet values) =
     candle_analytic_value (list_of_seq values 6)
       candle_case10173_hist_delta_x4_expr`,
  REWRITE_TAC[candle_fs_hist_delta_x4_real_jet_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_make_def; FST;
              candle_case10173_hist_delta_x4_value]);;

let candle_case10173_hist_delta_x4_jet_d = prove
 (`!values coordinate.
     coordinate < 6
     ==> candle_hist_real_jet_gradient
           (candle_fs_hist_delta_x4_real_jet values) coordinate =
         candle_analytic_d coordinate (list_of_seq values 6)
           candle_case10173_hist_delta_x4_expr`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_real_jet_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_make_def; FST; SND] THEN
  ASM_SIMP_TAC[candle_case10173_hist_delta_x4_d]);;

let candle_case10173_hist_delta_x4_jet_dd = prove
 (`!values rowindex colindex.
     rowindex < 6 /\ colindex < 6
     ==> candle_hist_real_jet_hessian
           (candle_fs_hist_delta_x4_real_jet values) rowindex colindex =
         candle_analytic_dd rowindex colindex (list_of_seq values 6)
           candle_case10173_hist_delta_x4_expr`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_delta_x4_real_jet_def;
              candle_hist_real_jet_hessian_def;
              candle_hist_real_jet_make_def; FST; SND] THEN
  ASM_SIMP_TAC[candle_case10173_hist_delta_x4_dd]);;

let candle_case10173_hist_root_delta_jet_value = prove
 (`!values.
     candle_hist_real_jet_value
       (candle_fs_hist_root_delta_real_jet values) =
     candle_analytic_value (list_of_seq values 6)
       (candle_hist_analytic_sqrt candle_case10173_hist_delta_expr)`,
  REWRITE_TAC[candle_fs_hist_root_delta_real_jet_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_make_def; FST;
              candle_hist_analytic_sqrt_def;
              candle_analytic_value_def;
              candle_case10173_hist_delta_value]);;

let candle_case10173_hist_root_delta_jet_d = prove
 (`!values coordinate.
     coordinate < 6
     ==> candle_hist_real_jet_gradient
           (candle_fs_hist_root_delta_real_jet values) coordinate =
         candle_analytic_d coordinate (list_of_seq values 6)
           (candle_hist_analytic_sqrt
             candle_case10173_hist_delta_expr)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_root_delta_real_jet_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_make_def; FST; SND;
              candle_hist_analytic_sqrt_def;
              candle_analytic_value_def; candle_analytic_d_def] THEN
  ASM_SIMP_TAC[candle_case10173_hist_delta_value;
               candle_case10173_hist_delta_d]);;

let candle_case10173_hist_root_delta_jet_dd = prove
 (`!values rowindex colindex.
     rowindex < 6 /\ colindex < 6
     ==> candle_hist_real_jet_hessian
           (candle_fs_hist_root_delta_real_jet values) rowindex colindex =
         candle_analytic_dd rowindex colindex (list_of_seq values 6)
           (candle_hist_analytic_sqrt
             candle_case10173_hist_delta_expr)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_root_delta_real_jet_def;
              candle_hist_real_jet_hessian_def;
              candle_hist_real_jet_make_def; FST; SND;
              candle_hist_analytic_sqrt_def;
              candle_analytic_value_def; candle_analytic_d_def;
              candle_analytic_dd_def] THEN
  ASM_SIMP_TAC[candle_case10173_hist_delta_value;
               candle_case10173_hist_delta_d;
               candle_case10173_hist_delta_dd]);;

let candle_case10173_hist_root_four_x0_jet_value = prove
 (`!values.
     candle_hist_real_jet_value
       (candle_fs_hist_root_four_x0_real_jet values) =
     candle_analytic_value (list_of_seq values 6)
       (candle_hist_analytic_sqrt candle_case10173_hist_four_x0_expr)`,
  REWRITE_TAC[candle_fs_hist_root_four_x0_real_jet_def;
              candle_hist_real_jet_value_def;
              candle_hist_real_jet_make_def; FST;
              candle_hist_analytic_sqrt_def;
              candle_analytic_value_def;
              candle_case10173_hist_four_x0_value]);;

let candle_case10173_hist_root_four_x0_jet_d = prove
 (`!values coordinate.
     coordinate < 6
     ==> candle_hist_real_jet_gradient
           (candle_fs_hist_root_four_x0_real_jet values) coordinate =
         candle_analytic_d coordinate (list_of_seq values 6)
           (candle_hist_analytic_sqrt
             candle_case10173_hist_four_x0_expr)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_root_four_x0_real_jet_def;
              candle_hist_real_jet_gradient_def;
              candle_hist_real_jet_make_def; FST; SND;
              candle_hist_analytic_sqrt_def;
              candle_analytic_value_def; candle_analytic_d_def] THEN
  ASM_SIMP_TAC[candle_case10173_hist_four_x0_value;
               candle_case10173_hist_four_x0_d]);;

let candle_case10173_hist_root_four_x0_jet_dd = prove
 (`!values rowindex colindex.
     rowindex < 6 /\ colindex < 6
     ==> candle_hist_real_jet_hessian
           (candle_fs_hist_root_four_x0_real_jet values) rowindex colindex =
         candle_analytic_dd rowindex colindex (list_of_seq values 6)
           (candle_hist_analytic_sqrt
             candle_case10173_hist_four_x0_expr)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_fs_hist_root_four_x0_real_jet_def;
              candle_hist_real_jet_hessian_def;
              candle_hist_real_jet_make_def; FST; SND;
              candle_hist_analytic_sqrt_def;
              candle_analytic_value_def; candle_analytic_d_def;
              candle_analytic_dd_def] THEN
  ASM_SIMP_TAC[candle_case10173_hist_four_x0_value;
               candle_case10173_hist_four_x0_d;
               candle_case10173_hist_four_x0_dd]);;

end;;
