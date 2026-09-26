(* ========================================================================== *)
(* Analytic-invariant bridge for fixed-scale polynomial Taylor blocks.       *)
(*                                                                            *)
(* The fixed evaluator already proves value, gradient, and Hessian           *)
(* containment for every valid compiled polynomial.  This file identifies   *)
(* those generic partials with the analytic-expression semantics, so the     *)
(* result can be consumed by the existing universal Taylor-model invariant.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_invariant.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_compile_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_sound = struct

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_flyspeck_dim_bridge;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;

let candle_poly_value_list_denote_at_dim = prove
 (`!e (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e
     ==>
     candle_poly_value_list
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e =
     candle_poly_denote_dim e z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_poly_denote_dim_def] THEN
  ASM_SIMP_TAC[candle_poly_value_list_fun]);;

let candle_poly_d_list_partial_at_dim = prove
 (`!e (z:real^N) di.
     candle_poly_valid_dim (dimindex (:N)) e /\
     di < dimindex (:N)
     ==>
     candle_poly_d_list di
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e =
     partial (di + 1) (candle_poly_denote_dim e) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[candle_poly_d_list_fun] THEN
  MP_TAC
    (ISPECL
      [`e:candle_poly_expr`; `z:real^N`; `di + 1`; `di + 1`]
      candle_poly_denote_dim_partials) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `(di + 1) - 1 = di`] THEN MESON_TAC[]]);;

let candle_poly_dd_list_partial2_at_dim = prove
 (`!e (z:real^N) di dj.
     candle_poly_valid_dim (dimindex (:N)) e /\
     di < dimindex (:N) /\
     dj < dimindex (:N)
     ==>
     candle_poly_dd_list dj di
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e =
     partial2 (dj + 1) (di + 1) (candle_poly_denote_dim e) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[candle_poly_dd_list_fun] THEN
  MP_TAC
    (ISPECL
      [`e:candle_poly_expr`; `z:real^N`; `di + 1`; `dj + 1`]
      candle_poly_denote_dim_partials) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `(di + 1) - 1 = di`;
                ARITH_RULE `(dj + 1) - 1 = dj`] THEN MESON_TAC[]]);;

let candle_q_dim_poly_analytic_contains_partials = prove
 (`!e jet (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e
     ==>
     (candle_q_dim_analytic_contains (dimindex (:N)) jet
        (list_of_seq (\k. z$(k + 1)) (dimindex (:N)))
        (Candle_analytic_poly e) <=>
      candle_q_dim_jet_contains_components (dimindex (:N)) jet
        (candle_poly_denote_dim e z)
        (\di. partial (di + 1) (candle_poly_denote_dim e) z)
        (\di dj. partial2 (dj + 1) (di + 1)
          (candle_poly_denote_dim e) z))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def;
              candle_q_dim_jet_contains_components_def] THEN
  ASM_SIMP_TAC[candle_poly_value_list_denote_at_dim;
               candle_poly_d_list_partial_at_dim;
               candle_poly_dd_list_partial2_at_dim]);;

let candle_fs_result_to_q_domain = prove
 (`!result.
     candle_q_dim_taylor_model_result_domain
       (candle_fs_result_to_q result) =
     candle_fs_result_domain result`,
  REWRITE_TAC[candle_fs_result_to_q_def;
              candle_q_dim_taylor_model_result_domain_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND]);;

let candle_fs_poly_program_to_q_analytic_invariant = prove
 (`!e boxes (type_witness:real^N).
     candle_poly_valid_dim (dimindex (:N)) e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_fs_poly_program_to_q
         (candle_q_center_environment_list boxes)
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_poly_compile e))
       (Candle_analytic_poly e) (Candle_analytic_poly e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_result_poly_invariant (type_witness:real^N) boxes
      (candle_fs_poly_program_fixed
        (candle_fs_interval_list_of_q
          (candle_q_center_environment_list boxes))
        (candle_fs_list_of_q
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes)))
        (candle_poly_compile e)) e`
   (LABEL_TAC "fixed_invariant") THENL
   [MATCH_MP_TAC candle_fs_poly_compile_poly_invariant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_q_dim_taylor_model_result_analytic_invariant_def;
              candle_fs_poly_program_to_q_def;
              candle_fs_poly_program_def;
              candle_fs_result_to_q_domain] THEN
  DISCH_TAC THEN
  USE_THEN "fixed_invariant" MP_TAC THEN
  REWRITE_TAC[candle_fs_result_poly_invariant_def] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "center_shape")
      (CONJUNCTS_THEN2 (LABEL_TAC "center_contains")
        (CONJUNCTS_THEN2 (LABEL_TAC "proxy_shape")
          (LABEL_TAC "proxy_contains")))) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_analytic_regular_at_def];
    REWRITE_TAC[candle_analytic_regular_at_def];
    USE_THEN "center_shape" ACCEPT_TAC;
    ASM_SIMP_TAC[candle_q_dim_poly_analytic_contains_partials] THEN
    USE_THEN "center_contains" ACCEPT_TAC;
    USE_THEN "proxy_shape" ACCEPT_TAC;
    X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_q_dim_poly_analytic_contains_partials] THEN
    USE_THEN "proxy_contains" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

end;;
