(* ========================================================================== *)
(* Analytic invariant lift for reflected signed fixed-scale Taylor models.   *)
(*                                                                            *)
(* The numerical backend computes only fixed-scale data.  This file connects *)
(* its completed result to the dimension-generic analytic interface, outside *)
(* the hot computation path.                                                  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_complete_sound.ml";;

module Candle_cv_analytic_expr_fixed_scale_invariant = struct

open Candle_cv_analytic_expr_taylor_model_representation;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_complete_sound;;

let candle_fs_gradient_bounds_map2 = prove
 (`!radii gradients rows.
     LENGTH gradients = LENGTH rows
     ==>
     candle_fs_gradient_bounds radii gradients rows =
     MAP2
       (\gradient_interval interval_row.
          candle_fs_gradient_bound radii gradient_interval interval_row)
       gradients rows`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; candle_fs_gradient_bounds_def; MAP2_DEF] THEN
    ARITH_TAC;
    LIST_INDUCT_TAC THENL
     [REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[LENGTH; candle_fs_gradient_bounds_def;
                  candle_fs_gradient_bound_def;
                  candle_fs_gradient_bound_raw_def;
                  MAP2_DEF; CONS_11] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[HD; TL; SUC_INJ] THEN
      ONCE_REWRITE_TAC[GSYM candle_fs_gradient_bound_raw_def] THEN
      ONCE_REWRITE_TAC[GSYM candle_fs_gradient_bound_def] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let candle_fs_gradient_bounds_el = prove
 (`!radii gradients rows i.
     LENGTH gradients = LENGTH rows /\ i < LENGTH gradients
     ==>
     EL i (candle_fs_gradient_bounds radii gradients rows) =
     candle_fs_gradient_bound radii (EL i gradients) (EL i rows)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_fs_gradient_bounds_map2] THEN
  MATCH_MP_TAC EL_MAP2 THEN ASM_ARITH_TAC);;

let candle_fs_result_complete_domain = prove
 (`!radii (domain:bool) center hessian.
     candle_fs_result_domain
       (candle_fs_result_complete_rounded radii domain center hessian) =
     domain`,
  REWRITE_TAC[candle_fs_result_complete_rounded_def;
              candle_fs_result_domain_def;
              candle_fs_result_make_def; FST; SND]);;

let candle_fs_result_complete_center = prove
 (`!radii (domain:bool) center hessian.
     candle_q_dim_taylor_model_result_center
       (candle_fs_result_to_q
         (candle_fs_result_complete_rounded
           radii domain center hessian)) =
     candle_fs_first_to_q center hessian`,
  REWRITE_TAC[candle_fs_result_to_q_def;
              candle_fs_result_complete_rounded_def;
              candle_q_dim_taylor_model_result_center_def;
              candle_q_dim_taylor_model_result_make_def;
              candle_fs_result_center_def;
              candle_fs_result_hessian_def;
              candle_fs_result_make_def; FST; SND]);;

let candle_fs_result_complete_value_bound = prove
 (`!radii (domain:bool) center hessian.
     candle_fs_result_value_bound
       (candle_fs_result_complete_rounded radii domain center hessian) =
     candle_fs_value_bound radii
       (candle_fs_first_value center)
       (candle_fs_first_gradient center) hessian`,
  REWRITE_TAC[candle_fs_result_value_bound_def;
              candle_fs_result_complete_rounded_def;
              candle_fs_value_bound_def;
              candle_fs_value_bound_raw_def;
              candle_fs_value_error_raw_def;
              candle_fs_result_make_def; FST; SND]);;

let candle_fs_result_complete_gradient_bounds = prove
 (`!radii (domain:bool) center hessian.
     candle_fs_result_gradient_bounds
       (candle_fs_result_complete_rounded radii domain center hessian) =
     candle_fs_gradient_bounds radii
       (candle_fs_first_gradient center) hessian`,
  REWRITE_TAC[candle_fs_result_gradient_bounds_def;
              candle_fs_result_complete_rounded_def;
              candle_fs_result_make_def; FST; SND]);;

let candle_fs_result_complete_hessian = prove
 (`!radii (domain:bool) center hessian.
     candle_fs_result_hessian
       (candle_fs_result_complete_rounded radii domain center hessian) =
     hessian`,
  REWRITE_TAC[candle_fs_result_hessian_def;
              candle_fs_result_complete_rounded_def;
              candle_fs_result_make_def; FST; SND]);;

let candle_fs_result_complete_proxy = prove
 (`!radii (domain:bool) center hessian.
     candle_q_dim_taylor_model_proxy
       (candle_fs_result_to_q
         (candle_fs_result_complete_rounded
           radii domain center hessian)) =
     candle_q_dim_jet_make
       (candle_fs_interval_to_q
         (candle_fs_value_bound radii
           (candle_fs_first_value center)
           (candle_fs_first_gradient center) hessian))
       (candle_fs_interval_list_to_q
         (candle_fs_gradient_bounds radii
           (candle_fs_first_gradient center) hessian))
       (candle_fs_interval_matrix_to_q hessian)`,
  REWRITE_TAC[candle_q_dim_taylor_model_proxy_def;
              candle_fs_result_to_q_def;
              candle_fs_result_complete_value_bound;
              candle_fs_result_complete_gradient_bounds;
              candle_fs_result_complete_hessian;
              candle_q_dim_taylor_model_result_value_bound_def;
              candle_q_dim_taylor_model_result_gradient_bounds_def;
              candle_q_dim_taylor_model_result_hessian_def;
              candle_q_dim_taylor_model_result_make_def; FST; SND]);;

end;;
