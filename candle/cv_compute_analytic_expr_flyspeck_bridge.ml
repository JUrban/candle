(* ========================================================================== *)
(* Flyspeck gradient/Hessian views of reflected analytic jets.               *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The jet keeps zero-based analytic derivative  *)
(* data.  These theorems expose exactly the one-based partial/partial2 lists  *)
(* consumed by Flyspeck's Taylor machinery, without expression-specific      *)
(* symbolic differentiation.                                                  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_domain.ml";;
needs "candle/cv_compute_polynomial_expr_dim_jet_sound.ml";;

module Candle_cv_analytic_expr_flyspeck_bridge = struct

open Multivariate_taylor;;
open Taylor_interval;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_sound;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_partials;;
open Candle_cv_analytic_expr_hessian;;
open Candle_cv_analytic_expr_domain;;

let candle_q_dim_analytic_jet_gradient_flyspeck_contains = prove
 (`!e jet (z:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e /\
     candle_q_dim_jet_shape (dimindex (:N)) jet /\
     candle_q_dim_analytic_contains (dimindex (:N)) jet
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e
     ==>
     candle_q_stack_contains
       (candle_q_dim_jet_gradient jet)
       (list_of_seq
         (\di. partial (di + 1) (candle_analytic_denote_dim e) z)
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_stack_contains_all2] THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_gradient jet =
    list_of_seq (\i. candle_q_dim_jet_gradient_at jet i)
      (dimindex (:N))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_dim_jet_gradient_list_of_seq THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_all2_list_of_seq] THEN
  X_GEN_TAC `di:num` THEN DISCH_TAC THEN
  MP_TAC
    (SPECL [`e:candle_analytic_expr`; `z:real^N`; `di + 1`]
      candle_analytic_denote_dim_partial) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC[th])] THEN
  REWRITE_TAC[ARITH_RULE `(di + 1) - 1 = di`] THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_dim_analytic_contains_def;
                  candle_q_dim_jet_contains_components_def]) THEN
  ASM_SIMP_TAC[]);;

let candle_q_dim_analytic_jet_hessian_flyspeck_contains = prove
 (`!e jet (z:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e /\
     candle_q_dim_jet_shape (dimindex (:N)) jet /\
     candle_q_dim_analytic_contains (dimindex (:N)) jet
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e
     ==>
     ALL2 candle_q_stack_contains
       (candle_q_dim_jet_hessian jet)
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_analytic_denote_dim e) z)
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_q_dim_jet_hessian jet =
    list_of_seq
      (\i. list_of_seq
        (\j. candle_q_dim_jet_hessian_at jet i j) (dimindex (:N)))
      (dimindex (:N))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_q_dim_jet_hessian_list_of_seq THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[candle_all2_list_of_seq] THEN
  X_GEN_TAC `di:num` THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_stack_contains_all2;
              candle_all2_list_of_seq] THEN
  X_GEN_TAC `dj:num` THEN DISCH_TAC THEN
  MP_TAC
    (SPECL
      [`e:candle_analytic_expr`; `z:real^N`; `di + 1`; `dj + 1`]
      candle_analytic_denote_dim_second_partial) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC[th])] THEN
  REWRITE_TAC[ARITH_RULE `(di + 1) - 1 = di`;
              ARITH_RULE `(dj + 1) - 1 = dj`] THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_q_dim_analytic_contains_def;
                  candle_q_dim_jet_contains_components_def]) THEN
  ASM_SIMP_TAC[]);;

end;;
