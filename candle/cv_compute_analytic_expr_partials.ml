(* ========================================================================== *)
(* Flyspeck partial-derivative correspondence for analytic expressions.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This layer connects the zero-based gradient   *)
(* data computed by the reflected jet evaluator to Flyspeck's one-based       *)
(* [partial] operator, once for every supported analytic AST.                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_calculus.ml";;

module Candle_cv_analytic_expr_partials = struct

open Multivariate_taylor;;
open Taylor_interval;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_flyspeck_dim_bridge;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;

let candle_analytic_denote_dim_partial = prove
 (`!e (z:real^N) i.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e /\
     i IN 1..dimindex (:N)
     ==>
     partial i (candle_analytic_denote_dim e) z =
       candle_analytic_d (i - 1)
         (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `p:candle_poly_expr` THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    MP_TAC
     (SPECL [`p:candle_poly_expr`; `z:real^N`; `i:num`; `i:num`]
       candle_poly_denote_dim_partials) THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_poly;
                 candle_analytic_d_def; candle_poly_d_list_fun];
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "ih" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (ASSUME `i IN 1..dimindex (:N)`))))) THEN
    ASSUME_TAC
     (MATCH_MP
       (SPECL [`a:candle_analytic_expr`; `z:real^N`]
         candle_analytic_denote_dim_diff2c)
       (CONJ
         (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
         (ASSUME
           `candle_analytic_regular_at
             (list_of_seq (\k. (z:real^N)$(k + 1))
               (dimindex (:N))) a`))) THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_analytic_denote_dim a):real^N->real)
           (z:real^N)`)) THEN
    MP_TAC
     (SPECL
       [`i:num`; `(candle_analytic_denote_dim a):real^N->real`; `z:real^N`]
       partial_neg) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_neg; candle_analytic_d_def;
                 partial_neg];
    MAP_EVERY X_GEN_TAC [`a:candle_analytic_expr`;
                         `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`z:real^N`; `i:num`] (ASSUME
      `!z:real^N. !i.
        candle_analytic_valid_dim (dimindex (:N)) a /\
        candle_analytic_regular_at
          (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) a /\
        i IN 1..dimindex (:N)
        ==> partial i (candle_analytic_denote_dim a) z =
            candle_analytic_d (i - 1)
              (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) a`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC (SPECL [`z:real^N`; `i:num`] (ASSUME
      `!z:real^N. !i.
        candle_analytic_valid_dim (dimindex (:N)) b /\
        candle_analytic_regular_at
          (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) b /\
        i IN 1..dimindex (:N)
        ==> partial i (candle_analytic_denote_dim b) z =
            candle_analytic_d (i - 1)
              (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) b`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC
     (SPECL [`a:candle_analytic_expr`; `z:real^N`]
       candle_analytic_denote_dim_diff2c) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL [`b:candle_analytic_expr`; `z:real^N`]
       candle_analytic_denote_dim_diff2c) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_analytic_denote_dim a):real^N->real)
           (z:real^N)`)) THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_analytic_denote_dim b):real^N->real)
           (z:real^N)`)) THEN
    MP_TAC
     (SPECL
       [`(candle_analytic_denote_dim a):real^N->real`; `i:num`;
        `(candle_analytic_denote_dim b):real^N->real`; `z:real^N`]
       partial_add) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_add; candle_analytic_d_def;
                 partial_add];
    MAP_EVERY X_GEN_TAC [`a:candle_analytic_expr`;
                         `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "iha" (fun iha ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`] iha)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (ASSUME `i IN 1..dimindex (:N)`))))) THEN
    USE_THEN "ihb" (fun ihb ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`] ihb)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) b`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) b`)
             (ASSUME `i IN 1..dimindex (:N)`))))) THEN
    ASSUME_TAC
     (MATCH_MP
       (SPECL [`a:candle_analytic_expr`; `z:real^N`]
         candle_analytic_denote_dim_diff2c)
       (CONJ
         (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
         (ASSUME
           `candle_analytic_regular_at
             (list_of_seq (\k. (z:real^N)$(k + 1))
               (dimindex (:N))) a`))) THEN
    ASSUME_TAC
     (MATCH_MP
       (SPECL [`b:candle_analytic_expr`; `z:real^N`]
         candle_analytic_denote_dim_diff2c)
       (CONJ
         (ASSUME `candle_analytic_valid_dim (dimindex (:N)) b`)
         (ASSUME
           `candle_analytic_regular_at
             (list_of_seq (\k. (z:real^N)$(k + 1))
               (dimindex (:N))) b`))) THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_analytic_denote_dim a):real^N->real)
           (z:real^N)`)) THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_analytic_denote_dim b):real^N->real)
           (z:real^N)`)) THEN
    MP_TAC
     (SPECL
       [`(candle_analytic_denote_dim a):real^N->real`; `i:num`;
        `(candle_analytic_denote_dim b):real^N->real`; `z:real^N`]
       partial_mul) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_mul; candle_analytic_d_def;
                 partial_mul] THEN
    REWRITE_TAC[candle_analytic_denote_dim_def];
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "ih" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (ASSUME `i IN 1..dimindex (:N)`))))) THEN
    ASSUME_TAC
     (MATCH_MP
       (SPECL [`a:candle_analytic_expr`; `z:real^N`]
         candle_analytic_denote_dim_diff2c)
       (CONJ
         (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
         (ASSUME
           `candle_analytic_regular_at
             (list_of_seq (\k. (z:real^N)$(k + 1))
               (dimindex (:N))) a`))) THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_analytic_denote_dim a):real^N->real)
           (z:real^N)`)) THEN
    MP_TAC
     (SPECL
       [`(candle_analytic_denote_dim a):real^N->real`; `i:num`;
        `(candle_analytic_denote_dim a):real^N->real`; `z:real^N`]
       partial_mul) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_square; candle_analytic_d_def;
                 partial_mul] THEN
    REWRITE_TAC[candle_analytic_denote_dim_def];
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "ih" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (ASSUME `i IN 1..dimindex (:N)`))))) THEN
    ASSUME_TAC
     (MATCH_MP
       (SPECL [`a:candle_analytic_expr`; `z:real^N`]
         candle_analytic_denote_dim_diff2c)
       (CONJ
         (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
         (ASSUME
           `candle_analytic_regular_at
             (list_of_seq (\k. (z:real^N)$(k + 1))
               (dimindex (:N))) a`))) THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_analytic_denote_dim a):real^N->real)
           (z:real^N)`)) THEN
    SUBGOAL_THEN
      `~(candle_analytic_denote_dim a (z:real^N) = &0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[candle_analytic_denote_dim_def];
      ALL_TAC] THEN
    MP_TAC
     (SPECL
       [`i:num`; `(candle_analytic_denote_dim a):real^N->real`; `z:real^N`]
       partial_uni_compose) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `inv`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_DIFFERENTIABLE_AT_INV THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_DEF] THEN DISCH_TAC] THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_inv; candle_analytic_d_def;
                 derivative_inv; REAL_INV_MUL] THEN
    REWRITE_TAC[candle_analytic_denote_dim_def];
    MAP_EVERY X_GEN_TAC
      [`lp:num`; `ln:num`; `ld:num`; `up:num`; `un:num`; `ud:num`;
       `a:candle_analytic_expr`] THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "ih" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (ASSUME `i IN 1..dimindex (:N)`))))) THEN
    ASSUME_TAC
     (MATCH_MP
       (SPECL [`a:candle_analytic_expr`; `z:real^N`]
         candle_analytic_denote_dim_diff2c)
       (CONJ
         (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
         (ASSUME
           `candle_analytic_regular_at
             (list_of_seq (\k. (z:real^N)$(k + 1))
               (dimindex (:N))) a`))) THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_analytic_denote_dim a):real^N->real)
           (z:real^N)`)) THEN
    SUBGOAL_THEN
      `&0 < candle_analytic_denote_dim a (z:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[candle_analytic_denote_dim_def];
      ALL_TAC] THEN
    MP_TAC
     (SPECL
       [`i:num`; `(candle_analytic_denote_dim a):real^N->real`; `z:real^N`]
       partial_uni_compose) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `sqrt`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_DIFFERENTIABLE_AT_SQRT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_DEF] THEN DISCH_TAC] THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_sqrt; candle_analytic_d_def;
                 derivative_sqrt;
                 REAL_ARITH `&2 * x = x + x`] THEN
    REWRITE_TAC[candle_analytic_denote_dim_def];
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "ih" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (ASSUME `i IN 1..dimindex (:N)`))))) THEN
    ASSUME_TAC
     (MATCH_MP
       (SPECL [`a:candle_analytic_expr`; `z:real^N`]
         candle_analytic_denote_dim_diff2c)
       (CONJ
         (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
         (ASSUME
           `candle_analytic_regular_at
             (list_of_seq (\k. (z:real^N)$(k + 1))
               (dimindex (:N))) a`))) THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_analytic_denote_dim a):real^N->real)
           (z:real^N)`)) THEN
    MP_TAC
     (SPECL
       [`i:num`; `(candle_analytic_denote_dim a):real^N->real`; `z:real^N`]
       partial_uni_compose) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `atn`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_DIFFERENTIABLE_AT_ATN];
      REWRITE_TAC[o_DEF] THEN DISCH_TAC] THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_atn; candle_analytic_d_def;
                 derivative_atn] THEN
    REWRITE_TAC[candle_analytic_denote_dim_def];
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def;
                candle_analytic_denote_dim_pi_half;
                candle_analytic_d_def; partial_const]]);;

end;;
