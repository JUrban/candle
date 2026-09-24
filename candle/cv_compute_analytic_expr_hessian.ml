(* ========================================================================== *)
(* Flyspeck second-partial correspondence for analytic expressions.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This layer identifies every component of the  *)
(* reflected analytic Hessian with Flyspeck's one-based [partial2] operator.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_partials.ml";;

module Candle_cv_analytic_expr_hessian = struct

open Multivariate_taylor;;
open Taylor_interval;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_flyspeck_dim_bridge;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_partials;;

let candle_analytic_denote_dim_second_partial = prove
 (`!e (z:real^N) i j.
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e /\
     i IN 1..dimindex (:N) /\
     j IN 1..dimindex (:N)
     ==>
     partial2 j i (candle_analytic_denote_dim e) z =
       candle_analytic_dd (i - 1) (j - 1)
         (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `p:candle_poly_expr` THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    MP_TAC
     (SPECL [`p:candle_poly_expr`; `z:real^N`; `i:num`; `j:num`]
       candle_poly_denote_dim_partials) THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_poly;
                 candle_analytic_dd_def; candle_poly_dd_list_fun];
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "ih" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`; `j:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (CONJ
               (ASSUME `i IN 1..dimindex (:N)`)
               (ASSUME `j IN 1..dimindex (:N)`)))))) THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (MATCH_MP
         (SPECL [`a:candle_analytic_expr`; `z:real^N`]
           candle_analytic_denote_dim_diff2c)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (ASSUME
             `candle_analytic_regular_at
               (list_of_seq (\k. (z:real^N)$(k + 1))
                 (dimindex (:N))) a`)))) THEN
    MP_TAC
     (SPECL
       [`z:real^N`; `j:num`; `i:num`;
        `(candle_analytic_denote_dim a):real^N->real`]
       second_partial_neg) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_neg; candle_analytic_dd_def;
                 second_partial_neg];
    MAP_EVERY X_GEN_TAC [`a:candle_analytic_expr`;
                         `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "iha" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`; `j:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (CONJ
               (ASSUME `i IN 1..dimindex (:N)`)
               (ASSUME `j IN 1..dimindex (:N)`)))))) THEN
    USE_THEN "ihb" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`; `j:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) b`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) b`)
             (CONJ
               (ASSUME `i IN 1..dimindex (:N)`)
               (ASSUME `j IN 1..dimindex (:N)`)))))) THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (MATCH_MP
         (SPECL [`a:candle_analytic_expr`; `z:real^N`]
           candle_analytic_denote_dim_diff2c)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (ASSUME
             `candle_analytic_regular_at
               (list_of_seq (\k. (z:real^N)$(k + 1))
                 (dimindex (:N))) a`)))) THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (MATCH_MP
         (SPECL [`b:candle_analytic_expr`; `z:real^N`]
           candle_analytic_denote_dim_diff2c)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) b`)
           (ASSUME
             `candle_analytic_regular_at
               (list_of_seq (\k. (z:real^N)$(k + 1))
                 (dimindex (:N))) b`)))) THEN
    MP_TAC
     (SPECL
       [`z:real^N`; `j:num`; `i:num`;
        `(candle_analytic_denote_dim a):real^N->real`;
        `(candle_analytic_denote_dim b):real^N->real`]
       second_partial_add) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_add; candle_analytic_dd_def;
                 second_partial_add];
    MAP_EVERY X_GEN_TAC [`a:candle_analytic_expr`;
                         `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "iha" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`; `j:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (CONJ
               (ASSUME `i IN 1..dimindex (:N)`)
               (ASSUME `j IN 1..dimindex (:N)`)))))) THEN
    USE_THEN "ihb" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`; `j:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) b`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) b`)
             (CONJ
               (ASSUME `i IN 1..dimindex (:N)`)
               (ASSUME `j IN 1..dimindex (:N)`)))))) THEN
    MP_TAC
     (SPECL [`a:candle_analytic_expr`; `z:real^N`; `i:num`]
       candle_analytic_denote_dim_partial) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL [`a:candle_analytic_expr`; `z:real^N`; `j:num`]
       candle_analytic_denote_dim_partial) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL [`b:candle_analytic_expr`; `z:real^N`; `i:num`]
       candle_analytic_denote_dim_partial) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL [`b:candle_analytic_expr`; `z:real^N`; `j:num`]
       candle_analytic_denote_dim_partial) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (MATCH_MP
         (SPECL [`a:candle_analytic_expr`; `z:real^N`]
           candle_analytic_denote_dim_diff2c)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (ASSUME
             `candle_analytic_regular_at
               (list_of_seq (\k. (z:real^N)$(k + 1))
                 (dimindex (:N))) a`)))) THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (MATCH_MP
         (SPECL [`b:candle_analytic_expr`; `z:real^N`]
           candle_analytic_denote_dim_diff2c)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) b`)
           (ASSUME
             `candle_analytic_regular_at
               (list_of_seq (\k. (z:real^N)$(k + 1))
                 (dimindex (:N))) b`)))) THEN
    MP_TAC
     (SPECL
       [`z:real^N`; `j:num`; `i:num`;
        `(candle_analytic_denote_dim a):real^N->real`;
        `(candle_analytic_denote_dim b):real^N->real`]
       second_partial_mul) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_mul; candle_analytic_dd_def;
                 second_partial_mul] THEN
    REWRITE_TAC[candle_analytic_denote_dim_def] THEN
    MESON_TAC[REAL_MUL_SYM];
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "ih" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`; `j:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (CONJ
               (ASSUME `i IN 1..dimindex (:N)`)
               (ASSUME `j IN 1..dimindex (:N)`)))))) THEN
    MP_TAC
     (SPECL [`a:candle_analytic_expr`; `z:real^N`; `i:num`]
       candle_analytic_denote_dim_partial) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL [`a:candle_analytic_expr`; `z:real^N`; `j:num`]
       candle_analytic_denote_dim_partial) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (MATCH_MP
         (SPECL [`a:candle_analytic_expr`; `z:real^N`]
           candle_analytic_denote_dim_diff2c)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (ASSUME
             `candle_analytic_regular_at
               (list_of_seq (\k. (z:real^N)$(k + 1))
                 (dimindex (:N))) a`)))) THEN
    MP_TAC
     (SPECL
       [`z:real^N`; `j:num`; `i:num`;
        `(candle_analytic_denote_dim a):real^N->real`;
        `(candle_analytic_denote_dim a):real^N->real`]
       second_partial_mul) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_square; candle_analytic_dd_def;
                 second_partial_mul] THEN
    REWRITE_TAC[candle_analytic_denote_dim_def] THEN
    MESON_TAC[REAL_MUL_SYM];
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "ih" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`; `j:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (CONJ
               (ASSUME `i IN 1..dimindex (:N)`)
               (ASSUME `j IN 1..dimindex (:N)`)))))) THEN
    MP_TAC
     (SPECL [`a:candle_analytic_expr`; `z:real^N`; `i:num`]
       candle_analytic_denote_dim_partial) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL [`a:candle_analytic_expr`; `z:real^N`; `j:num`]
       candle_analytic_denote_dim_partial) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (MATCH_MP
         (SPECL [`a:candle_analytic_expr`; `z:real^N`]
           candle_analytic_denote_dim_diff2c)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (ASSUME
             `candle_analytic_regular_at
               (list_of_seq (\k. (z:real^N)$(k + 1))
                 (dimindex (:N))) a`)))) THEN
    SUBGOAL_THEN
      `~(candle_analytic_denote_dim a (z:real^N) = &0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[candle_analytic_denote_dim_def];
      ALL_TAC] THEN
    MP_TAC
     (SPECL
       [`z:real^N`; `j:num`; `i:num`;
        `(candle_analytic_denote_dim a):real^N->real`]
       second_partial_uni_compose) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `inv`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC diff2_inv THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_DEF] THEN DISCH_TAC] THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_inv; candle_analytic_dd_def;
                 second_derivative_inv; derivative_inv; REAL_INV_POW;
                 REAL_INV_MUL; real_pow] THEN
    REWRITE_TAC[candle_analytic_denote_dim_def] THEN
    CONV_TAC REAL_RING;
    MAP_EVERY X_GEN_TAC
      [`lp:num`; `ln:num`; `ld:num`; `up:num`; `un:num`; `ud:num`;
       `a:candle_analytic_expr`] THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "ih" (fun ih ->
      ASSUME_TAC
       (MATCH_MP (SPECL [`z:real^N`; `i:num`; `j:num`] ih)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (CONJ
             (ASSUME
               `candle_analytic_regular_at
                 (list_of_seq (\k. (z:real^N)$(k + 1))
                   (dimindex (:N))) a`)
             (CONJ
               (ASSUME `i IN 1..dimindex (:N)`)
               (ASSUME `j IN 1..dimindex (:N)`)))))) THEN
    MP_TAC
     (SPECL [`a:candle_analytic_expr`; `z:real^N`; `i:num`]
       candle_analytic_denote_dim_partial) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL [`a:candle_analytic_expr`; `z:real^N`; `j:num`]
       candle_analytic_denote_dim_partial) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (MATCH_MP
         (SPECL [`a:candle_analytic_expr`; `z:real^N`]
           candle_analytic_denote_dim_diff2c)
         (CONJ
           (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
           (ASSUME
             `candle_analytic_regular_at
               (list_of_seq (\k. (z:real^N)$(k + 1))
                 (dimindex (:N))) a`)))) THEN
    SUBGOAL_THEN
      `&0 < candle_analytic_denote_dim a (z:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[candle_analytic_denote_dim_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `sqrt (candle_analytic_denote_dim a (z:real^N) pow 3) =
       sqrt (candle_analytic_denote_dim a (z:real^N)) *
       candle_analytic_denote_dim a (z:real^N)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM SQRT_POW; ARITH_RULE `3 = SUC 2`; real_powS;
                   SQRT_POW_2; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC
     (SPECL
       [`z:real^N`; `j:num`; `i:num`;
        `(candle_analytic_denote_dim a):real^N->real`]
       second_partial_uni_compose) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `sqrt`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC diff2_sqrt THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_DEF] THEN DISCH_TAC] THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_sqrt; candle_analytic_dd_def;
                 second_derivative_sqrt; derivative_sqrt;
                 REAL_ARITH `&2 * x = x + x`;
                 REAL_ARITH `&4 * (s * x) = (s + s) * (x + x)`] THEN
    REWRITE_TAC[candle_analytic_denote_dim_def] THEN
    MATCH_MP_TAC (REAL_ARITH `(x:real) = y ==> x + z = y + z`) THEN
    MESON_TAC[REAL_MUL_ASSOC; REAL_MUL_SYM]]);;

end;;
