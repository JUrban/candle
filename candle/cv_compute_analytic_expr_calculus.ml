(* ========================================================================== *)
(* Universal Flyspeck calculus bridge for reflected analytic expressions.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This layer states the dimension and regularity *)
(* obligations once for the complete AST.  In particular, reciprocal and     *)
(* square-root nodes carry semantic nonzero/positive hypotheses rather than   *)
(* requiring a new calculus proof for each source expression.                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_dim_bridge.ml";;

module Candle_cv_analytic_expr_calculus = struct

open Multivariate_taylor;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_flyspeck_dim_bridge;;
open Candle_cv_analytic_expr_jet;;

let candle_analytic_valid_dim_def = define
 `(candle_analytic_valid_dim n (Candle_analytic_poly p) <=>
     candle_poly_valid_dim n p) /\
  (candle_analytic_valid_dim n (Candle_analytic_neg a) <=>
     candle_analytic_valid_dim n a) /\
  (candle_analytic_valid_dim n (Candle_analytic_add a b) <=>
     candle_analytic_valid_dim n a /\ candle_analytic_valid_dim n b) /\
  (candle_analytic_valid_dim n (Candle_analytic_mul a b) <=>
     candle_analytic_valid_dim n a /\ candle_analytic_valid_dim n b) /\
  (candle_analytic_valid_dim n (Candle_analytic_square a) <=>
     candle_analytic_valid_dim n a) /\
  (candle_analytic_valid_dim n (Candle_analytic_inv a) <=>
     candle_analytic_valid_dim n a) /\
  (candle_analytic_valid_dim n
      (Candle_analytic_sqrt lp ln ld up un ud a) <=>
     candle_analytic_valid_dim n a) /\
  (candle_analytic_valid_dim n (Candle_analytic_atn a) <=>
     candle_analytic_valid_dim n a) /\
  (candle_analytic_valid_dim n Candle_analytic_pi_half <=> T)`;;

let candle_analytic_regular_at_def = define
 `(candle_analytic_regular_at env (Candle_analytic_poly p) <=> T) /\
  (candle_analytic_regular_at env (Candle_analytic_neg a) <=>
     candle_analytic_regular_at env a) /\
  (candle_analytic_regular_at env (Candle_analytic_add a b) <=>
     candle_analytic_regular_at env a /\ candle_analytic_regular_at env b) /\
  (candle_analytic_regular_at env (Candle_analytic_mul a b) <=>
     candle_analytic_regular_at env a /\ candle_analytic_regular_at env b) /\
  (candle_analytic_regular_at env (Candle_analytic_square a) <=>
     candle_analytic_regular_at env a) /\
  (candle_analytic_regular_at env (Candle_analytic_inv a) <=>
     candle_analytic_regular_at env a /\
     ~(candle_analytic_value env a = &0)) /\
  (candle_analytic_regular_at env
      (Candle_analytic_sqrt lp ln ld up un ud a) <=>
     candle_analytic_regular_at env a /\
     &0 < candle_analytic_value env a) /\
  (candle_analytic_regular_at env (Candle_analytic_atn a) <=>
     candle_analytic_regular_at env a) /\
  (candle_analytic_regular_at env Candle_analytic_pi_half <=> T)`;;

let candle_analytic_denote_dim_def = new_definition
 `candle_analytic_denote_dim e (z:real^N) =
    candle_analytic_value
      (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e`;;

let candle_analytic_denote_dim_poly = prove
 (`!p.
     candle_poly_valid_dim (dimindex (:N)) p
     ==> (candle_analytic_denote_dim (Candle_analytic_poly p) :
          real^N->real) = candle_poly_denote_dim p`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; candle_analytic_denote_dim_def;
              candle_analytic_value_def; candle_poly_denote_dim_def] THEN
  ASM_SIMP_TAC[candle_poly_value_list_fun]);;

let candle_analytic_denote_dim_neg = prove
 (`!a. (candle_analytic_denote_dim (Candle_analytic_neg a) :
         real^N->real) =
       (\z. --(candle_analytic_denote_dim a z))`,
  REWRITE_TAC[FUN_EQ_THM; candle_analytic_denote_dim_def;
              candle_analytic_value_def]);;

let candle_analytic_denote_dim_add = prove
 (`!a b. (candle_analytic_denote_dim (Candle_analytic_add a b) :
           real^N->real) =
         (\z. candle_analytic_denote_dim a z +
              candle_analytic_denote_dim b z)`,
  REWRITE_TAC[FUN_EQ_THM; candle_analytic_denote_dim_def;
              candle_analytic_value_def]);;

let candle_analytic_denote_dim_mul = prove
 (`!a b. (candle_analytic_denote_dim (Candle_analytic_mul a b) :
           real^N->real) =
         (\z. candle_analytic_denote_dim a z *
              candle_analytic_denote_dim b z)`,
  REWRITE_TAC[FUN_EQ_THM; candle_analytic_denote_dim_def;
              candle_analytic_value_def]);;

let candle_analytic_denote_dim_square = prove
 (`!a. (candle_analytic_denote_dim (Candle_analytic_square a) :
         real^N->real) =
       (\z. candle_analytic_denote_dim a z *
            candle_analytic_denote_dim a z)`,
  REWRITE_TAC[FUN_EQ_THM; candle_analytic_denote_dim_def;
              candle_analytic_value_def]);;

let candle_analytic_denote_dim_inv = prove
 (`!a. (candle_analytic_denote_dim (Candle_analytic_inv a) :
         real^N->real) =
       (\z. inv (candle_analytic_denote_dim a z))`,
  REWRITE_TAC[FUN_EQ_THM; candle_analytic_denote_dim_def;
              candle_analytic_value_def]);;

let candle_analytic_denote_dim_sqrt = prove
 (`!lp ln ld up un ud a.
     (candle_analytic_denote_dim
       (Candle_analytic_sqrt lp ln ld up un ud a) : real^N->real) =
     (\z. sqrt (candle_analytic_denote_dim a z))`,
  REWRITE_TAC[FUN_EQ_THM; candle_analytic_denote_dim_def;
              candle_analytic_value_def]);;

let candle_analytic_denote_dim_atn = prove
 (`!a. (candle_analytic_denote_dim (Candle_analytic_atn a) :
         real^N->real) =
       (\z. atn (candle_analytic_denote_dim a z))`,
  REWRITE_TAC[FUN_EQ_THM; candle_analytic_denote_dim_def;
              candle_analytic_value_def]);;

let candle_analytic_denote_dim_pi_half = prove
 (`(candle_analytic_denote_dim Candle_analytic_pi_half : real^N->real) =
   (\z. pi / &2)`,
  REWRITE_TAC[FUN_EQ_THM; candle_analytic_denote_dim_def;
              candle_analytic_value_def]);;

let candle_analytic_denote_dim_diff2c = prove
 (`!e (z:real^N).
     candle_analytic_valid_dim (dimindex (:N)) e /\
     candle_analytic_regular_at
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e
     ==> diff2c (candle_analytic_denote_dim e) z`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[candle_analytic_denote_dim_poly;
                 candle_poly_denote_dim_diff2c];
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN STRIP_TAC THEN
    REWRITE_TAC[candle_analytic_denote_dim_neg] THEN
    USE_THEN "ih" (fun ih ->
      let source =
        MATCH_MP (SPEC `z:real^N` ih)
          (CONJ
            (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
            (ASSUME
              `candle_analytic_regular_at
                (list_of_seq (\k. (z:real^N)$(k + 1))
                  (dimindex (:N))) a`)) in
      ACCEPT_TAC
        (MATCH_MP
          (SPECL [`z:real^N`;
                  `(candle_analytic_denote_dim a):real^N->real`]
            diff2c_neg)
          source));
    MAP_EVERY X_GEN_TAC [`a:candle_analytic_expr`;
                         `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN STRIP_TAC THEN
    REWRITE_TAC[candle_analytic_denote_dim_add] THEN
    USE_THEN "iha" (fun iha ->
      USE_THEN "ihb" (fun ihb ->
        let source_a =
          MATCH_MP (SPEC `z:real^N` iha)
            (CONJ
              (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
              (ASSUME
                `candle_analytic_regular_at
                  (list_of_seq (\k. (z:real^N)$(k + 1))
                    (dimindex (:N))) a`)) in
        let source_b =
          MATCH_MP (SPEC `z:real^N` ihb)
            (CONJ
              (ASSUME `candle_analytic_valid_dim (dimindex (:N)) b`)
              (ASSUME
                `candle_analytic_regular_at
                  (list_of_seq (\k. (z:real^N)$(k + 1))
                    (dimindex (:N))) b`)) in
        ACCEPT_TAC
          (MATCH_MP
            (MATCH_MP
              (SPECL
                [`z:real^N`;
                 `(candle_analytic_denote_dim a):real^N->real`;
                 `(candle_analytic_denote_dim b):real^N->real`]
                diff2c_add)
              source_a)
            source_b)));
    MAP_EVERY X_GEN_TAC [`a:candle_analytic_expr`;
                         `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN STRIP_TAC THEN
    REWRITE_TAC[candle_analytic_denote_dim_mul] THEN
    USE_THEN "iha" (fun iha ->
      USE_THEN "ihb" (fun ihb ->
        let source_a =
          MATCH_MP (SPEC `z:real^N` iha)
            (CONJ
              (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
              (ASSUME
                `candle_analytic_regular_at
                  (list_of_seq (\k. (z:real^N)$(k + 1))
                    (dimindex (:N))) a`)) in
        let source_b =
          MATCH_MP (SPEC `z:real^N` ihb)
            (CONJ
              (ASSUME `candle_analytic_valid_dim (dimindex (:N)) b`)
              (ASSUME
                `candle_analytic_regular_at
                  (list_of_seq (\k. (z:real^N)$(k + 1))
                    (dimindex (:N))) b`)) in
        ACCEPT_TAC
          (MATCH_MP
            (MATCH_MP
              (SPECL
                [`z:real^N`;
                 `(candle_analytic_denote_dim a):real^N->real`;
                 `(candle_analytic_denote_dim b):real^N->real`]
                diff2c_mul)
              source_a)
            source_b)));
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN STRIP_TAC THEN
    REWRITE_TAC[candle_analytic_denote_dim_square] THEN
    USE_THEN "ih" (fun ih ->
      let source =
        MATCH_MP (SPEC `z:real^N` ih)
          (CONJ
            (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
            (ASSUME
              `candle_analytic_regular_at
                (list_of_seq (\k. (z:real^N)$(k + 1))
                  (dimindex (:N))) a`)) in
      ACCEPT_TAC
        (MATCH_MP
          (MATCH_MP
            (SPECL
              [`z:real^N`;
               `(candle_analytic_denote_dim a):real^N->real`;
               `(candle_analytic_denote_dim a):real^N->real`]
              diff2c_mul)
            source)
          source));
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN STRIP_TAC THEN
    REWRITE_TAC[candle_analytic_denote_dim_inv] THEN
    USE_THEN "ih" (fun ih ->
      let source =
        MATCH_MP (SPEC `z:real^N` ih)
          (CONJ
            (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
            (ASSUME
              `candle_analytic_regular_at
                (list_of_seq (\k. (z:real^N)$(k + 1))
                  (dimindex (:N))) a`)) in
      let regular =
        REWRITE_RULE[GSYM candle_analytic_denote_dim_def]
          (ASSUME
            `~(candle_analytic_value
                (list_of_seq (\k. (z:real^N)$(k + 1))
                  (dimindex (:N))) a = &0)`) in
      ACCEPT_TAC
        (REWRITE_RULE[o_DEF]
          (MATCH_MP
            (MATCH_MP
              (SPECL
                [`z:real^N`;
                 `(candle_analytic_denote_dim a):real^N->real`]
                diff2c_inv_compose)
              regular)
            source)));
    MAP_EVERY X_GEN_TAC
      [`lp:num`; `ln:num`; `ld:num`; `up:num`; `un:num`; `ud:num`;
       `a:candle_analytic_expr`] THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN STRIP_TAC THEN
    REWRITE_TAC[candle_analytic_denote_dim_sqrt] THEN
    USE_THEN "ih" (fun ih ->
      let source =
        MATCH_MP (SPEC `z:real^N` ih)
          (CONJ
            (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
            (ASSUME
              `candle_analytic_regular_at
                (list_of_seq (\k. (z:real^N)$(k + 1))
                  (dimindex (:N))) a`)) in
      let regular =
        REWRITE_RULE[GSYM candle_analytic_denote_dim_def]
          (ASSUME
            `&0 < candle_analytic_value
                (list_of_seq (\k. (z:real^N)$(k + 1))
                  (dimindex (:N))) a`) in
      ACCEPT_TAC
        (REWRITE_RULE[o_DEF]
          (MATCH_MP
            (MATCH_MP
              (SPECL
                [`z:real^N`;
                 `(candle_analytic_denote_dim a):real^N->real`]
                diff2c_sqrt_compose)
              regular)
            source)));
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def] THEN STRIP_TAC THEN
    REWRITE_TAC[candle_analytic_denote_dim_atn] THEN
    USE_THEN "ih" (fun ih ->
      let source =
        MATCH_MP (SPEC `z:real^N` ih)
          (CONJ
            (ASSUME `candle_analytic_valid_dim (dimindex (:N)) a`)
            (ASSUME
              `candle_analytic_regular_at
                (list_of_seq (\k. (z:real^N)$(k + 1))
                  (dimindex (:N))) a`)) in
      ACCEPT_TAC
        (REWRITE_RULE[o_DEF]
          (MATCH_MP
            (SPECL
              [`z:real^N`;
               `(candle_analytic_denote_dim a):real^N->real`]
              diff2c_atn_compose)
            source)));
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_analytic_valid_dim_def;
                candle_analytic_regular_at_def;
                candle_analytic_denote_dim_pi_half] THEN
    MATCH_ACCEPT_TAC diff2c_const]);;

end;;
