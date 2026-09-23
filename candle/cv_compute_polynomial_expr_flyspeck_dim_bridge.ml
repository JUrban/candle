(* ========================================================================== *)
(* Dimension-generic Flyspeck analytic bridge for reflected polynomials.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The denotation is over an arbitrary finite    *)
(* real vector.  Each AST constructor is connected once to Flyspeck's        *)
(* diff2c theory; individual expressions only instantiate the result.         *)
(* ========================================================================== *)

needs "taylor/theory/multivariate_taylor-compiled.hl";;
needs "candle/cv_compute_polynomial_expr_dim_calculus.ml";;
needs "candle/cv_compute_polynomial_expr_diff.ml";;

let _ = ();;

module Candle_cv_polynomial_expr_flyspeck_dim_bridge = struct

open Multivariate_taylor;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_diff;;

(* Reflected coordinates are zero-based; Flyspeck vectors are one-based. *)

let candle_poly_denote_dim_def = new_definition
 `candle_poly_denote_dim e (z:real^N) =
    candle_poly_value_fun (\k. z$(k + 1)) e`;;

let candle_poly_denote_dim_const = prove
 (`!p n d.
     candle_poly_denote_dim (Candle_poly_const p n d) =
       (\z:real^N. candle_q_real ((p,n),d))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; candle_poly_denote_dim_def;
              candle_poly_value_fun_def]);;

let candle_poly_denote_dim_var = prove
 (`!i. candle_poly_denote_dim (Candle_poly_var i) =
       (\z:real^N. z$(i + 1))`,
  GEN_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; candle_poly_denote_dim_def;
              candle_poly_value_fun_def]);;

let candle_poly_denote_dim_neg = prove
 (`!a. candle_poly_denote_dim (Candle_poly_neg a) =
       (\z:real^N. --(candle_poly_denote_dim a z))`,
  GEN_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; candle_poly_denote_dim_def;
              candle_poly_value_fun_def]);;

let candle_poly_denote_dim_add = prove
 (`!a b. candle_poly_denote_dim (Candle_poly_add a b) =
       (\z:real^N.
          candle_poly_denote_dim a z + candle_poly_denote_dim b z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; candle_poly_denote_dim_def;
              candle_poly_value_fun_def]);;

let candle_poly_denote_dim_mul = prove
 (`!a b. candle_poly_denote_dim (Candle_poly_mul a b) =
       (\z:real^N.
          candle_poly_denote_dim a z * candle_poly_denote_dim b z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; candle_poly_denote_dim_def;
              candle_poly_value_fun_def]);;

let candle_poly_denote_dim_square = prove
 (`!a. candle_poly_denote_dim (Candle_poly_square a) =
       (\z:real^N.
          candle_poly_denote_dim a z * candle_poly_denote_dim a z)`,
  GEN_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; candle_poly_denote_dim_def;
              candle_poly_value_fun_def]);;

let _ = print_endline "CANDLE_DIM_BRIDGE_STAGE denotation";;

let candle_poly_denote_dim_diff2c = prove
 (`!e (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e
     ==> diff2c (candle_poly_denote_dim e) z`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def;
                candle_poly_denote_dim_const] THEN
    MATCH_ACCEPT_TAC diff2c_const;
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def;
                candle_poly_denote_dim_var] THEN
    DISCH_TAC THEN MATCH_MP_TAC diff2c_x THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    X_GEN_TAC `a:candle_poly_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_poly_valid_dim_def] THEN
    DISCH_THEN (LABEL_TAC "valid") THEN
    REWRITE_TAC[candle_poly_denote_dim_neg] THEN
    USE_THEN "ih" (fun ih ->
      USE_THEN "valid" (fun valid ->
        let source = MATCH_MP (SPEC `z:real^N` ih) valid in
        ACCEPT_TAC
         (MATCH_MP
           (SPECL
             [`z:real^N`; `(candle_poly_denote_dim a):real^N->real`]
             diff2c_neg)
           source)));
    MAP_EVERY X_GEN_TAC [`a:candle_poly_expr`; `b:candle_poly_expr`] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_poly_valid_dim_def] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2 (LABEL_TAC "valida") (LABEL_TAC "validb")) THEN
    REWRITE_TAC[candle_poly_denote_dim_add] THEN
    USE_THEN "iha" (fun iha ->
      USE_THEN "valida" (fun valida ->
        USE_THEN "ihb" (fun ihb ->
          USE_THEN "validb" (fun validb ->
            let source_a = MATCH_MP (SPEC `z:real^N` iha) valida and
                source_b = MATCH_MP (SPEC `z:real^N` ihb) validb in
            ACCEPT_TAC
             (MATCH_MP
               (MATCH_MP
                 (SPECL
                   [`z:real^N`;
                    `(candle_poly_denote_dim a):real^N->real`;
                    `(candle_poly_denote_dim b):real^N->real`]
                   diff2c_add)
                 source_a)
               source_b)))));
    MAP_EVERY X_GEN_TAC [`a:candle_poly_expr`; `b:candle_poly_expr`] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_poly_valid_dim_def] THEN
    DISCH_THEN
     (CONJUNCTS_THEN2 (LABEL_TAC "valida") (LABEL_TAC "validb")) THEN
    REWRITE_TAC[candle_poly_denote_dim_mul] THEN
    USE_THEN "iha" (fun iha ->
      USE_THEN "valida" (fun valida ->
        USE_THEN "ihb" (fun ihb ->
          USE_THEN "validb" (fun validb ->
            let source_a = MATCH_MP (SPEC `z:real^N` iha) valida and
                source_b = MATCH_MP (SPEC `z:real^N` ihb) validb in
            ACCEPT_TAC
             (MATCH_MP
               (MATCH_MP
                 (SPECL
                   [`z:real^N`;
                    `(candle_poly_denote_dim a):real^N->real`;
                    `(candle_poly_denote_dim b):real^N->real`]
                   diff2c_mul)
                 source_a)
               source_b)))));
    X_GEN_TAC `a:candle_poly_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[candle_poly_valid_dim_def] THEN
    DISCH_THEN (LABEL_TAC "valid") THEN
    REWRITE_TAC[candle_poly_denote_dim_square] THEN
    USE_THEN "ih" (fun ih ->
      USE_THEN "valid" (fun valid ->
        let source = MATCH_MP (SPEC `z:real^N` ih) valid in
        ACCEPT_TAC
         (MATCH_MP
           (MATCH_MP
             (SPECL
               [`z:real^N`; `(candle_poly_denote_dim a):real^N->real`;
                `(candle_poly_denote_dim a):real^N->real`]
               diff2c_mul)
             source)
           source)))]);;

let _ = print_endline "CANDLE_DIM_BRIDGE_STAGE diff2c";;

let candle_poly_denote_dim_diff2c_domain = prove
 (`!e (domain:real^N#real^N).
     candle_poly_valid_dim (dimindex (:N)) e
     ==> diff2c_domain domain (candle_poly_denote_dim e)`,
  REWRITE_TAC[diff2c_domain] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC candle_poly_denote_dim_diff2c THEN
  ASM_REWRITE_TAC[]);;

let candle_dim_diff2c_imp_differentiable = prove
 (`!f:real^N->real. !x:real^N.
     diff2c f x ==> (lift o f) differentiable at x`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC diff2_imp_diff THEN
  MATCH_MP_TAC diff2c_imp_diff2 THEN
  ASM_REWRITE_TAC[]);;

let _ = print_endline "CANDLE_DIM_BRIDGE_STAGE diff2c_domain";;

(* One theorem identifies every gradient and Hessian component.  [partial]  *)
(* is one-based, while the reflected evaluator is zero-based.               *)

let candle_poly_denote_dim_partials = prove
 (`!e (z:real^N) i j.
     candle_poly_valid_dim (dimindex (:N)) e /\
     i IN 1..dimindex (:N) /\
     j IN 1..dimindex (:N)
     ==>
       partial i (candle_poly_denote_dim e) z =
         candle_poly_d_fun (i - 1) (\k. z$(k + 1)) e /\
       partial2 j i (candle_poly_denote_dim e) z =
         candle_poly_dd_fun (j - 1) (i - 1) (\k. z$(k + 1)) e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def;
                candle_poly_denote_dim_const;
                candle_poly_d_fun_def; candle_poly_dd_fun_def;
                partial_const; partial2_const];
    X_GEN_TAC `k:num` THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
    REWRITE_TAC[candle_poly_valid_dim_def; IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN `k + 1 IN 1..dimindex (:N)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(k = i - 1) <=> (i = k + 1)` ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[candle_poly_denote_dim_var;
                 candle_poly_d_fun_def; candle_poly_dd_fun_def;
                 partial_x; partial2_x; IN_NUMSEG];
    X_GEN_TAC `a:candle_poly_expr` THEN DISCH_THEN
     (fun ih ->
        MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN STRIP_TAC THEN
        MP_TAC (SPECL [`z:real^N`; `i:num`; `j:num`] ih) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC) THEN
    MP_TAC
     (SPECL [`a:candle_poly_expr`; `z:real^N`]
       candle_poly_denote_dim_diff2c) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_poly_denote_dim a):real^N->real) (z:real^N)`)) THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (ASSUME
         `diff2c ((candle_poly_denote_dim a):real^N->real) (z:real^N)`)) THEN
    MP_TAC
     (SPECL
       [`i:num`; `(candle_poly_denote_dim a):real^N->real`; `z:real^N`]
       partial_neg) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL
       [`z:real^N`; `j:num`; `i:num`;
        `(candle_poly_denote_dim a):real^N->real`]
       second_partial_neg) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_poly_denote_dim_neg;
                 candle_poly_d_fun_def; candle_poly_dd_fun_def;
                 partial_neg; second_partial_neg;
                 candle_poly_denote_dim_diff2c;
                 candle_dim_diff2c_imp_differentiable;
                 diff2c_imp_diff2];
    MAP_EVERY X_GEN_TAC [`a:candle_poly_expr`; `b:candle_poly_expr`] THEN
    DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN STRIP_TAC THEN
        MP_TAC (SPECL [`z:real^N`; `i:num`; `j:num`] iha) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
        MP_TAC (SPECL [`z:real^N`; `i:num`; `j:num`] ihb) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC) THEN
    MP_TAC
     (SPECL [`a:candle_poly_expr`; `z:real^N`]
       candle_poly_denote_dim_diff2c) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL [`b:candle_poly_expr`; `z:real^N`]
       candle_poly_denote_dim_diff2c) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_poly_denote_dim a):real^N->real) (z:real^N)`)) THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_poly_denote_dim b):real^N->real) (z:real^N)`)) THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (ASSUME
         `diff2c ((candle_poly_denote_dim a):real^N->real) (z:real^N)`)) THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (ASSUME
         `diff2c ((candle_poly_denote_dim b):real^N->real) (z:real^N)`)) THEN
    MP_TAC
     (SPECL
       [`(candle_poly_denote_dim a):real^N->real`; `i:num`;
        `(candle_poly_denote_dim b):real^N->real`; `z:real^N`]
       partial_add) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL
       [`z:real^N`; `j:num`; `i:num`;
        `(candle_poly_denote_dim a):real^N->real`;
        `(candle_poly_denote_dim b):real^N->real`]
       second_partial_add) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_poly_denote_dim_add;
                 candle_poly_d_fun_def; candle_poly_dd_fun_def;
                 partial_add; second_partial_add;
                 candle_poly_denote_dim_diff2c;
                 candle_dim_diff2c_imp_differentiable;
                 diff2c_imp_diff2];
    MAP_EVERY X_GEN_TAC [`a:candle_poly_expr`; `b:candle_poly_expr`] THEN
    DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN STRIP_TAC THEN
        MP_TAC (SPECL [`z:real^N`; `i:num`; `j:num`] iha) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
        MP_TAC (SPECL [`z:real^N`; `i:num`; `j:num`] ihb) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
        MP_TAC (SPECL [`z:real^N`; `j:num`; `j:num`] iha) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
        MP_TAC (SPECL [`z:real^N`; `j:num`; `j:num`] ihb) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC) THEN
    MP_TAC
     (SPECL [`a:candle_poly_expr`; `z:real^N`]
       candle_poly_denote_dim_diff2c) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL [`b:candle_poly_expr`; `z:real^N`]
       candle_poly_denote_dim_diff2c) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_poly_denote_dim a):real^N->real) (z:real^N)`)) THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_poly_denote_dim b):real^N->real) (z:real^N)`)) THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (ASSUME
         `diff2c ((candle_poly_denote_dim a):real^N->real) (z:real^N)`)) THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (ASSUME
         `diff2c ((candle_poly_denote_dim b):real^N->real) (z:real^N)`)) THEN
    MP_TAC
     (SPECL
       [`(candle_poly_denote_dim a):real^N->real`; `i:num`;
        `(candle_poly_denote_dim b):real^N->real`; `z:real^N`]
       partial_mul) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL
       [`z:real^N`; `j:num`; `i:num`;
        `(candle_poly_denote_dim a):real^N->real`;
        `(candle_poly_denote_dim b):real^N->real`]
       second_partial_mul) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_poly_denote_dim_mul;
                 candle_poly_value_fun_def;
                 candle_poly_d_fun_def; candle_poly_dd_fun_def;
                 partial_mul; second_partial_mul;
                 candle_poly_denote_dim_diff2c;
                 candle_dim_diff2c_imp_differentiable;
                 diff2c_imp_diff2] THEN
    ASM_REWRITE_TAC[candle_poly_denote_dim_def];
    X_GEN_TAC `a:candle_poly_expr` THEN DISCH_THEN
     (fun ih ->
        MAP_EVERY X_GEN_TAC [`z:real^N`; `i:num`; `j:num`] THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN STRIP_TAC THEN
        MP_TAC (SPECL [`z:real^N`; `i:num`; `j:num`] ih) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
        MP_TAC (SPECL [`z:real^N`; `j:num`; `j:num`] ih) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC) THEN
    MP_TAC
     (SPECL [`a:candle_poly_expr`; `z:real^N`]
       candle_poly_denote_dim_diff2c) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASSUME_TAC
     (MATCH_MP candle_dim_diff2c_imp_differentiable
       (ASSUME
         `diff2c ((candle_poly_denote_dim a):real^N->real) (z:real^N)`)) THEN
    ASSUME_TAC
     (MATCH_MP diff2c_imp_diff2
       (ASSUME
         `diff2c ((candle_poly_denote_dim a):real^N->real) (z:real^N)`)) THEN
    MP_TAC
     (SPECL
       [`(candle_poly_denote_dim a):real^N->real`; `i:num`;
        `(candle_poly_denote_dim a):real^N->real`; `z:real^N`]
       partial_mul) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC
     (SPECL
       [`z:real^N`; `j:num`; `i:num`;
        `(candle_poly_denote_dim a):real^N->real`;
        `(candle_poly_denote_dim a):real^N->real`]
       second_partial_mul) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[candle_poly_denote_dim_square;
                 candle_poly_value_fun_def;
                 candle_poly_d_fun_def; candle_poly_dd_fun_def;
                 partial_mul; second_partial_mul;
                 candle_poly_denote_dim_diff2c;
                 candle_dim_diff2c_imp_differentiable;
                 diff2c_imp_diff2] THEN
    ONCE_REWRITE_TAC
     [SPECL [`z:real^N`; `a:candle_poly_expr`]
       candle_poly_denote_dim_def] THEN
    CONJ_TAC THENL
     [CONV_TAC REAL_RING THEN REWRITE_TAC[];
      CONV_TAC REAL_RING THEN REWRITE_TAC[]]]);;

let _ = print_endline "CANDLE_DIM_BRIDGE_STAGE partials";;

(* Symbolic differentiation and compilation therefore produce Flyspeck's   *)
(* actual derivatives uniformly for every supported expression.             *)

let candle_poly_diff_flyspeck_partial = prove
 (`!e (z:real^N) i.
     candle_poly_valid_dim (dimindex (:N)) e /\
     i IN 1..dimindex (:N)
     ==>
     candle_poly_value_fun (\k. z$(k + 1))
       (candle_poly_diff (i - 1) e) =
     partial i (candle_poly_denote_dim e) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (SPECL [`e:candle_poly_expr`; `z:real^N`; `i:num`; `i:num`]
     candle_poly_denote_dim_partials) THEN
  ASM_REWRITE_TAC[candle_poly_diff_value_fun] THEN MESON_TAC[]);;

let candle_poly_diff2_flyspeck_partial2 = prove
 (`!e (z:real^N) i j.
     candle_poly_valid_dim (dimindex (:N)) e /\
     i IN 1..dimindex (:N) /\
     j IN 1..dimindex (:N)
     ==>
     candle_poly_value_fun (\k. z$(k + 1))
       (candle_poly_diff2 (j - 1) (i - 1) e) =
     partial2 j i (candle_poly_denote_dim e) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (SPECL [`e:candle_poly_expr`; `z:real^N`; `i:num`; `j:num`]
     candle_poly_denote_dim_partials) THEN
  ASM_REWRITE_TAC[candle_poly_diff2_value_fun] THEN MESON_TAC[]);;

let _ = print_endline "CANDLE_DIM_BRIDGE_STAGE compiled_partials";;

(* The finite derivative data consumed by the reflected checker is exactly *)
(* Flyspeck's gradient and Hessian, in zero-to-one-based index order.       *)

let candle_poly_gradient_flyspeck_partials = prove
 (`!e (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e
     ==>
     candle_poly_gradient
       (dimindex (:N))
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e =
     list_of_seq
       (\di. partial (di + 1) (candle_poly_denote_dim e) z)
       (dimindex (:N))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; candle_poly_gradient_length;
              LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `di:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[candle_poly_gradient_el; EL_LIST_OF_SEQ;
               candle_poly_d_list_fun] THEN
  SUBGOAL_THEN `di + 1 IN 1..dimindex (:N)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(di + 1) - 1 = di` ASSUME_TAC THENL
   [ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC
   (SPECL [`e:candle_poly_expr`; `z:real^N`; `di + 1`]
     candle_poly_diff_flyspeck_partial) THEN
  ASM_REWRITE_TAC[candle_poly_diff_value_fun]);;

let candle_poly_hessian_flyspeck_partials = prove
 (`!e (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e
     ==>
     candle_poly_hessian
       (dimindex (:N))
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e =
     list_of_seq
       (\di.
          list_of_seq
            (\dj. partial2 (dj + 1) (di + 1)
                    (candle_poly_denote_dim e) z)
            (dimindex (:N)))
       (dimindex (:N))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; candle_poly_hessian_length;
              LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `di:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[LIST_EQ] THEN
  ASM_SIMP_TAC[candle_poly_hessian_row_length; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `dj:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[candle_poly_hessian_el; EL_LIST_OF_SEQ;
               candle_poly_dd_list_fun] THEN
  SUBGOAL_THEN `di + 1 IN 1..dimindex (:N)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dj + 1 IN 1..dimindex (:N)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(di + 1) - 1 = di` ASSUME_TAC THENL
   [ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(dj + 1) - 1 = dj` ASSUME_TAC THENL
   [ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC
   (SPECL
     [`e:candle_poly_expr`; `z:real^N`; `di + 1`; `dj + 1`]
     candle_poly_diff2_flyspeck_partial2) THEN
  ASM_REWRITE_TAC[candle_poly_diff2_value_fun]);;

let _ = print_endline "CANDLE_DIM_BRIDGE_STAGE derivative_lists";;

(* Language-wide analytic contract.  It is quantified over every valid AST, *)
(* not proved anew for individual Flyspeck expressions.  The polynomial      *)
(* language has no extra domain side conditions; later partial constructors  *)
(* will refine validity with their mechanically checked box conditions.       *)

let candle_poly_flyspeck_analytic_contract = prove
 (`!e (domain:real^N#real^N).
     candle_poly_valid_dim (dimindex (:N)) e
     ==>
     diff2c_domain domain (candle_poly_denote_dim e) /\
     (!z i.
        i IN 1..dimindex (:N)
        ==>
        candle_poly_value_fun (\k. (z:real^N)$(k + 1))
          (candle_poly_diff (i - 1) e) =
        partial i (candle_poly_denote_dim e) z) /\
     (!z i j.
        i IN 1..dimindex (:N) /\
        j IN 1..dimindex (:N)
        ==>
        candle_poly_value_fun (\k. (z:real^N)$(k + 1))
          (candle_poly_diff2 (j - 1) (i - 1) e) =
        partial2 j i (candle_poly_denote_dim e) z)`,
  REPEAT STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_poly_denote_dim_diff2c_domain THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC candle_poly_diff_flyspeck_partial THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC candle_poly_diff2_flyspeck_partial2 THEN
    ASM_REWRITE_TAC[]]);;

let _ = print_endline "CANDLE_DIM_BRIDGE_STAGE analytic_contract";;

end;;
