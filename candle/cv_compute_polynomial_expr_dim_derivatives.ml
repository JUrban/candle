(* ========================================================================== *)
(* Dimension-parametric derivative semantics for reflected polynomials.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the reusable numerical/analytic        *)
(* boundary for Flyspeck's six-variable polynomials.  A source expression     *)
(* selects an AST only; the definitions below produce every gradient and      *)
(* Hessian component uniformly by coordinate index.                           *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_jet.ml";;

module Candle_cv_polynomial_expr_dim_derivatives = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;

(* Coordinate indices are zero-based at the reflected-data boundary. *)

let candle_poly_d_list_def = define
 `(candle_poly_d_list di env (Candle_poly_const p n d) = &0) /\
  (candle_poly_d_list di env (Candle_poly_var i) =
     if i = di then &1 else &0) /\
  (candle_poly_d_list di env (Candle_poly_neg a) =
     --(candle_poly_d_list di env a)) /\
  (candle_poly_d_list di env (Candle_poly_add a b) =
     candle_poly_d_list di env a + candle_poly_d_list di env b) /\
  (candle_poly_d_list di env (Candle_poly_mul a b) =
     candle_poly_d_list di env a * candle_poly_value_list env b +
     candle_poly_value_list env a * candle_poly_d_list di env b) /\
  (candle_poly_d_list di env (Candle_poly_square a) =
     candle_poly_d_list di env a * candle_poly_value_list env a +
     candle_poly_value_list env a * candle_poly_d_list di env a)`;;

(* [candle_poly_dd_list dj di] differentiates coordinate [di] first and       *)
(* coordinate [dj] second, matching Flyspeck's [partial2 j i] convention.     *)

let candle_poly_dd_list_def = define
 `(candle_poly_dd_list dj di env (Candle_poly_const p n d) = &0) /\
  (candle_poly_dd_list dj di env (Candle_poly_var i) = &0) /\
  (candle_poly_dd_list dj di env (Candle_poly_neg a) =
     --(candle_poly_dd_list dj di env a)) /\
  (candle_poly_dd_list dj di env (Candle_poly_add a b) =
     candle_poly_dd_list dj di env a +
     candle_poly_dd_list dj di env b) /\
  (candle_poly_dd_list dj di env (Candle_poly_mul a b) =
     (candle_poly_dd_list dj di env a * candle_poly_value_list env b +
      candle_poly_d_list di env a * candle_poly_d_list dj env b) +
     (candle_poly_d_list dj env a * candle_poly_d_list di env b +
      candle_poly_value_list env a * candle_poly_dd_list dj di env b)) /\
  (candle_poly_dd_list dj di env (Candle_poly_square a) =
     (candle_poly_dd_list dj di env a * candle_poly_value_list env a +
      candle_poly_d_list di env a * candle_poly_d_list dj env a) +
     (candle_poly_d_list dj env a * candle_poly_d_list di env a +
      candle_poly_value_list env a * candle_poly_dd_list dj di env a))`;;

let candle_poly_gradient_def = new_definition
 `candle_poly_gradient (nvars:num) env e =
    list_of_seq (\di. candle_poly_d_list di env e) nvars`;;

let candle_poly_hessian_def = new_definition
 `candle_poly_hessian (nvars:num) env e =
    list_of_seq
      (\di. list_of_seq
        (\dj. candle_poly_dd_list dj di env e) nvars)
      nvars`;;

let candle_poly_gradient_length = prove
 (`!nvars env e. LENGTH (candle_poly_gradient nvars env e) = nvars`,
  REWRITE_TAC[candle_poly_gradient_def; LENGTH_LIST_OF_SEQ]);;

let candle_poly_gradient_el = prove
 (`!nvars env e di.
     di < nvars
     ==> EL di (candle_poly_gradient nvars env e) =
         candle_poly_d_list di env e`,
  SIMP_TAC[candle_poly_gradient_def; EL_LIST_OF_SEQ]);;

let candle_poly_hessian_length = prove
 (`!nvars env e. LENGTH (candle_poly_hessian nvars env e) = nvars`,
  REWRITE_TAC[candle_poly_hessian_def; LENGTH_LIST_OF_SEQ]);;

let candle_poly_hessian_row_length = prove
 (`!nvars env e di.
     di < nvars
     ==> LENGTH (EL di (candle_poly_hessian nvars env e)) = nvars`,
  SIMP_TAC[candle_poly_hessian_def; EL_LIST_OF_SEQ;
           LENGTH_LIST_OF_SEQ]);;

let candle_poly_hessian_el = prove
 (`!nvars env e di dj.
     di < nvars /\ dj < nvars
     ==> EL dj (EL di (candle_poly_hessian nvars env e)) =
         candle_poly_dd_list dj di env e`,
  SIMP_TAC[candle_poly_hessian_def; EL_LIST_OF_SEQ]);;

(* Hessian symmetry is a theorem of the language semantics, not a property    *)
(* that individual source expressions must establish.                        *)

let candle_poly_dd_list_symmetric = prove
 (`!e env di dj.
     candle_poly_dd_list dj di env e =
     candle_poly_dd_list di dj env e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[candle_poly_dd_list_def];
    REPEAT GEN_TAC THEN REWRITE_TAC[candle_poly_dd_list_def];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        MAP_EVERY X_GEN_TAC [`env:real list`; `di:num`; `dj:num`] THEN
        MP_TAC (SPECL [`env:real list`; `di:num`; `dj:num`] ih)) THEN
    REWRITE_TAC[candle_poly_dd_list_def] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        MAP_EVERY X_GEN_TAC [`env:real list`; `di:num`; `dj:num`] THEN
        MP_TAC (SPECL [`env:real list`; `di:num`; `dj:num`] iha) THEN
        MP_TAC (SPECL [`env:real list`; `di:num`; `dj:num`] ihb)) THEN
    REWRITE_TAC[candle_poly_dd_list_def] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        MAP_EVERY X_GEN_TAC [`env:real list`; `di:num`; `dj:num`] THEN
        ASSUME_TAC (SPECL [`env:real list`; `di:num`; `dj:num`] iha) THEN
        ASSUME_TAC (SPECL [`env:real list`; `di:num`; `dj:num`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_dd_list_def] THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        MAP_EVERY X_GEN_TAC [`env:real list`; `di:num`; `dj:num`] THEN
        ASSUME_TAC (SPECL [`env:real list`; `di:num`; `dj:num`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_dd_list_def] THEN CONV_TAC REAL_RING]);;

(* The indexed definitions conservatively extend the already checked          *)
(* two-coordinate prototype.  This theorem is also a compact regression       *)
(* oracle for product-rule orientation.                                       *)

let candle_poly_dim_derivatives_2 = prove
 (`!e x y.
     candle_poly_d_list 0 [x;y] e = candle_poly_dx x y e /\
     candle_poly_d_list 1 [x;y] e = candle_poly_dy x y e /\
     candle_poly_dd_list 0 0 [x;y] e = candle_poly_dxx x y e /\
     candle_poly_dd_list 1 0 [x;y] e = candle_poly_dxy x y e /\
     candle_poly_dd_list 0 1 [x;y] e = candle_poly_dxy x y e /\
     candle_poly_dd_list 1 1 [x;y] e = candle_poly_dyy x y e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_d_list_def; candle_poly_dd_list_def;
                candle_poly_dx_def; candle_poly_dy_def;
                candle_poly_dxx_def; candle_poly_dxy_def;
                candle_poly_dyy_def];
    X_GEN_TAC `i:num` THEN
    MP_TAC (SPEC `i:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC[candle_poly_d_list_def; candle_poly_dd_list_def;
                  candle_poly_dx_def; candle_poly_dy_def;
                  candle_poly_dxx_def; candle_poly_dxy_def;
                  candle_poly_dyy_def] THEN
      ARITH_TAC;
      MP_TAC (SPEC `n:num` num_CASES) THEN
      DISCH_THEN
       (DISJ_CASES_THEN2 SUBST1_TAC
         (X_CHOOSE_THEN `m:num` SUBST1_TAC)) THEN
      REPEAT GEN_TAC THEN
      REWRITE_TAC[candle_poly_d_list_def; candle_poly_dd_list_def;
                  candle_poly_dx_def; candle_poly_dy_def;
                  candle_poly_dxx_def; candle_poly_dxy_def;
                  candle_poly_dyy_def] THEN
      ARITH_TAC];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_d_list_def; candle_poly_dd_list_def;
                    candle_poly_dx_def; candle_poly_dy_def;
                    candle_poly_dxx_def; candle_poly_dxy_def;
                    candle_poly_dyy_def];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] iha) THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_d_list_def; candle_poly_dd_list_def;
                    candle_poly_value_list_2;
                    candle_poly_dx_def; candle_poly_dy_def;
                    candle_poly_dxx_def; candle_poly_dxy_def;
                    candle_poly_dyy_def] THEN
    REPEAT CONJ_TAC THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] iha) THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_d_list_def; candle_poly_dd_list_def;
                    candle_poly_value_list_2;
                    candle_poly_dx_def; candle_poly_dy_def;
                    candle_poly_dxx_def; candle_poly_dxy_def;
                    candle_poly_dyy_def] THEN
    REPEAT CONJ_TAC THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_d_list_def; candle_poly_dd_list_def;
                    candle_poly_value_list_2;
                    candle_poly_dx_def; candle_poly_dy_def;
                    candle_poly_dxx_def; candle_poly_dxy_def;
                    candle_poly_dyy_def] THEN
    REPEAT CONJ_TAC THEN CONV_TAC REAL_RING]);;

end;;
