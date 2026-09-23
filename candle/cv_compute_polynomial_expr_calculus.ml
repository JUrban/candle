(* ========================================================================== *)
(* Universal real-calculus correctness for the reflected polynomial AST.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This theorem is the analytic half of the       *)
(* source bridge: symbolic jet components are actual first and second real    *)
(* derivatives for every expression, not expression-specific proof scripts.  *)
(* The later Flyspeck bridge only has to identify these two coordinate         *)
(* derivatives with partial/partial2 on real^N.                               *)
(* ========================================================================== *)

needs "Multivariate/realanalysis.ml";;
needs "candle/cv_compute_polynomial_expr_jet.ml";;

module Candle_cv_polynomial_expr_calculus = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;

(* [REAL_DIFF_TAC] recursively constructs derivatives without consulting the *)
(* tactic assumptions.  Structural induction deliberately supplies arbitrary *)
(* subexpression derivatives as assumptions, so expose just those derivative *)
(* facts to the conversion for the duration of one goal, then restore the     *)
(* global differentiation database even when conversion fails.               *)
let candle_real_diff_with_assumptions_tac =
  fun ((assumptions,_) as goal) ->
    let saved = !real_differentiation_theorems in
    let is_derivative theorem =
      can (term_match [] `(f has_real_derivative f') net`)
        (concl theorem) in
    let local_derivatives =
      filter is_derivative (map snd assumptions) in
    real_differentiation_theorems := local_derivatives @ saved;
    try
      let result = REAL_DIFF_TAC goal in
      real_differentiation_theorems := saved;
      result
    with Failure message ->
      real_differentiation_theorems := saved;
      failwith message;;

(* Both mixed orders are included.  Flyspeck's [partial2 j i] differentiates *)
(* [partial i] in coordinate [j], so a source bridge can instantiate either  *)
(* order without first proving a separate symmetry result.                    *)

let candle_poly_has_real_jet_derivatives = prove
 (`!e x y.
     ((\u. candle_poly_value u y e) has_real_derivative
       candle_poly_dx x y e) (atreal x) /\
     ((\v. candle_poly_value x v e) has_real_derivative
       candle_poly_dy x y e) (atreal y) /\
     ((\u. candle_poly_dx u y e) has_real_derivative
       candle_poly_dxx x y e) (atreal x) /\
     ((\v. candle_poly_dx x v e) has_real_derivative
       candle_poly_dxy x y e) (atreal y) /\
     ((\u. candle_poly_dy u y e) has_real_derivative
       candle_poly_dxy x y e) (atreal x) /\
     ((\v. candle_poly_dy x v e) has_real_derivative
       candle_poly_dyy x y e) (atreal y)`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_value_def; candle_poly_dx_def;
                candle_poly_dy_def; candle_poly_dxx_def;
                candle_poly_dxy_def; candle_poly_dyy_def] THEN
    REPEAT CONJ_TAC THEN REAL_DIFF_TAC THEN REFL_TAC;
    X_GEN_TAC `i:num` THEN
    MP_TAC (SPEC `i:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC[candle_poly_value_def; candle_poly_dx_def;
                  candle_poly_dy_def; candle_poly_dxx_def;
                  candle_poly_dxy_def; candle_poly_dyy_def;
                  candle_q_real_lookup_def] THEN
      REPEAT CONJ_TAC THEN REAL_DIFF_TAC THEN REFL_TAC;
      MP_TAC (SPEC `n:num` num_CASES) THEN
      DISCH_THEN
       (DISJ_CASES_THEN2 SUBST1_TAC
         (X_CHOOSE_THEN `m:num` SUBST1_TAC)) THEN
      REPEAT GEN_TAC THEN
      REWRITE_TAC[candle_poly_value_def; candle_poly_dx_def;
                  candle_poly_dy_def; candle_poly_dxx_def;
                  candle_poly_dxy_def; candle_poly_dyy_def;
                  candle_q_real_lookup_def] THEN
      REPEAT CONJ_TAC THEN REAL_DIFF_TAC THEN REFL_TAC];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_value_def; candle_poly_dx_def;
                    candle_poly_dy_def; candle_poly_dxx_def;
                    candle_poly_dxy_def; candle_poly_dyy_def] THEN
    REPEAT CONJ_TAC THEN candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN
    DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] iha) THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_value_def; candle_poly_dx_def;
                    candle_poly_dy_def; candle_poly_dxx_def;
                    candle_poly_dxy_def; candle_poly_dyy_def] THEN
    REPEAT CONJ_TAC THEN candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN
    DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] iha) THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_value_def; candle_poly_dx_def;
                    candle_poly_dy_def; candle_poly_dxx_def;
                    candle_poly_dxy_def; candle_poly_dyy_def] THEN
    REPEAT CONJ_TAC THEN candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
        STRIP_ASSUME_TAC (SPECL [`x:real`; `y:real`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_value_def; candle_poly_dx_def;
                    candle_poly_dy_def; candle_poly_dxx_def;
                    candle_poly_dxy_def; candle_poly_dyy_def] THEN
    REPEAT CONJ_TAC THEN candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING]);;

end;;
