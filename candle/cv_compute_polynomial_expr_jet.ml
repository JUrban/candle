(* ========================================================================== *)
(* Universal polynomial expression semantics for reflected nonlinear jets.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This in-logic AST is the induction boundary    *)
(* for the reusable analytic bridge.  The theorem below covers every valid    *)
(* expression in the current polynomial language; no expression-specific     *)
(* value/gradient/Hessian reconstruction is required.                         *)
(* ========================================================================== *)

needs "candle/cv_compute_whole_box_jet.ml";;

module Candle_cv_polynomial_expr_jet = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_jet;;

let candle_poly_expr_INDUCT,candle_poly_expr_RECURSION = define_type
  "candle_poly_expr =
       Candle_poly_const num num num
     | Candle_poly_var num
     | Candle_poly_neg candle_poly_expr
     | Candle_poly_add candle_poly_expr candle_poly_expr
     | Candle_poly_mul candle_poly_expr candle_poly_expr
     | Candle_poly_square candle_poly_expr";;

(* The current numerical jet has exactly two coordinates, numbered 0 and 1 *)
(* at the reflected-program boundary.  Keep validity explicit even though   *)
(* the total evaluator maps an out-of-range load to zero: source reification *)
(* must reject such an expression rather than silently change its meaning.  *)

let candle_poly_valid_2_def = define
 `(candle_poly_valid_2 (Candle_poly_const p n d) <=> T) /\
  (candle_poly_valid_2 (Candle_poly_var i) <=> i < 2) /\
  (candle_poly_valid_2 (Candle_poly_neg a) <=> candle_poly_valid_2 a) /\
  (candle_poly_valid_2 (Candle_poly_add a b) <=>
     candle_poly_valid_2 a /\ candle_poly_valid_2 b) /\
  (candle_poly_valid_2 (Candle_poly_mul a b) <=>
     candle_poly_valid_2 a /\ candle_poly_valid_2 b) /\
  (candle_poly_valid_2 (Candle_poly_square a) <=> candle_poly_valid_2 a)`;;

let candle_poly_value_def = define
 `(candle_poly_value x y (Candle_poly_const p n d) =
     candle_q_real ((p,n),d)) /\
  (candle_poly_value x y (Candle_poly_var i) =
     candle_q_real_lookup i [x;y]) /\
  (candle_poly_value x y (Candle_poly_neg a) =
     --(candle_poly_value x y a)) /\
  (candle_poly_value x y (Candle_poly_add a b) =
     candle_poly_value x y a + candle_poly_value x y b) /\
  (candle_poly_value x y (Candle_poly_mul a b) =
     candle_poly_value x y a * candle_poly_value x y b) /\
  (candle_poly_value x y (Candle_poly_square a) =
     candle_poly_value x y a * candle_poly_value x y a)`;;

(* Symbolic first- and second-derivative semantics.  The next analytic layer *)
(* proves once that these functions are Flyspeck partial/partial2.             *)

let candle_poly_dx_def = define
 `(candle_poly_dx x y (Candle_poly_const p n d) = &0) /\
  (candle_poly_dx x y (Candle_poly_var 0) = &1) /\
  (candle_poly_dx x y (Candle_poly_var (SUC i)) = &0) /\
  (candle_poly_dx x y (Candle_poly_neg a) = --(candle_poly_dx x y a)) /\
  (candle_poly_dx x y (Candle_poly_add a b) =
     candle_poly_dx x y a + candle_poly_dx x y b) /\
  (candle_poly_dx x y (Candle_poly_mul a b) =
     candle_poly_dx x y a * candle_poly_value x y b +
     candle_poly_value x y a * candle_poly_dx x y b) /\
  (candle_poly_dx x y (Candle_poly_square a) =
     candle_poly_dx x y a * candle_poly_value x y a +
     candle_poly_value x y a * candle_poly_dx x y a)`;;

let candle_poly_dy_def = define
 `(candle_poly_dy x y (Candle_poly_const p n d) = &0) /\
  (candle_poly_dy x y (Candle_poly_var 0) = &0) /\
  (candle_poly_dy x y (Candle_poly_var (SUC 0)) = &1) /\
  (candle_poly_dy x y (Candle_poly_var (SUC (SUC i))) = &0) /\
  (candle_poly_dy x y (Candle_poly_neg a) = --(candle_poly_dy x y a)) /\
  (candle_poly_dy x y (Candle_poly_add a b) =
     candle_poly_dy x y a + candle_poly_dy x y b) /\
  (candle_poly_dy x y (Candle_poly_mul a b) =
     candle_poly_dy x y a * candle_poly_value x y b +
     candle_poly_value x y a * candle_poly_dy x y b) /\
  (candle_poly_dy x y (Candle_poly_square a) =
     candle_poly_dy x y a * candle_poly_value x y a +
     candle_poly_value x y a * candle_poly_dy x y a)`;;

let candle_poly_dxx_def = define
 `(candle_poly_dxx x y (Candle_poly_const p n d) = &0) /\
  (candle_poly_dxx x y (Candle_poly_var i) = &0) /\
  (candle_poly_dxx x y (Candle_poly_neg a) = --(candle_poly_dxx x y a)) /\
  (candle_poly_dxx x y (Candle_poly_add a b) =
     candle_poly_dxx x y a + candle_poly_dxx x y b) /\
  (candle_poly_dxx x y (Candle_poly_mul a b) =
     (candle_poly_dxx x y a * candle_poly_value x y b +
      candle_poly_value x y a * candle_poly_dxx x y b) +
     (candle_poly_dx x y a * candle_poly_dx x y b +
      candle_poly_dx x y a * candle_poly_dx x y b)) /\
  (candle_poly_dxx x y (Candle_poly_square a) =
     (candle_poly_dxx x y a * candle_poly_value x y a +
      candle_poly_value x y a * candle_poly_dxx x y a) +
     (candle_poly_dx x y a * candle_poly_dx x y a +
      candle_poly_dx x y a * candle_poly_dx x y a))`;;

let candle_poly_dxy_def = define
 `(candle_poly_dxy x y (Candle_poly_const p n d) = &0) /\
  (candle_poly_dxy x y (Candle_poly_var i) = &0) /\
  (candle_poly_dxy x y (Candle_poly_neg a) = --(candle_poly_dxy x y a)) /\
  (candle_poly_dxy x y (Candle_poly_add a b) =
     candle_poly_dxy x y a + candle_poly_dxy x y b) /\
  (candle_poly_dxy x y (Candle_poly_mul a b) =
     (candle_poly_dxy x y a * candle_poly_value x y b +
      candle_poly_dx x y a * candle_poly_dy x y b) +
     (candle_poly_dy x y a * candle_poly_dx x y b +
      candle_poly_value x y a * candle_poly_dxy x y b)) /\
  (candle_poly_dxy x y (Candle_poly_square a) =
     (candle_poly_dxy x y a * candle_poly_value x y a +
      candle_poly_dx x y a * candle_poly_dy x y a) +
     (candle_poly_dy x y a * candle_poly_dx x y a +
      candle_poly_value x y a * candle_poly_dxy x y a))`;;

let candle_poly_dyy_def = define
 `(candle_poly_dyy x y (Candle_poly_const p n d) = &0) /\
  (candle_poly_dyy x y (Candle_poly_var i) = &0) /\
  (candle_poly_dyy x y (Candle_poly_neg a) = --(candle_poly_dyy x y a)) /\
  (candle_poly_dyy x y (Candle_poly_add a b) =
     candle_poly_dyy x y a + candle_poly_dyy x y b) /\
  (candle_poly_dyy x y (Candle_poly_mul a b) =
     (candle_poly_dyy x y a * candle_poly_value x y b +
      candle_poly_value x y a * candle_poly_dyy x y b) +
     (candle_poly_dy x y a * candle_poly_dy x y b +
      candle_poly_dy x y a * candle_poly_dy x y b)) /\
  (candle_poly_dyy x y (Candle_poly_square a) =
     (candle_poly_dyy x y a * candle_poly_value x y a +
      candle_poly_value x y a * candle_poly_dyy x y a) +
     (candle_poly_dy x y a * candle_poly_dy x y a +
      candle_poly_dy x y a * candle_poly_dy x y a))`;;

let candle_poly_real_jet_def = define
 `(candle_poly_real_jet x y (Candle_poly_const p n d) =
     candle_real_jet_constant ((p,n),d)) /\
  (candle_poly_real_jet x y (Candle_poly_var i) =
     candle_real_jet_variable x y i) /\
  (candle_poly_real_jet x y (Candle_poly_neg a) =
     candle_real_jet_neg (candle_poly_real_jet x y a)) /\
  (candle_poly_real_jet x y (Candle_poly_add a b) =
     candle_real_jet_add
       (candle_poly_real_jet x y a) (candle_poly_real_jet x y b)) /\
  (candle_poly_real_jet x y (Candle_poly_mul a b) =
     candle_real_jet_mul
       (candle_poly_real_jet x y a) (candle_poly_real_jet x y b)) /\
  (candle_poly_real_jet x y (Candle_poly_square a) =
     candle_real_jet_mul
       (candle_poly_real_jet x y a) (candle_poly_real_jet x y a))`;;

let candle_poly_variable_jet_correct = prove
 (`!i x y.
     candle_real_jet_f (candle_poly_real_jet x y (Candle_poly_var i)) =
       candle_poly_value x y (Candle_poly_var i) /\
     candle_real_jet_fx (candle_poly_real_jet x y (Candle_poly_var i)) =
       candle_poly_dx x y (Candle_poly_var i) /\
     candle_real_jet_fy (candle_poly_real_jet x y (Candle_poly_var i)) =
       candle_poly_dy x y (Candle_poly_var i) /\
     candle_real_jet_fxx (candle_poly_real_jet x y (Candle_poly_var i)) =
       candle_poly_dxx x y (Candle_poly_var i) /\
     candle_real_jet_fxy (candle_poly_real_jet x y (Candle_poly_var i)) =
       candle_poly_dxy x y (Candle_poly_var i) /\
     candle_real_jet_fyy (candle_poly_real_jet x y (Candle_poly_var i)) =
       candle_poly_dyy x y (Candle_poly_var i)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPEC `i:num` num_CASES) THEN
  DISCH_THEN
   (DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THENL
   [REWRITE_TAC[candle_poly_real_jet_def; candle_poly_value_def;
                candle_poly_dx_def; candle_poly_dy_def; candle_poly_dxx_def;
                candle_poly_dxy_def; candle_poly_dyy_def;
                candle_real_jet_variable_def; candle_real_jet_x_def;
                candle_real_jet_make_def; candle_real_jet_f_def;
                candle_real_jet_fx_def; candle_real_jet_fy_def;
                candle_real_jet_fxx_def; candle_real_jet_fxy_def;
                candle_real_jet_fyy_def; candle_q_real_lookup_def; FST; SND];
    MP_TAC (SPEC `n:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `m:num` SUBST1_TAC)) THEN
    REWRITE_TAC[candle_poly_real_jet_def; candle_poly_value_def;
                candle_poly_dx_def; candle_poly_dy_def; candle_poly_dxx_def;
                candle_poly_dxy_def; candle_poly_dyy_def;
                candle_real_jet_variable_def; candle_real_jet_y_def;
                candle_real_jet_zero_def; candle_real_jet_make_def;
                candle_real_jet_f_def; candle_real_jet_fx_def;
                candle_real_jet_fy_def; candle_real_jet_fxx_def;
                candle_real_jet_fxy_def; candle_real_jet_fyy_def;
                candle_q_real_lookup_def; FST; SND]]);;

let candle_poly_real_jet_correct = prove
 (`!e x y.
     candle_real_jet_f (candle_poly_real_jet x y e) =
       candle_poly_value x y e /\
     candle_real_jet_fx (candle_poly_real_jet x y e) =
       candle_poly_dx x y e /\
     candle_real_jet_fy (candle_poly_real_jet x y e) =
       candle_poly_dy x y e /\
     candle_real_jet_fxx (candle_poly_real_jet x y e) =
       candle_poly_dxx x y e /\
     candle_real_jet_fxy (candle_poly_real_jet x y e) =
       candle_poly_dxy x y e /\
     candle_real_jet_fyy (candle_poly_real_jet x y e) =
       candle_poly_dyy x y e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_poly_variable_jet_correct;
                  candle_poly_real_jet_def; candle_poly_value_def;
                  candle_poly_dx_def; candle_poly_dy_def;
                  candle_poly_dxx_def; candle_poly_dxy_def;
                  candle_poly_dyy_def; candle_real_jet_constant_def;
                  candle_real_jet_neg_def; candle_real_jet_add_def;
                  candle_real_jet_mul_def; candle_real_jet_make_def;
                  candle_real_jet_f_def; candle_real_jet_fx_def;
                  candle_real_jet_fy_def; candle_real_jet_fxx_def;
                  candle_real_jet_fxy_def; candle_real_jet_fyy_def;
                  FST; SND]);;

let candle_poly_compile_def = define
 `(candle_poly_compile (Candle_poly_const p n d) =
     [Candle_q_push p n d]) /\
  (candle_poly_compile (Candle_poly_var i) = [Candle_q_load i]) /\
  (candle_poly_compile (Candle_poly_neg a) =
     APPEND (candle_poly_compile a) [Candle_q_neg]) /\
  (candle_poly_compile (Candle_poly_add a b) =
     APPEND (candle_poly_compile a)
       (APPEND (candle_poly_compile b) [Candle_q_add])) /\
  (candle_poly_compile (Candle_poly_mul a b) =
     APPEND (candle_poly_compile a)
       (APPEND (candle_poly_compile b) [Candle_q_mul])) /\
  (candle_poly_compile (Candle_poly_square a) =
     APPEND (candle_poly_compile a) [Candle_q_square])`;;

let candle_real_jet_run_append = prove
 (`!left right x y stack.
     candle_real_jet_run x y (APPEND left right) stack =
     candle_real_jet_run x y right
       (candle_real_jet_run x y left stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; candle_real_jet_run_def]);;

let candle_poly_compile_run = prove
 (`!e x y stack.
     candle_real_jet_run x y (candle_poly_compile e) stack =
     CONS (candle_poly_real_jet x y e) stack`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_poly_compile_def; candle_poly_real_jet_def;
                  candle_real_jet_run_append; candle_real_jet_run_def;
                  candle_real_jet_step_def; candle_real_jet_head_def;
                  candle_real_jet_tail_def; APPEND]);;

let candle_poly_compile_program = prove
 (`!e x y.
     candle_real_jet_program x y (candle_poly_compile e) =
     candle_poly_real_jet x y e`,
  REWRITE_TAC[candle_real_jet_program_def; candle_poly_compile_run;
              candle_real_jet_head_def]);;

let candle_poly_compile_correct = prove
 (`!e x y.
     candle_real_jet_f
       (candle_real_jet_program x y (candle_poly_compile e)) =
       candle_poly_value x y e /\
     candle_real_jet_fx
       (candle_real_jet_program x y (candle_poly_compile e)) =
       candle_poly_dx x y e /\
     candle_real_jet_fy
       (candle_real_jet_program x y (candle_poly_compile e)) =
       candle_poly_dy x y e /\
     candle_real_jet_fxx
       (candle_real_jet_program x y (candle_poly_compile e)) =
       candle_poly_dxx x y e /\
     candle_real_jet_fxy
       (candle_real_jet_program x y (candle_poly_compile e)) =
       candle_poly_dxy x y e /\
     candle_real_jet_fyy
       (candle_real_jet_program x y (candle_poly_compile e)) =
       candle_poly_dyy x y e`,
  REWRITE_TAC[candle_poly_compile_program; candle_poly_real_jet_correct]);;

end;;
