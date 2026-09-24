(* ========================================================================== *)
(* Coordinate-generic real calculus for reflected polynomial expressions.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Variables are interpreted by a total function *)
(* [num -> real].  The two derivative theorems therefore quantify over every *)
(* coordinate and every expression once; vector dimensions and source-list   *)
(* encodings are later specializations, not new calculus developments.       *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_calculus.ml";;
needs "candle/cv_compute_polynomial_expr_dim_derivatives.ml";;

module Candle_cv_polynomial_expr_dim_calculus = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_calculus;;
open Candle_cv_polynomial_expr_dim_derivatives;;

let candle_real_fun_update_def = new_definition
 `candle_real_fun_update (candle_rho:num->real) di u =
    (\k. if k = di then u else candle_rho k)`;;

let candle_real_fun_update_same = prove
 (`!candle_rho di. candle_real_fun_update candle_rho di (candle_rho di) = candle_rho`,
  REWRITE_TAC[candle_real_fun_update_def; FUN_EQ_THM] THEN MESON_TAC[]);;

let candle_poly_value_fun_def = define
 `(candle_poly_value_fun candle_rho (Candle_poly_const p n d) =
     candle_q_real ((p,n),d)) /\
  (candle_poly_value_fun candle_rho (Candle_poly_var i) = candle_rho i) /\
  (candle_poly_value_fun candle_rho (Candle_poly_neg a) =
     --(candle_poly_value_fun candle_rho a)) /\
  (candle_poly_value_fun candle_rho (Candle_poly_add a b) =
     candle_poly_value_fun candle_rho a + candle_poly_value_fun candle_rho b) /\
  (candle_poly_value_fun candle_rho (Candle_poly_mul a b) =
     candle_poly_value_fun candle_rho a * candle_poly_value_fun candle_rho b) /\
  (candle_poly_value_fun candle_rho (Candle_poly_square a) =
     candle_poly_value_fun candle_rho a * candle_poly_value_fun candle_rho a)`;;

let candle_poly_d_fun_def = define
 `(candle_poly_d_fun di candle_rho (Candle_poly_const p n d) = &0) /\
  (candle_poly_d_fun di candle_rho (Candle_poly_var i) =
     if i = di then &1 else &0) /\
  (candle_poly_d_fun di candle_rho (Candle_poly_neg a) =
     --(candle_poly_d_fun di candle_rho a)) /\
  (candle_poly_d_fun di candle_rho (Candle_poly_add a b) =
     candle_poly_d_fun di candle_rho a + candle_poly_d_fun di candle_rho b) /\
  (candle_poly_d_fun di candle_rho (Candle_poly_mul a b) =
     candle_poly_d_fun di candle_rho a * candle_poly_value_fun candle_rho b +
     candle_poly_value_fun candle_rho a * candle_poly_d_fun di candle_rho b) /\
  (candle_poly_d_fun di candle_rho (Candle_poly_square a) =
     candle_poly_d_fun di candle_rho a * candle_poly_value_fun candle_rho a +
     candle_poly_value_fun candle_rho a * candle_poly_d_fun di candle_rho a)`;;

let candle_poly_dd_fun_def = define
 `(candle_poly_dd_fun dj di candle_rho (Candle_poly_const p n d) = &0) /\
  (candle_poly_dd_fun dj di candle_rho (Candle_poly_var i) = &0) /\
  (candle_poly_dd_fun dj di candle_rho (Candle_poly_neg a) =
     --(candle_poly_dd_fun dj di candle_rho a)) /\
  (candle_poly_dd_fun dj di candle_rho (Candle_poly_add a b) =
     candle_poly_dd_fun dj di candle_rho a + candle_poly_dd_fun dj di candle_rho b) /\
  (candle_poly_dd_fun dj di candle_rho (Candle_poly_mul a b) =
     (candle_poly_dd_fun dj di candle_rho a * candle_poly_value_fun candle_rho b +
      candle_poly_d_fun di candle_rho a * candle_poly_d_fun dj candle_rho b) +
     (candle_poly_d_fun dj candle_rho a * candle_poly_d_fun di candle_rho b +
      candle_poly_value_fun candle_rho a * candle_poly_dd_fun dj di candle_rho b)) /\
  (candle_poly_dd_fun dj di candle_rho (Candle_poly_square a) =
     (candle_poly_dd_fun dj di candle_rho a * candle_poly_value_fun candle_rho a +
      candle_poly_d_fun di candle_rho a * candle_poly_d_fun dj candle_rho a) +
     (candle_poly_d_fun dj candle_rho a * candle_poly_d_fun di candle_rho a +
      candle_poly_value_fun candle_rho a * candle_poly_dd_fun dj di candle_rho a))`;;

let candle_poly_value_fun_has_real_derivative = prove
 (`!e candle_rho di.
     ((\u. candle_poly_value_fun (candle_real_fun_update candle_rho di u) e)
       has_real_derivative candle_poly_d_fun di candle_rho e)
      (atreal (candle_rho di))`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_value_fun_def; candle_poly_d_fun_def] THEN
    REAL_DIFF_TAC THEN REFL_TAC;
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_value_fun_def; candle_poly_d_fun_def;
                candle_real_fun_update_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_DIFF_TAC THEN REFL_TAC;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        REPEAT GEN_TAC THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_value_fun_def; candle_poly_d_fun_def] THEN
    candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[candle_real_fun_update_same] THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`] iha) THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_value_fun_def; candle_poly_d_fun_def] THEN
    candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[candle_real_fun_update_same] THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`] iha) THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_value_fun_def; candle_poly_d_fun_def] THEN
    candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[candle_real_fun_update_same] THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        REPEAT GEN_TAC THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_value_fun_def; candle_poly_d_fun_def] THEN
    candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[candle_real_fun_update_same] THEN CONV_TAC REAL_RING]);;

let candle_poly_d_fun_has_real_derivative = prove
 (`!e candle_rho di dj.
     ((\u. candle_poly_d_fun di (candle_real_fun_update candle_rho dj u) e)
       has_real_derivative candle_poly_dd_fun dj di candle_rho e)
      (atreal (candle_rho dj))`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_d_fun_def; candle_poly_dd_fun_def] THEN
    REAL_DIFF_TAC THEN REFL_TAC;
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_d_fun_def; candle_poly_dd_fun_def] THEN
    REAL_DIFF_TAC THEN REFL_TAC;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        REPEAT GEN_TAC THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`; `dj:num`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_d_fun_def; candle_poly_dd_fun_def] THEN
    candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[candle_real_fun_update_same] THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`; `dj:num`] iha) THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`; `dj:num`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_d_fun_def; candle_poly_dd_fun_def] THEN
    candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[candle_real_fun_update_same] THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`; `dj:num`] iha) THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`; `dj:num`] ihb) THEN
        ASSUME_TAC
          (SPECL [`a:candle_poly_expr`; `candle_rho:num->real`; `dj:num`]
            candle_poly_value_fun_has_real_derivative) THEN
        ASSUME_TAC
          (SPECL [`b:candle_poly_expr`; `candle_rho:num->real`; `dj:num`]
            candle_poly_value_fun_has_real_derivative)) THEN
    ASM_REWRITE_TAC[candle_poly_d_fun_def; candle_poly_dd_fun_def;
                    candle_poly_value_fun_def] THEN
    candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[candle_real_fun_update_same] THEN CONV_TAC REAL_RING;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        REPEAT GEN_TAC THEN
        ASSUME_TAC (SPECL [`candle_rho:num->real`; `di:num`; `dj:num`] ih) THEN
        ASSUME_TAC
          (SPECL [`a:candle_poly_expr`; `candle_rho:num->real`; `dj:num`]
            candle_poly_value_fun_has_real_derivative)) THEN
    ASM_REWRITE_TAC[candle_poly_d_fun_def; candle_poly_dd_fun_def;
                    candle_poly_value_fun_def] THEN
    candle_real_diff_with_assumptions_tac THEN
    ASM_REWRITE_TAC[candle_real_fun_update_same] THEN CONV_TAC REAL_RING]);;

(* Relate the total-function calculus semantics to the finite list data used  *)
(* by the compiler and reflected checker.                                     *)

let candle_q_real_lookup_in_range = prove
 (`!l i. i < LENGTH l ==> candle_q_real_lookup i l = EL i l`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LT];
    X_GEN_TAC `i:num` THEN
    MP_TAC (SPEC `i:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `j:num` SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[LENGTH; candle_q_real_lookup_def; EL; HD; TL; LT_SUC]]);;

let candle_q_real_lookup_list_of_seq = prove
 (`!candle_rho nvars i.
     i < nvars
     ==> candle_q_real_lookup i (list_of_seq candle_rho nvars) = candle_rho i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[candle_q_real_lookup_in_range; LENGTH_LIST_OF_SEQ;
               EL_LIST_OF_SEQ]);;

let candle_poly_value_list_fun = prove
 (`!e nvars candle_rho.
     candle_poly_valid_dim nvars e
     ==> candle_poly_value_list (list_of_seq candle_rho nvars) e =
         candle_poly_value_fun candle_rho e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def; candle_poly_value_list_def;
                candle_poly_value_fun_def];
    REPEAT GEN_TAC THEN
    SIMP_TAC[candle_poly_valid_dim_def; candle_poly_value_list_def;
             candle_poly_value_fun_def;
             candle_q_real_lookup_list_of_seq];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN DISCH_TAC THEN
        MP_TAC (SPECL [`nvars:num`; `candle_rho:num->real`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_value_list_def;
                    candle_poly_value_fun_def] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN STRIP_TAC THEN
        MP_TAC (SPECL [`nvars:num`; `candle_rho:num->real`] iha) THEN
        MP_TAC (SPECL [`nvars:num`; `candle_rho:num->real`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_value_list_def;
                    candle_poly_value_fun_def] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN STRIP_TAC THEN
        MP_TAC (SPECL [`nvars:num`; `candle_rho:num->real`] iha) THEN
        MP_TAC (SPECL [`nvars:num`; `candle_rho:num->real`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_value_list_def;
                    candle_poly_value_fun_def] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN DISCH_TAC THEN
        MP_TAC (SPECL [`nvars:num`; `candle_rho:num->real`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_value_list_def;
                    candle_poly_value_fun_def] THEN MESON_TAC[]]);;

let candle_poly_d_list_fun = prove
 (`!e nvars candle_rho di.
     candle_poly_valid_dim nvars e
     ==> candle_poly_d_list di (list_of_seq candle_rho nvars) e =
         candle_poly_d_fun di candle_rho e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def; candle_poly_d_list_def;
                candle_poly_d_fun_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def; candle_poly_d_list_def;
                candle_poly_d_fun_def];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN DISCH_TAC THEN
        MP_TAC
         (SPECL [`nvars:num`; `candle_rho:num->real`; `di:num`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_d_list_def; candle_poly_d_fun_def] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN STRIP_TAC THEN
        MP_TAC
         (SPECL [`nvars:num`; `candle_rho:num->real`; `di:num`] iha) THEN
        MP_TAC
         (SPECL [`nvars:num`; `candle_rho:num->real`; `di:num`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_d_list_def; candle_poly_d_fun_def] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN STRIP_TAC THEN
        MP_TAC
         (SPECL [`nvars:num`; `candle_rho:num->real`; `di:num`] iha) THEN
        MP_TAC
         (SPECL [`nvars:num`; `candle_rho:num->real`; `di:num`] ihb)) THEN
    ASM_SIMP_TAC[candle_poly_d_list_def; candle_poly_d_fun_def;
                 candle_poly_value_list_fun] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN DISCH_TAC THEN
        MP_TAC
         (SPECL [`nvars:num`; `candle_rho:num->real`; `di:num`] ih)) THEN
    ASM_SIMP_TAC[candle_poly_d_list_def; candle_poly_d_fun_def;
                 candle_poly_value_list_fun] THEN MESON_TAC[]]);;

let candle_poly_dd_list_fun = prove
 (`!e nvars candle_rho di dj.
     candle_poly_valid_dim nvars e
     ==> candle_poly_dd_list dj di (list_of_seq candle_rho nvars) e =
         candle_poly_dd_fun dj di candle_rho e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def; candle_poly_dd_list_def;
                candle_poly_dd_fun_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_poly_valid_dim_def; candle_poly_dd_list_def;
                candle_poly_dd_fun_def];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN DISCH_TAC THEN
        MP_TAC
         (SPECL
           [`nvars:num`; `candle_rho:num->real`; `di:num`; `dj:num`] ih)) THEN
    ASM_REWRITE_TAC[candle_poly_dd_list_def; candle_poly_dd_fun_def] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN STRIP_TAC THEN
        MP_TAC
         (SPECL
           [`nvars:num`; `candle_rho:num->real`; `di:num`; `dj:num`] iha) THEN
        MP_TAC
         (SPECL
           [`nvars:num`; `candle_rho:num->real`; `di:num`; `dj:num`] ihb)) THEN
    ASM_REWRITE_TAC[candle_poly_dd_list_def; candle_poly_dd_fun_def] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN STRIP_TAC THEN
        MP_TAC
         (SPECL
           [`nvars:num`; `candle_rho:num->real`; `di:num`; `dj:num`] iha) THEN
        MP_TAC
         (SPECL
           [`nvars:num`; `candle_rho:num->real`; `di:num`; `dj:num`] ihb)) THEN
    ASM_SIMP_TAC[candle_poly_dd_list_def; candle_poly_dd_fun_def;
                 candle_poly_d_list_fun; candle_poly_value_list_fun] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih ->
        REPEAT GEN_TAC THEN
        REWRITE_TAC[candle_poly_valid_dim_def] THEN DISCH_TAC THEN
        MP_TAC
         (SPECL
           [`nvars:num`; `candle_rho:num->real`; `di:num`; `dj:num`] ih)) THEN
    ASM_SIMP_TAC[candle_poly_dd_list_def; candle_poly_dd_fun_def;
                 candle_poly_d_list_fun; candle_poly_value_list_fun] THEN
    MESON_TAC[]]);;

end;;
