(* ========================================================================== *)
(* Computed-domain certificates imply the analytic regularity contract.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The reflected jet evaluator checks every      *)
(* reciprocal and square-root denominator over the complete input box.  This *)
(* layer turns those data checks into the pointwise hypotheses required by   *)
(* the universal calculus bridge, once for the complete analytic AST.        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_hessian.ml";;

module Candle_cv_analytic_expr_domain = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_inv_core;;
open Candle_cv_exact_interval_sqrt_certificate;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;

let candle_q_interval_not_zero_contains_nonzero = prove
 (`!i x.
     candle_q_interval_not_zero i /\ candle_q_interval_contains i x
     ==> ~(x = &0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_not_zero_real;
              candle_q_interval_contains_def] THEN
  REAL_ARITH_TAC);;

let candle_q_interval_sqrt_certificate_input_nonnegative = prove
 (`!input output x.
     candle_q_interval_sqrt_certificate input output /\
     candle_q_interval_contains input x
     ==> &0 <= x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_sqrt_certificate_def;
              candle_q_interval_contains_def; candle_q_le_real;
              candle_q_zero_def; candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let candle_q_dim_jet_sqrt_domain_value_positive = prove
 (`!s a x.
     candle_q_dim_jet_sqrt_domain s a /\
     candle_q_interval_contains (candle_q_dim_jet_f a) x
     ==> &0 < x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_sqrt_domain_def] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_interval_sqrt_certificate_input_nonnegative];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains s (sqrt x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_interval_sqrt_certificate_sound];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_interval_contains
      (candle_q_interval_add_normalized s s) (sqrt x + sqrt x)`
   ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_interval_add_normalized_sound];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(sqrt x + sqrt x = &0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[candle_q_interval_not_zero_contains_nonzero];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt x` ASSUME_TAC THENL
   [MP_TAC (SPEC `x:real` SQRT_POS_LE) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC (SPEC `x:real` SQRT_LT_0) THEN ASM_REWRITE_TAC[]]);;

let candle_q_dim_analytic_domain_regular = prove
 (`!e boxes env.
     candle_q_stack_contains boxes env /\
     candle_q_dim_analytic_domain boxes e
     ==> candle_analytic_regular_at env e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_q_dim_analytic_domain_def;
                candle_analytic_regular_at_def];
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC
      [`boxes:(((num#num)#num)#((num#num)#num))list`; `env:real list`] THEN
    REWRITE_TAC[candle_q_dim_analytic_domain_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "ih" (fun ih ->
      ACCEPT_TAC
        (MATCH_MP
          (SPECL
            [`boxes:(((num#num)#num)#((num#num)#num))list`;
             `env:real list`] ih)
          (CONJ
            (ASSUME `candle_q_stack_contains boxes env`)
            (ASSUME `candle_q_dim_analytic_domain boxes a`))));
    MAP_EVERY X_GEN_TAC [`a:candle_analytic_expr`;
                         `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    MAP_EVERY X_GEN_TAC
      [`boxes:(((num#num)#num)#((num#num)#num))list`; `env:real list`] THEN
    REWRITE_TAC[candle_q_dim_analytic_domain_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "iha" (fun ih ->
        ACCEPT_TAC
          (MATCH_MP
            (SPECL
              [`boxes:(((num#num)#num)#((num#num)#num))list`;
               `env:real list`] ih)
            (CONJ
              (ASSUME `candle_q_stack_contains boxes env`)
              (ASSUME `candle_q_dim_analytic_domain boxes a`))));
      USE_THEN "ihb" (fun ih ->
        ACCEPT_TAC
          (MATCH_MP
            (SPECL
              [`boxes:(((num#num)#num)#((num#num)#num))list`;
               `env:real list`] ih)
            (CONJ
              (ASSUME `candle_q_stack_contains boxes env`)
              (ASSUME `candle_q_dim_analytic_domain boxes b`))))];
    MAP_EVERY X_GEN_TAC [`a:candle_analytic_expr`;
                         `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    MAP_EVERY X_GEN_TAC
      [`boxes:(((num#num)#num)#((num#num)#num))list`; `env:real list`] THEN
    REWRITE_TAC[candle_q_dim_analytic_domain_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "iha" (fun ih ->
        ACCEPT_TAC
          (MATCH_MP
            (SPECL
              [`boxes:(((num#num)#num)#((num#num)#num))list`;
               `env:real list`] ih)
            (CONJ
              (ASSUME `candle_q_stack_contains boxes env`)
              (ASSUME `candle_q_dim_analytic_domain boxes a`))));
      USE_THEN "ihb" (fun ih ->
        ACCEPT_TAC
          (MATCH_MP
            (SPECL
              [`boxes:(((num#num)#num)#((num#num)#num))list`;
               `env:real list`] ih)
            (CONJ
              (ASSUME `candle_q_stack_contains boxes env`)
              (ASSUME `candle_q_dim_analytic_domain boxes b`))))];
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC
      [`boxes:(((num#num)#num)#((num#num)#num))list`; `env:real list`] THEN
    REWRITE_TAC[candle_q_dim_analytic_domain_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN
    USE_THEN "ih" (fun ih ->
      ACCEPT_TAC
        (MATCH_MP
          (SPECL
            [`boxes:(((num#num)#num)#((num#num)#num))list`;
             `env:real list`] ih)
          (CONJ
            (ASSUME `candle_q_stack_contains boxes env`)
            (ASSUME `candle_q_dim_analytic_domain boxes a`))));
    X_GEN_TAC `a:candle_analytic_expr` THEN DISCH_THEN
      (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC
      [`boxes:(((num#num)#num)#((num#num)#num))list`; `env:real list`] THEN
    REWRITE_TAC[candle_q_dim_analytic_domain_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "ih" (fun ih ->
        ACCEPT_TAC
          (MATCH_MP
            (SPECL
              [`boxes:(((num#num)#num)#((num#num)#num))list`;
               `env:real list`] ih)
            (CONJ
              (ASSUME `candle_q_stack_contains boxes env`)
              (ASSUME `candle_q_dim_analytic_domain boxes a`))));
      let domain_th =
        REWRITE_RULE[candle_q_dim_jet_inv_domain_def]
          (ASSUME
            `candle_q_dim_jet_inv_domain
              (candle_q_dim_analytic_jet boxes a)`) in
      let sound_th =
        MATCH_MP
          (SPECL [`a:candle_analytic_expr`;
                  `boxes:(((num#num)#num)#((num#num)#num))list`;
                  `env:real list`]
            candle_q_dim_analytic_jet_sound)
          (CONJ
            (ASSUME `candle_q_stack_contains boxes env`)
            (ASSUME `candle_q_dim_analytic_domain boxes a`)) in
      let contains_th =
        CONJUNCT1
          (REWRITE_RULE[candle_q_dim_analytic_contains_def;
                        candle_q_dim_jet_contains_components_def]
            sound_th) in
      ACCEPT_TAC
        (MATCH_MP
          candle_q_interval_not_zero_contains_nonzero
          (CONJ domain_th contains_th))];
    MAP_EVERY X_GEN_TAC
      [`lp:num`; `ln:num`; `ld:num`; `up:num`; `un:num`; `ud:num`;
       `a:candle_analytic_expr`] THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    MAP_EVERY X_GEN_TAC
      [`boxes:(((num#num)#num)#((num#num)#num))list`; `env:real list`] THEN
    REWRITE_TAC[candle_q_dim_analytic_domain_def;
                candle_analytic_regular_at_def] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "ih" (fun ih ->
        ACCEPT_TAC
          (MATCH_MP
            (SPECL
              [`boxes:(((num#num)#num)#((num#num)#num))list`;
               `env:real list`] ih)
            (CONJ
              (ASSUME `candle_q_stack_contains boxes env`)
              (ASSUME `candle_q_dim_analytic_domain boxes a`))));
      let sound_th =
        MATCH_MP
          (SPECL [`a:candle_analytic_expr`;
                  `boxes:(((num#num)#num)#((num#num)#num))list`;
                  `env:real list`]
            candle_q_dim_analytic_jet_sound)
          (CONJ
            (ASSUME `candle_q_stack_contains boxes env`)
            (ASSUME `candle_q_dim_analytic_domain boxes a`)) in
      let contains_th =
        CONJUNCT1
          (REWRITE_RULE[candle_q_dim_analytic_contains_def;
                        candle_q_dim_jet_contains_components_def]
            sound_th) in
      ACCEPT_TAC
        (MATCH_MP
          candle_q_dim_jet_sqrt_domain_value_positive
          (CONJ
            (ASSUME
              `candle_q_dim_jet_sqrt_domain
                (candle_analytic_sqrt_interval lp ln ld up un ud)
                (candle_q_dim_analytic_jet boxes a)`)
            contains_th))]]);;

end;;
