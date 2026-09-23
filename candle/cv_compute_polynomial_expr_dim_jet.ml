(* ========================================================================== *)
(* Dimension-generic second-order interval jets for polynomial expressions.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the ordinary HOL algorithm and its     *)
(* source-generic soundness theorem.  One traversal of the authenticated AST  *)
(* carries value, gradient, and Hessian interval data; it does not construct   *)
(* or normalize 1 + n + n^2 symbolic derivative programs.                     *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_dim_derivatives.ml";;

module Candle_cv_polynomial_expr_dim_jet = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_jet;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;

(* A dimension-generic jet is (value,(gradient,Hessian)). *)

let candle_q_dim_jet_make_def = new_definition
 `candle_q_dim_jet_make
    (f:((num#num)#num)#((num#num)#num))
    (gradient:(((num#num)#num)#((num#num)#num))list)
    (hessian:((((num#num)#num)#((num#num)#num))list)list) =
    (f,(gradient,hessian))`;;

let candle_q_dim_jet_f_def = new_definition
 `candle_q_dim_jet_f
    (jet:(((num#num)#num)#((num#num)#num))#
         ((((num#num)#num)#((num#num)#num))list#
          ((((num#num)#num)#((num#num)#num))list)list)) = FST jet`;;

let candle_q_dim_jet_gradient_def = new_definition
 `candle_q_dim_jet_gradient
    (jet:(((num#num)#num)#((num#num)#num))#
         ((((num#num)#num)#((num#num)#num))list#
          ((((num#num)#num)#((num#num)#num))list)list)) = FST (SND jet)`;;

let candle_q_dim_jet_hessian_def = new_definition
 `candle_q_dim_jet_hessian
    (jet:(((num#num)#num)#((num#num)#num))#
         ((((num#num)#num)#((num#num)#num))list#
          ((((num#num)#num)#((num#num)#num))list)list)) = SND (SND jet)`;;

let candle_q_dim_interval_row_lookup_def = define
 `(candle_q_dim_interval_row_lookup n
     ([]:((((num#num)#num)#((num#num)#num))list)list) = []) /\
  (candle_q_dim_interval_row_lookup 0 (CONS h t) = h) /\
  (candle_q_dim_interval_row_lookup (SUC n) (CONS h t) =
     candle_q_dim_interval_row_lookup n t)`;;

let candle_q_dim_jet_gradient_at_def = new_definition
 `candle_q_dim_jet_gradient_at
    (jet:(((num#num)#num)#((num#num)#num))#
         ((((num#num)#num)#((num#num)#num))list#
          ((((num#num)#num)#((num#num)#num))list)list)) di =
    candle_q_interval_lookup di (candle_q_dim_jet_gradient jet)`;;

let candle_q_dim_jet_hessian_at_def = new_definition
 `candle_q_dim_jet_hessian_at
    (jet:(((num#num)#num)#((num#num)#num))#
         ((((num#num)#num)#((num#num)#num))list#
          ((((num#num)#num)#((num#num)#num))list)list)) di dj =
    candle_q_interval_lookup dj
      (candle_q_dim_interval_row_lookup di
        (candle_q_dim_jet_hessian jet))`;;

let candle_q_dim_interval_zeros_def = new_definition
 `candle_q_dim_interval_zeros nvars =
    list_of_seq (\di. candle_q_zero_interval) nvars`;;

let candle_q_dim_interval_zero_matrix_def = new_definition
 `candle_q_dim_interval_zero_matrix nvars =
    list_of_seq
      (\di. list_of_seq (\dj. candle_q_zero_interval) nvars)
      nvars`;;

let candle_q_dim_jet_zero_def = new_definition
 `candle_q_dim_jet_zero nvars =
    candle_q_dim_jet_make candle_q_zero_interval
      (candle_q_dim_interval_zeros nvars)
      (candle_q_dim_interval_zero_matrix nvars)`;;

let candle_q_dim_jet_constant_def = new_definition
 `candle_q_dim_jet_constant nvars q =
    candle_q_dim_jet_make (q,q)
      (candle_q_dim_interval_zeros nvars)
      (candle_q_dim_interval_zero_matrix nvars)`;;

let candle_q_dim_jet_variable_def = new_definition
 `candle_q_dim_jet_variable nvars boxes variable =
    candle_q_dim_jet_make
      (candle_q_interval_lookup variable boxes)
      (list_of_seq
        (\di. if variable = di
              then candle_q_one_interval
              else candle_q_zero_interval)
        nvars)
      (candle_q_dim_interval_zero_matrix nvars)`;;

let candle_q_dim_jet_neg_def = new_definition
 `candle_q_dim_jet_neg nvars a =
    candle_q_dim_jet_make
      (candle_q_interval_neg (candle_q_dim_jet_f a))
      (list_of_seq
        (\di. candle_q_interval_neg
          (candle_q_dim_jet_gradient_at a di)) nvars)
      (list_of_seq
        (\di. list_of_seq
          (\dj. candle_q_interval_neg
            (candle_q_dim_jet_hessian_at a di dj)) nvars)
        nvars)`;;

let candle_q_dim_jet_add_def = new_definition
 `candle_q_dim_jet_add nvars a b =
    candle_q_dim_jet_make
      (candle_q_interval_add
        (candle_q_dim_jet_f a) (candle_q_dim_jet_f b))
      (list_of_seq
        (\di. candle_q_interval_add
          (candle_q_dim_jet_gradient_at a di)
          (candle_q_dim_jet_gradient_at b di)) nvars)
      (list_of_seq
        (\di. list_of_seq
          (\dj. candle_q_interval_add
            (candle_q_dim_jet_hessian_at a di dj)
            (candle_q_dim_jet_hessian_at b di dj)) nvars)
        nvars)`;;

let candle_q_dim_jet_mul_def = new_definition
 `candle_q_dim_jet_mul nvars a b =
    candle_q_dim_jet_make
      (candle_q_interval_mul
        (candle_q_dim_jet_f a) (candle_q_dim_jet_f b))
      (list_of_seq
        (\di. candle_q_interval_add
          (candle_q_interval_mul
            (candle_q_dim_jet_gradient_at a di)
            (candle_q_dim_jet_f b))
          (candle_q_interval_mul
            (candle_q_dim_jet_f a)
            (candle_q_dim_jet_gradient_at b di))) nvars)
      (list_of_seq
        (\di. list_of_seq
          (\dj. candle_q_interval_add
            (candle_q_interval_add
              (candle_q_interval_mul
                (candle_q_dim_jet_hessian_at a di dj)
                (candle_q_dim_jet_f b))
              (candle_q_interval_mul
                (candle_q_dim_jet_gradient_at a di)
                (candle_q_dim_jet_gradient_at b dj)))
            (candle_q_interval_add
              (candle_q_interval_mul
                (candle_q_dim_jet_gradient_at a dj)
                (candle_q_dim_jet_gradient_at b di))
              (candle_q_interval_mul
                (candle_q_dim_jet_f a)
                (candle_q_dim_jet_hessian_at b di dj)))) nvars)
        nvars)`;;

let candle_q_dim_poly_jet_def = define
 `(candle_q_dim_poly_jet nvars boxes (Candle_poly_const p n d) =
     candle_q_dim_jet_constant nvars ((p,n),d)) /\
  (candle_q_dim_poly_jet nvars boxes (Candle_poly_var i) =
     candle_q_dim_jet_variable nvars boxes i) /\
  (candle_q_dim_poly_jet nvars boxes (Candle_poly_neg a) =
     candle_q_dim_jet_neg nvars (candle_q_dim_poly_jet nvars boxes a)) /\
  (candle_q_dim_poly_jet nvars boxes (Candle_poly_add a b) =
     candle_q_dim_jet_add nvars
       (candle_q_dim_poly_jet nvars boxes a)
       (candle_q_dim_poly_jet nvars boxes b)) /\
  (candle_q_dim_poly_jet nvars boxes (Candle_poly_mul a b) =
     candle_q_dim_jet_mul nvars
       (candle_q_dim_poly_jet nvars boxes a)
       (candle_q_dim_poly_jet nvars boxes b)) /\
  (candle_q_dim_poly_jet nvars boxes (Candle_poly_square a) =
     candle_q_dim_jet_mul nvars
       (candle_q_dim_poly_jet nvars boxes a)
       (candle_q_dim_poly_jet nvars boxes a))`;;

(* Lookup facts keep the structural soundness proof componentwise and avoid   *)
(* materializing any symbolic derivative expression.                          *)

let candle_q_interval_lookup_in_range = prove
 (`!l i. i < LENGTH l ==> candle_q_interval_lookup i l = EL i l`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LT];
    X_GEN_TAC `i:num` THEN
    MP_TAC (SPEC `i:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `j:num` SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[LENGTH; candle_q_interval_lookup_def;
                    EL; HD; TL; LT_SUC]]);;

let candle_q_interval_lookup_list_of_seq = prove
 (`!f nvars i.
     i < nvars
     ==> candle_q_interval_lookup i (list_of_seq f nvars) = f i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[candle_q_interval_lookup_in_range;
               LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let candle_q_dim_interval_row_lookup_in_range = prove
 (`!rows i. i < LENGTH rows
             ==> candle_q_dim_interval_row_lookup i rows = EL i rows`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LT];
    X_GEN_TAC `i:num` THEN
    MP_TAC (SPEC `i:num` num_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `j:num` SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[LENGTH; candle_q_dim_interval_row_lookup_def;
                    EL; HD; TL; LT_SUC]]);;

let candle_q_dim_interval_row_lookup_list_of_seq = prove
 (`!f nvars i.
     i < nvars
     ==> candle_q_dim_interval_row_lookup i (list_of_seq f nvars) = f i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[candle_q_dim_interval_row_lookup_in_range;
               LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let candle_q_dim_jet_generated_accessors = prove
 (`(!f gradient hessian.
      candle_q_dim_jet_f
        (candle_q_dim_jet_make f gradient hessian) = f) /\
   (!nvars f gradient hessian di.
      di < nvars
      ==> candle_q_dim_jet_gradient_at
            (candle_q_dim_jet_make f (list_of_seq gradient nvars) hessian)
            di = gradient di) /\
   (!nvars f gradient hessian di dj.
      di < nvars /\ dj < nvars
      ==> candle_q_dim_jet_hessian_at
            (candle_q_dim_jet_make f (list_of_seq gradient nvars)
              (list_of_seq (\i. list_of_seq (hessian i) nvars) nvars))
            di dj = hessian di dj)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_dim_jet_f_def; candle_q_dim_jet_gradient_at_def;
              candle_q_dim_jet_gradient_def;
              candle_q_dim_jet_hessian_at_def;
              candle_q_dim_jet_hessian_def;
              candle_q_dim_jet_make_def; FST; SND] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_q_interval_lookup_list_of_seq;
               candle_q_dim_interval_row_lookup_list_of_seq]);;

(* Componentwise source contract.  This is equivalent to the list/matrix      *)
(* enclosure needed by the dimension-generic Taylor theorem, while being much *)
(* cheaper to establish by expression induction.                              *)

let candle_q_dim_poly_jet_contains_def = new_definition
 `candle_q_dim_poly_jet_contains nvars jet env e <=>
    candle_q_interval_contains (candle_q_dim_jet_f jet)
      (candle_poly_value_list env e) /\
    (!di. di < nvars
          ==> candle_q_interval_contains
                (candle_q_dim_jet_gradient_at jet di)
                (candle_poly_d_list di env e)) /\
    (!di dj. di < nvars /\ dj < nvars
             ==> candle_q_interval_contains
                   (candle_q_dim_jet_hessian_at jet di dj)
                   (candle_poly_dd_list dj di env e))`;;

let candle_q_dim_jet_assumption_tac =
  ASM_SIMP_TAC[candle_q_dim_jet_f_def;
               candle_q_dim_jet_gradient_at_def;
               candle_q_dim_jet_gradient_def;
               candle_q_dim_jet_hessian_at_def;
               candle_q_dim_jet_hessian_def];;

let candle_q_dim_poly_jet_sound = prove
 (`!e nvars boxes env.
     candle_q_stack_contains boxes env
     ==> candle_q_dim_poly_jet_contains nvars
           (candle_q_dim_poly_jet nvars boxes e) env e`,
  MATCH_MP_TAC candle_poly_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[candle_q_dim_poly_jet_def;
                candle_q_dim_poly_jet_contains_def;
                candle_q_dim_jet_constant_def;
                candle_q_dim_interval_zeros_def;
                candle_q_dim_interval_zero_matrix_def;
                candle_poly_value_list_def; candle_poly_d_list_def;
                candle_poly_dd_list_def] THEN
    REWRITE_TAC[candle_q_dim_jet_generated_accessors] THEN
    REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_dim_jet_gradient_at_def;
                 candle_q_dim_jet_gradient_def;
                 candle_q_dim_jet_hessian_at_def;
                 candle_q_dim_jet_hessian_def;
                 candle_q_dim_jet_make_def; FST; SND;
                 candle_q_interval_lookup_list_of_seq;
                 candle_q_dim_interval_row_lookup_list_of_seq;
                 candle_q_exact_interval_contains;
                 candle_q_zero_interval_contains];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[candle_q_dim_poly_jet_def;
                candle_q_dim_poly_jet_contains_def;
                candle_q_dim_jet_variable_def;
                candle_q_dim_interval_zero_matrix_def;
                candle_poly_value_list_def; candle_poly_d_list_def;
                candle_poly_dd_list_def] THEN
    REWRITE_TAC[candle_q_dim_jet_generated_accessors] THEN
    REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC candle_q_stack_lookup_contains THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[candle_q_dim_jet_gradient_at_def;
                   candle_q_dim_jet_gradient_def;
                   candle_q_dim_jet_make_def; FST; SND;
                   candle_q_interval_lookup_list_of_seq] THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC[candle_q_one_interval_contains;
                      candle_q_zero_interval_contains];
      ASM_SIMP_TAC[candle_q_dim_jet_hessian_at_def;
                   candle_q_dim_jet_hessian_def;
                   candle_q_dim_jet_make_def; FST; SND;
                   candle_q_interval_lookup_list_of_seq;
                   candle_q_dim_interval_row_lookup_list_of_seq;
                   candle_q_zero_interval_contains]];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih -> REPEAT GEN_TAC THEN DISCH_TAC THEN
                ASSUME_TAC (SPECL
                  [`nvars:num`;
                   `boxes:(((num#num)#num)#((num#num)#num))list`;
                   `env:real list`] ih)) THEN
    FIRST_X_ASSUM
     (fun th -> MP_TAC
       (MATCH_MP th (ASSUME `candle_q_stack_contains boxes env`))) THEN
    REWRITE_TAC[candle_q_dim_poly_jet_contains_def] THEN
    STRIP_TAC THEN
    RULE_ASSUM_TAC
     (REWRITE_RULE[candle_q_dim_jet_f_def;
                   candle_q_dim_jet_gradient_at_def;
                   candle_q_dim_jet_gradient_def;
                   candle_q_dim_jet_hessian_at_def;
                   candle_q_dim_jet_hessian_def]) THEN
    ASM_REWRITE_TAC[candle_q_dim_poly_jet_def;
                    candle_q_dim_jet_neg_def;
                    candle_poly_value_list_def; candle_poly_d_list_def;
                    candle_poly_dd_list_def;
                    candle_q_dim_jet_generated_accessors] THEN
    REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_dim_jet_gradient_at_def;
                 candle_q_dim_jet_gradient_def;
                 candle_q_dim_jet_hessian_at_def;
                 candle_q_dim_jet_hessian_def;
                 candle_q_dim_jet_make_def; FST; SND;
                 candle_q_interval_lookup_list_of_seq;
                 candle_q_dim_interval_row_lookup_list_of_seq] THEN
    MATCH_MP_TAC candle_q_interval_neg_sound THEN
    candle_q_dim_jet_assumption_tac;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN DISCH_TAC THEN
        STRIP_ASSUME_TAC (REWRITE_RULE[candle_q_dim_poly_jet_contains_def]
         (MATCH_MP
          (SPECL [`nvars:num`;
                  `boxes:(((num#num)#num)#((num#num)#num))list`;
                  `env:real list`] iha)
          (ASSUME `candle_q_stack_contains boxes env`))) THEN
        STRIP_ASSUME_TAC (REWRITE_RULE[candle_q_dim_poly_jet_contains_def]
         (MATCH_MP
          (SPECL [`nvars:num`;
                  `boxes:(((num#num)#num)#((num#num)#num))list`;
                  `env:real list`] ihb)
          (ASSUME `candle_q_stack_contains boxes env`)))) THEN
    RULE_ASSUM_TAC
     (REWRITE_RULE[candle_q_dim_jet_f_def;
                   candle_q_dim_jet_gradient_at_def;
                   candle_q_dim_jet_gradient_def;
                   candle_q_dim_jet_hessian_at_def;
                   candle_q_dim_jet_hessian_def]) THEN
    ASM_REWRITE_TAC[candle_q_dim_poly_jet_contains_def;
                    candle_q_dim_poly_jet_def;
                    candle_q_dim_jet_add_def;
                    candle_poly_value_list_def; candle_poly_d_list_def;
                    candle_poly_dd_list_def;
                    candle_q_dim_jet_generated_accessors] THEN
    REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[candle_q_dim_jet_gradient_at_def;
                 candle_q_dim_jet_gradient_def;
                 candle_q_dim_jet_hessian_at_def;
                 candle_q_dim_jet_hessian_def;
                 candle_q_dim_jet_make_def; FST; SND;
                 candle_q_interval_lookup_list_of_seq;
                 candle_q_dim_interval_row_lookup_list_of_seq] THEN
    MATCH_MP_TAC candle_q_interval_add_sound THEN
    candle_q_dim_jet_assumption_tac;
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ihs ->
        let iha,ihb = CONJ_PAIR ihs in
        REPEAT GEN_TAC THEN DISCH_TAC THEN
        STRIP_ASSUME_TAC (REWRITE_RULE[candle_q_dim_poly_jet_contains_def]
         (MATCH_MP
          (SPECL [`nvars:num`;
                  `boxes:(((num#num)#num)#((num#num)#num))list`;
                  `env:real list`] iha)
          (ASSUME `candle_q_stack_contains boxes env`))) THEN
        STRIP_ASSUME_TAC (REWRITE_RULE[candle_q_dim_poly_jet_contains_def]
         (MATCH_MP
          (SPECL [`nvars:num`;
                  `boxes:(((num#num)#num)#((num#num)#num))list`;
                  `env:real list`] ihb)
          (ASSUME `candle_q_stack_contains boxes env`)))) THEN
    RULE_ASSUM_TAC
     (REWRITE_RULE[candle_q_dim_jet_f_def;
                   candle_q_dim_jet_gradient_at_def;
                   candle_q_dim_jet_gradient_def;
                   candle_q_dim_jet_hessian_at_def;
                   candle_q_dim_jet_hessian_def]) THEN
    ASM_REWRITE_TAC[candle_q_dim_poly_jet_contains_def;
                    candle_q_dim_poly_jet_def;
                    candle_q_dim_jet_mul_def;
                    candle_poly_value_list_def; candle_poly_d_list_def;
                    candle_poly_dd_list_def;
                    candle_q_dim_jet_generated_accessors] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_interval_mul_sound THEN
      candle_q_dim_jet_assumption_tac;
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[candle_q_dim_jet_gradient_at_def;
                     candle_q_dim_jet_gradient_def;
                     candle_q_dim_jet_make_def; FST; SND;
                     candle_q_interval_lookup_list_of_seq] THEN
        MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THEN
        MATCH_MP_TAC candle_q_interval_mul_sound THEN
        candle_q_dim_jet_assumption_tac;
        REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[candle_q_dim_jet_hessian_at_def;
                     candle_q_dim_jet_hessian_def;
                     candle_q_dim_jet_make_def; FST; SND;
                     candle_q_interval_lookup_list_of_seq;
                     candle_q_dim_interval_row_lookup_list_of_seq] THEN
        MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THENL
         [MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THEN
          MATCH_MP_TAC candle_q_interval_mul_sound THEN
          candle_q_dim_jet_assumption_tac;
          MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THEN
          MATCH_MP_TAC candle_q_interval_mul_sound THEN
          candle_q_dim_jet_assumption_tac]]];
    REPEAT GEN_TAC THEN DISCH_THEN
     (fun ih -> REPEAT GEN_TAC THEN DISCH_TAC THEN
                STRIP_ASSUME_TAC
                 (REWRITE_RULE[candle_q_dim_poly_jet_contains_def]
                  (MATCH_MP
                  (SPECL
                    [`nvars:num`;
                     `boxes:(((num#num)#num)#((num#num)#num))list`;
                     `env:real list`] ih)
                  (ASSUME `candle_q_stack_contains boxes env`)))) THEN
    RULE_ASSUM_TAC
     (REWRITE_RULE[candle_q_dim_jet_f_def;
                   candle_q_dim_jet_gradient_at_def;
                   candle_q_dim_jet_gradient_def;
                   candle_q_dim_jet_hessian_at_def;
                   candle_q_dim_jet_hessian_def]) THEN
    ASM_REWRITE_TAC[candle_q_dim_poly_jet_contains_def;
                    candle_q_dim_poly_jet_def;
                    candle_q_dim_jet_mul_def;
                    candle_poly_value_list_def; candle_poly_d_list_def;
                    candle_poly_dd_list_def;
                    candle_q_dim_jet_generated_accessors] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_q_interval_mul_sound THEN
      candle_q_dim_jet_assumption_tac;
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[candle_q_dim_jet_gradient_at_def;
                     candle_q_dim_jet_gradient_def;
                     candle_q_dim_jet_make_def; FST; SND;
                     candle_q_interval_lookup_list_of_seq] THEN
        MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THEN
        MATCH_MP_TAC candle_q_interval_mul_sound THEN
        candle_q_dim_jet_assumption_tac;
        REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[candle_q_dim_jet_hessian_at_def;
                     candle_q_dim_jet_hessian_def;
                     candle_q_dim_jet_make_def; FST; SND;
                     candle_q_interval_lookup_list_of_seq;
                     candle_q_dim_interval_row_lookup_list_of_seq] THEN
        MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THENL
         [MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THEN
          MATCH_MP_TAC candle_q_interval_mul_sound THEN
          candle_q_dim_jet_assumption_tac;
          MATCH_MP_TAC candle_q_interval_add_sound THEN CONJ_TAC THEN
          MATCH_MP_TAC candle_q_interval_mul_sound THEN
          candle_q_dim_jet_assumption_tac]]]]);;

end;;
