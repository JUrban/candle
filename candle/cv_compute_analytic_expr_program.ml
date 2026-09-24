(* ========================================================================== *)
(* Postfix programs for complete nested reflected analytic expressions.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Polynomial regions remain compact shared-jet *)
(* programs.  Each analytic instruction carries both its jet and a domain    *)
(* result, so an invalid reciprocal or square-root certificate fails closed  *)
(* without reconstructing intermediate arithmetic theorems.                  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet.ml";;

module Candle_cv_analytic_expr_program = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_expr_jet;;

let candle_analytic_instruction_INDUCT,
    candle_analytic_instruction_RECURSION = define_type
  "candle_analytic_instruction =
       Candle_analytic_push_poly (candle_q_instruction list)
     | Candle_analytic_program_neg
     | Candle_analytic_program_add
     | Candle_analytic_program_mul
     | Candle_analytic_program_square
     | Candle_analytic_program_inv
     | Candle_analytic_program_sqrt
         (((num#num)#num)#((num#num)#num))";;

let candle_q_dim_analytic_result_domain_def = new_definition
 `candle_q_dim_analytic_result_domain result = FST result`;;

let candle_q_dim_analytic_result_jet_def = new_definition
 `candle_q_dim_analytic_result_jet result = SND result`;;

let candle_q_dim_analytic_result_default_def = new_definition
 `candle_q_dim_analytic_result_default boxes =
    (F,candle_q_dim_jet_normalized_zero boxes)`;;

let candle_q_dim_analytic_result_head_def = define
 `(candle_q_dim_analytic_result_head boxes [] =
     candle_q_dim_analytic_result_default boxes) /\
  (candle_q_dim_analytic_result_head boxes (CONS h t) = h)`;;

let candle_q_dim_analytic_result_tail_def = define
 `(candle_q_dim_analytic_result_tail [] = []) /\
  (candle_q_dim_analytic_result_tail (CONS h t) = t)`;;

let candle_q_dim_analytic_program_step_def = define
 `(candle_q_dim_analytic_program_step boxes
     (Candle_analytic_push_poly program) stack =
     CONS
       (T,candle_q_dim_jet_normalized_program boxes program) stack) /\
  (candle_q_dim_analytic_program_step boxes
     Candle_analytic_program_neg stack =
     CONS
       (candle_q_dim_analytic_result_domain
          (candle_q_dim_analytic_result_head boxes stack),
        candle_q_dim_jet_normalized_neg
          (candle_q_dim_analytic_result_jet
            (candle_q_dim_analytic_result_head boxes stack)))
       (candle_q_dim_analytic_result_tail stack)) /\
  (candle_q_dim_analytic_program_step boxes
     Candle_analytic_program_add stack =
     CONS
       ((candle_q_dim_analytic_result_domain
           (candle_q_dim_analytic_result_head boxes
             (candle_q_dim_analytic_result_tail stack)) /\
         candle_q_dim_analytic_result_domain
           (candle_q_dim_analytic_result_head boxes stack)),
        candle_q_dim_jet_normalized_add
          (candle_q_dim_analytic_result_jet
            (candle_q_dim_analytic_result_head boxes
              (candle_q_dim_analytic_result_tail stack)))
          (candle_q_dim_analytic_result_jet
            (candle_q_dim_analytic_result_head boxes stack)))
       (candle_q_dim_analytic_result_tail
         (candle_q_dim_analytic_result_tail stack))) /\
  (candle_q_dim_analytic_program_step boxes
     Candle_analytic_program_mul stack =
     CONS
       ((candle_q_dim_analytic_result_domain
           (candle_q_dim_analytic_result_head boxes
             (candle_q_dim_analytic_result_tail stack)) /\
         candle_q_dim_analytic_result_domain
           (candle_q_dim_analytic_result_head boxes stack)),
        candle_q_dim_jet_normalized_mul
          (candle_q_dim_analytic_result_jet
            (candle_q_dim_analytic_result_head boxes
              (candle_q_dim_analytic_result_tail stack)))
          (candle_q_dim_analytic_result_jet
            (candle_q_dim_analytic_result_head boxes stack)))
       (candle_q_dim_analytic_result_tail
         (candle_q_dim_analytic_result_tail stack))) /\
  (candle_q_dim_analytic_program_step boxes
     Candle_analytic_program_square stack =
     CONS
       (candle_q_dim_analytic_result_domain
          (candle_q_dim_analytic_result_head boxes stack),
        candle_q_dim_jet_normalized_mul
          (candle_q_dim_analytic_result_jet
            (candle_q_dim_analytic_result_head boxes stack))
          (candle_q_dim_analytic_result_jet
            (candle_q_dim_analytic_result_head boxes stack)))
       (candle_q_dim_analytic_result_tail stack)) /\
  (candle_q_dim_analytic_program_step boxes
     Candle_analytic_program_inv stack =
     CONS
       ((candle_q_dim_analytic_result_domain
           (candle_q_dim_analytic_result_head boxes stack) /\
         candle_q_dim_jet_inv_domain
           (candle_q_dim_analytic_result_jet
             (candle_q_dim_analytic_result_head boxes stack))),
        candle_q_dim_jet_inv
          (candle_q_dim_analytic_result_jet
            (candle_q_dim_analytic_result_head boxes stack)))
       (candle_q_dim_analytic_result_tail stack)) /\
  (candle_q_dim_analytic_program_step boxes
     (Candle_analytic_program_sqrt s) stack =
     CONS
       ((candle_q_dim_analytic_result_domain
           (candle_q_dim_analytic_result_head boxes stack) /\
         candle_q_dim_jet_sqrt_domain s
           (candle_q_dim_analytic_result_jet
             (candle_q_dim_analytic_result_head boxes stack))),
        candle_q_dim_jet_sqrt_with s
          (candle_q_dim_analytic_result_jet
            (candle_q_dim_analytic_result_head boxes stack)))
       (candle_q_dim_analytic_result_tail stack))`;;

let candle_q_dim_analytic_program_run_def = define
 `(candle_q_dim_analytic_program_run boxes [] stack = stack) /\
  (candle_q_dim_analytic_program_run boxes (CONS h t) stack =
     candle_q_dim_analytic_program_run boxes t
       (candle_q_dim_analytic_program_step boxes h stack))`;;

let candle_q_dim_analytic_program_run_append = prove
 (`!left right boxes stack.
     candle_q_dim_analytic_program_run boxes (APPEND left right) stack =
     candle_q_dim_analytic_program_run boxes right
       (candle_q_dim_analytic_program_run boxes left stack)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; candle_q_dim_analytic_program_run_def]);;

let candle_analytic_compile_def = define
 `(candle_analytic_compile (Candle_analytic_poly p) =
     [Candle_analytic_push_poly (candle_poly_compile p)]) /\
  (candle_analytic_compile (Candle_analytic_neg a) =
     APPEND (candle_analytic_compile a)
       [Candle_analytic_program_neg]) /\
  (candle_analytic_compile (Candle_analytic_add a b) =
     APPEND (candle_analytic_compile a)
       (APPEND (candle_analytic_compile b)
         [Candle_analytic_program_add])) /\
  (candle_analytic_compile (Candle_analytic_mul a b) =
     APPEND (candle_analytic_compile a)
       (APPEND (candle_analytic_compile b)
         [Candle_analytic_program_mul])) /\
  (candle_analytic_compile (Candle_analytic_square a) =
     APPEND (candle_analytic_compile a)
       [Candle_analytic_program_square]) /\
  (candle_analytic_compile (Candle_analytic_inv a) =
     APPEND (candle_analytic_compile a)
       [Candle_analytic_program_inv]) /\
  (candle_analytic_compile
      (Candle_analytic_sqrt lp ln ld up un ud a) =
     APPEND (candle_analytic_compile a)
       [Candle_analytic_program_sqrt
         (candle_analytic_sqrt_interval lp ln ld up un ud)])`;;

let candle_q_dim_analytic_compile_run = prove
 (`!e boxes stack.
     candle_q_dim_analytic_program_run boxes
       (candle_analytic_compile e) stack =
     CONS
       (candle_q_dim_analytic_domain boxes e,
        candle_q_dim_analytic_jet boxes e) stack`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_analytic_compile_def;
                  candle_q_dim_analytic_program_run_append;
                  candle_q_dim_analytic_program_run_def;
                  candle_q_dim_analytic_program_step_def;
                  candle_q_dim_analytic_result_domain_def;
                  candle_q_dim_analytic_result_jet_def;
                  candle_q_dim_analytic_result_head_def;
                  candle_q_dim_analytic_result_tail_def;
                  candle_q_dim_analytic_domain_def;
                  candle_q_dim_analytic_jet_def;
                  candle_q_dim_poly_compile_normalized_jet_program;
                  APPEND; FST; SND]);;

let candle_q_dim_analytic_program_def = new_definition
 `candle_q_dim_analytic_program boxes program =
    candle_q_dim_analytic_result_head boxes
      (candle_q_dim_analytic_program_run boxes program [])`;;

let candle_q_dim_analytic_compile_program = prove
 (`!e boxes.
     candle_q_dim_analytic_program boxes (candle_analytic_compile e) =
     (candle_q_dim_analytic_domain boxes e,
      candle_q_dim_analytic_jet boxes e)`,
  REWRITE_TAC[candle_q_dim_analytic_program_def;
              candle_q_dim_analytic_compile_run;
              candle_q_dim_analytic_result_head_def]);;

end;;
