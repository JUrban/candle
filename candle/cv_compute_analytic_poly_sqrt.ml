(* ========================================================================== *)
(* Source-authenticated polynomial followed by one guarded square root.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The polynomial child stays on the compact     *)
(* shared-jet evaluator.  A supplied rational square-root enclosure is then  *)
(* authenticated and applied to the complete value/gradient/Hessian jet.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_dim_jet_sqrt.ml";;
needs "candle/cv_compute_polynomial_expr_reify.ml";;

module Candle_cv_analytic_poly_sqrt = struct

open Candle_cv_exact_interval_reify;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_reify;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_representation;;
open Candle_cv_polynomial_expr_dim_jet_semantics;;
open Candle_cv_analytic_dim_jet_inv;;
open Candle_cv_analytic_dim_jet_sqrt;;

let candle_q_dim_poly_sqrt_program_def = new_definition
 `candle_q_dim_poly_sqrt_program s boxes program =
    candle_q_dim_jet_sqrt_with s
      (candle_q_dim_jet_normalized_program boxes program)`;;

let candle_q_dim_poly_sqrt_domain_def = new_definition
 `candle_q_dim_poly_sqrt_domain s boxes program <=>
    candle_q_dim_jet_sqrt_domain s
      (candle_q_dim_jet_normalized_program boxes program)`;;

let candle_cv_q_dim_poly_sqrt_program_def = new_definition
 `candle_cv_q_dim_poly_sqrt_program s boxes program =
    candle_cv_q_dim_jet_sqrt_with s
      (candle_cv_q_dim_jet_program boxes program)`;;

let candle_cv_q_dim_poly_sqrt_domain_def = new_definition
 `candle_cv_q_dim_poly_sqrt_domain s boxes program =
    candle_cv_q_dim_jet_sqrt_domain s
      (candle_cv_q_dim_jet_program boxes program)`;;

let candle_cv_q_dim_poly_sqrt_compute_eqs =
  candle_cv_q_dim_jet_sqrt_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_dim_poly_sqrt_program_def;
    candle_cv_q_dim_poly_sqrt_domain_def];;

let candle_cv_q_dim_poly_sqrt_program_correct = prove
 (`!s boxes program.
     candle_cv_q_dim_poly_sqrt_program
       (candle_cv_q_interval s)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list program) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_poly_sqrt_program s boxes program)`,
  REWRITE_TAC[candle_cv_q_dim_poly_sqrt_program_def;
              candle_q_dim_poly_sqrt_program_def;
              candle_cv_q_dim_jet_program_correct;
              candle_cv_q_dim_jet_sqrt_with_correct]);;

let candle_cv_q_dim_poly_sqrt_domain_correct = prove
 (`!s boxes program.
     candle_cv_q_dim_poly_sqrt_domain
       (candle_cv_q_interval s)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list program) =
     Cexp_num
       (if candle_q_dim_poly_sqrt_domain s boxes program then 1 else 0)`,
  REWRITE_TAC[candle_cv_q_dim_poly_sqrt_domain_def;
              candle_q_dim_poly_sqrt_domain_def;
              candle_cv_q_dim_jet_program_correct;
              candle_cv_q_dim_jet_sqrt_domain_correct]);;

let candle_q_dim_poly_sqrt_child_contains_components = prove
 (`!n jet env e.
     candle_q_dim_poly_jet_contains n jet env e <=>
     candle_q_dim_jet_contains_components n jet
       (candle_poly_value_list env e)
       (\i. candle_poly_d_list i env e)
       (\i j. candle_poly_dd_list j i env e)`,
  REWRITE_TAC[candle_q_dim_poly_jet_contains_def;
              candle_q_dim_jet_contains_components_def]);;

let candle_q_dim_poly_sqrt_contains_def = new_definition
 `candle_q_dim_poly_sqrt_contains n jet env e <=>
    candle_q_dim_jet_contains_components n jet
      (sqrt (candle_poly_value_list env e))
      (\i.
         inv (sqrt (candle_poly_value_list env e) +
              sqrt (candle_poly_value_list env e)) *
         candle_poly_d_list i env e)
      (\i j.
         (--inv
           ((sqrt (candle_poly_value_list env e) +
             sqrt (candle_poly_value_list env e)) *
            (candle_poly_value_list env e +
             candle_poly_value_list env e))) *
           (candle_poly_d_list i env e *
            candle_poly_d_list j env e) +
         inv (sqrt (candle_poly_value_list env e) +
              sqrt (candle_poly_value_list env e)) *
         candle_poly_dd_list j i env e)`;;

let candle_q_dim_poly_sqrt_program_sound = prove
 (`!e s boxes env.
     candle_q_stack_contains boxes env /\
     candle_q_dim_poly_sqrt_domain s boxes (candle_poly_compile e)
     ==> candle_q_dim_poly_sqrt_contains (LENGTH boxes)
           (candle_q_dim_poly_sqrt_program
             s boxes (candle_poly_compile e)) env e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_poly_sqrt_contains_def;
              candle_q_dim_poly_sqrt_program_def] THEN
  MATCH_MP_TAC candle_q_dim_jet_sqrt_components_sound THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_poly_compile_normalized_jet_program] THEN
    MATCH_ACCEPT_TAC candle_q_dim_poly_jet_normalized_shape;
    ASM_MESON_TAC[candle_q_dim_poly_sqrt_domain_def];
    REWRITE_TAC[GSYM candle_q_dim_poly_sqrt_child_contains_components;
                candle_q_dim_poly_compile_normalized_jet_program] THEN
    MATCH_MP_TAC candle_q_dim_poly_jet_normalized_sound THEN
    ASM_REWRITE_TAC[]]);;

(* ML selects the polynomial child and proves that the reconstructed source  *)
(* value under [sqrt] is exactly the supplied HOL term.                      *)

let candle_poly_sqrt_reify_real_expression variables tm =
  if not (candle_q_is_unary `sqrt:real->real` tm) then
    failwith "candle analytic square-root reifier: expected top-level sqrt";
  let child = candle_q_dest_unary `sqrt:real->real` tm in
  let ast,valid_th,source_th,program_tm,run_th =
    candle_poly_reify_real_expression variables child in
  let sqrt_source_th = AP_TERM `sqrt:real->real` source_th in
  let expected_source =
    mk_eq
      (mk_comb
        (`sqrt:real->real`,
         list_mk_comb
          (`candle_poly_value_list`,
           [mk_list (variables,`:real`); ast])),
       tm) in
  if hyp sqrt_source_th <> [] ||
     not (aconv (concl sqrt_source_th) expected_source) then
    failwith "candle analytic square-root reifier: source theorem mismatch";
  ast,valid_th,sqrt_source_th,program_tm,run_th;;

end;;
