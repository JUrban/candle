(* ========================================================================== *)
(* Source-authenticated polynomial followed by one reflected reciprocal.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This bounded composition keeps the polynomial *)
(* child on the existing compact shared-jet path and applies [inv] to the     *)
(* resulting jet.  It is the integration bridge before the full analytic AST. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_dim_jet_inv.ml";;
needs "candle/cv_compute_polynomial_expr_reify.ml";;

module Candle_cv_analytic_poly_inv = struct

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

let candle_q_dim_poly_inv_program_def = new_definition
 `candle_q_dim_poly_inv_program boxes program =
    candle_q_dim_jet_inv
      (candle_q_dim_jet_normalized_program boxes program)`;;

let candle_q_dim_poly_inv_domain_def = new_definition
 `candle_q_dim_poly_inv_domain boxes program <=>
    candle_q_dim_jet_inv_domain
      (candle_q_dim_jet_normalized_program boxes program)`;;

let candle_cv_q_dim_poly_inv_program_def = new_definition
 `candle_cv_q_dim_poly_inv_program boxes program =
    candle_cv_q_dim_jet_inv
      (candle_cv_q_dim_jet_program boxes program)`;;

let candle_cv_q_dim_poly_inv_domain_def = new_definition
 `candle_cv_q_dim_poly_inv_domain boxes program =
    candle_cv_q_dim_jet_inv_domain
      (candle_cv_q_dim_jet_program boxes program)`;;

let candle_cv_q_dim_poly_inv_compute_eqs =
  candle_cv_q_dim_jet_inv_compute_eqs @
  map SPEC_ALL
   [candle_cv_q_dim_poly_inv_program_def;
    candle_cv_q_dim_poly_inv_domain_def];;

let candle_cv_q_dim_poly_inv_program_correct = prove
 (`!boxes program.
     candle_cv_q_dim_poly_inv_program
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list program) =
     candle_cv_q_dim_jet_encode
       (candle_q_dim_poly_inv_program boxes program)`,
  REWRITE_TAC[candle_cv_q_dim_poly_inv_program_def;
              candle_q_dim_poly_inv_program_def;
              candle_cv_q_dim_jet_program_correct;
              candle_cv_q_dim_jet_inv_correct]);;

let candle_cv_q_dim_poly_inv_domain_correct = prove
 (`!boxes program.
     candle_cv_q_dim_poly_inv_domain
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_instruction_list program) =
     Cexp_num
       (if candle_q_dim_poly_inv_domain boxes program then 1 else 0)`,
  REWRITE_TAC[candle_cv_q_dim_poly_inv_domain_def;
              candle_q_dim_poly_inv_domain_def;
              candle_cv_q_dim_jet_program_correct;
              candle_cv_q_dim_jet_inv_domain_correct]);;

let candle_q_dim_poly_contains_components = prove
 (`!n jet env e.
     candle_q_dim_poly_jet_contains n jet env e <=>
     candle_q_dim_jet_contains_components n jet
       (candle_poly_value_list env e)
       (\i. candle_poly_d_list i env e)
       (\i j. candle_poly_dd_list j i env e)`,
  REWRITE_TAC[candle_q_dim_poly_jet_contains_def;
              candle_q_dim_jet_contains_components_def]);;

let candle_q_dim_poly_inv_contains_def = new_definition
 `candle_q_dim_poly_inv_contains n jet env e <=>
    candle_q_dim_jet_contains_components n jet
      (inv (candle_poly_value_list env e))
      (\i. (--(inv (candle_poly_value_list env e) *
                   inv (candle_poly_value_list env e))) *
           candle_poly_d_list i env e)
      (\i j.
         (--(inv (candle_poly_value_list env e) *
                  inv (candle_poly_value_list env e))) *
           candle_poly_dd_list j i env e +
         (((inv (candle_poly_value_list env e) *
            inv (candle_poly_value_list env e)) *
           inv (candle_poly_value_list env e)) +
          ((inv (candle_poly_value_list env e) *
            inv (candle_poly_value_list env e)) *
           inv (candle_poly_value_list env e))) *
         (candle_poly_d_list i env e *
          candle_poly_d_list j env e))`;;

let candle_q_dim_poly_inv_program_sound = prove
 (`!e boxes env.
     candle_q_stack_contains boxes env /\
     candle_q_dim_poly_inv_domain boxes (candle_poly_compile e)
     ==> candle_q_dim_poly_inv_contains (LENGTH boxes)
           (candle_q_dim_poly_inv_program boxes (candle_poly_compile e))
           env e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_dim_poly_inv_contains_def;
              candle_q_dim_poly_inv_program_def] THEN
  MATCH_MP_TAC candle_q_dim_jet_inv_components_sound THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_q_dim_poly_compile_normalized_jet_program] THEN
    MATCH_ACCEPT_TAC candle_q_dim_poly_jet_normalized_shape;
    ASM_MESON_TAC[candle_q_dim_poly_inv_domain_def];
    REWRITE_TAC[GSYM candle_q_dim_poly_contains_components;
                candle_q_dim_poly_compile_normalized_jet_program] THEN
    MATCH_MP_TAC candle_q_dim_poly_jet_normalized_sound THEN
    ASM_REWRITE_TAC[]]);;

(* ML chooses the polynomial child, while the returned kernel theorem proves *)
(* that applying [inv] to its denotation is exactly the supplied source term. *)

let candle_poly_inv_reify_real_expression variables tm =
  if not (candle_q_is_unary `inv:real->real` tm) then
    failwith "candle analytic reciprocal reifier: expected top-level inv";
  let child = candle_q_dest_unary `inv:real->real` tm in
  let ast,valid_th,source_th,program_tm,run_th =
    candle_poly_reify_real_expression variables child in
  let reciprocal_source_th = AP_TERM `inv:real->real` source_th in
  let expected_source =
    mk_eq
      (mk_comb
        (`inv:real->real`,
         list_mk_comb
          (`candle_poly_value_list`,
           [mk_list (variables,`:real`); ast])),
       tm) in
  if hyp reciprocal_source_th <> [] ||
     not (aconv (concl reciprocal_source_th) expected_source) then
    failwith "candle analytic reciprocal reifier: source theorem mismatch";
  ast,valid_th,reciprocal_source_th,program_tm,run_th;;

end;;
