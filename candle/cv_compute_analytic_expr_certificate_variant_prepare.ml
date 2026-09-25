(* ========================================================================== *)
(* Lightweight preparation of certificate-only analytic program variants.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A box expression has already been connected  *)
(* to the original source formula.  Point-specific square-root certificates  *)
(* alter only certificate fields in that authenticated AST.  This module     *)
(* constructs and compiles such variants without repeating the source proof; *)
(* the certified adapter checks exact certificate erasure before use.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_point_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_certified_prove.ml";;

module Candle_cv_analytic_expr_certificate_variant_prepare = struct

open Candle_cv_exact_interval_reify;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_reify;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_point_certificate_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;

let rec candle_analytic_collect_sqrt_intervals
    sqrt_interval variables tm =
  if candle_analytic_is_pi_half tm ||
     candle_analytic_is_pi_half_expanded tm ||
     candle_analytic_polynomial_candidate variables tm then []
  else if candle_q_is_unary `(--):real->real` tm then
    candle_analytic_collect_sqrt_intervals sqrt_interval variables
      (candle_q_dest_unary `(--):real->real` tm)
  else if candle_q_is_binary `(+):real->real->real` tm then
    let left,right = candle_q_dest_binary `(+):real->real->real` tm in
    candle_analytic_collect_sqrt_intervals sqrt_interval variables left @
    candle_analytic_collect_sqrt_intervals sqrt_interval variables right
  else if candle_q_is_binary `(-):real->real->real` tm then
    let left,right = candle_q_dest_binary `(-):real->real->real` tm in
    candle_analytic_collect_sqrt_intervals sqrt_interval variables left @
    candle_analytic_collect_sqrt_intervals sqrt_interval variables right
  else if candle_q_is_binary `(*):real->real->real` tm then
    let left,right = candle_q_dest_binary `(*):real->real->real` tm in
    candle_analytic_collect_sqrt_intervals sqrt_interval variables left @
    candle_analytic_collect_sqrt_intervals sqrt_interval variables right
  else if candle_q_is_binary `(/):real->real->real` tm then
    let left,right = candle_q_dest_binary `(/):real->real->real` tm in
    candle_analytic_collect_sqrt_intervals sqrt_interval variables left @
    candle_analytic_collect_sqrt_intervals sqrt_interval variables right
  else if candle_q_is_unary `inv:real->real` tm then
    candle_analytic_collect_sqrt_intervals sqrt_interval variables
      (candle_q_dest_unary `inv:real->real` tm)
  else if candle_q_is_unary `sqrt:real->real` tm then
    let child = candle_q_dest_unary `sqrt:real->real` tm in
    candle_analytic_collect_sqrt_intervals sqrt_interval variables child @
    [sqrt_interval tm]
  else if candle_q_is_unary `atn:real->real` tm then
    candle_analytic_collect_sqrt_intervals sqrt_interval variables
      (candle_q_dest_unary `atn:real->real` tm)
  else if candle_q_is_binary `(pow):real->num->real` tm then
    let base,exponent = candle_q_dest_binary `(pow):real->num->real` tm in
    if dest_small_numeral exponent <> 2 then
      failwith "analytic certificate variant: unsupported power";
    candle_analytic_collect_sqrt_intervals sqrt_interval variables base
  else
    failwith "analytic certificate variant: unsupported source expression";;

let rec candle_analytic_replace_sqrt_intervals intervals expression =
  let operator,arguments = strip_comb expression in
  if aconv operator `Candle_analytic_poly` then expression,intervals
  else if aconv operator `Candle_analytic_pi_half` then expression,intervals
  else if aconv operator `Candle_analytic_neg` ||
          aconv operator `Candle_analytic_square` ||
          aconv operator `Candle_analytic_inv` ||
          aconv operator `Candle_analytic_atn` then
    match arguments with
    | [child] ->
        let replaced,remaining =
          candle_analytic_replace_sqrt_intervals intervals child in
        mk_comb (operator,replaced),remaining
    | _ -> failwith "analytic certificate variant: unary AST shape"
  else if aconv operator `Candle_analytic_add` ||
          aconv operator `Candle_analytic_mul` then
    match arguments with
    | [left;right] ->
        let replaced_left,after_left =
          candle_analytic_replace_sqrt_intervals intervals left in
        let replaced_right,remaining =
          candle_analytic_replace_sqrt_intervals after_left right in
        list_mk_comb (operator,[replaced_left;replaced_right]),remaining
    | _ -> failwith "analytic certificate variant: binary AST shape"
  else if aconv operator
      `Candle_analytic_sqrt:num->num->num->num->num->num->
        candle_analytic_expr->candle_analytic_expr` then
    match arguments with
    | [_;_;_;_;_;_;child] ->
        let replaced_child,after_child =
          candle_analytic_replace_sqrt_intervals intervals child in
        (match after_child with
         | interval :: remaining ->
             candle_analytic_sqrt_term interval replaced_child,remaining
         | [] ->
             failwith "analytic certificate variant: missing interval")
    | _ -> failwith "analytic certificate variant: square-root AST shape"
  else
    failwith "analytic certificate variant: unsupported AST";;

let candle_q_dim_taylor_model_variant_record_six
    base_prepared expression compile_theorem program_representation =
  {
    variant_function_term = base_prepared.function_term;
    variant_expression_term = expression;
    variant_compile_theorem = compile_theorem;
    variant_program_representation = program_representation;
    variant_program_representation_term =
      rand (concl program_representation);
  };;

let candle_q_dim_taylor_model_prepare_variant_six
    base_prepared intervals =
  let expression,remaining =
    candle_analytic_replace_sqrt_intervals
      intervals base_prepared.expression_term in
  if remaining <> [] then
    failwith "analytic certificate variant: unused intervals";
  let compile_theorem =
    REWRITE_CONV
      [candle_analytic_compile_def; candle_poly_compile_def; APPEND]
      (mk_comb (`candle_analytic_compile`,expression)) in
  let program = rand (concl compile_theorem) in
  let program_representation =
    candle_q_dim_analytic_jet_program_encode_conv program in
  if hyp compile_theorem <> [] || hyp program_representation <> [] then
    failwith "analytic certificate variant: program assumptions";
  candle_q_dim_taylor_model_variant_record_six
    base_prepared expression compile_theorem program_representation;;

let candle_q_dim_taylor_model_prepare_point_variant_six
    base_prepared lower upper =
  if length lower <> 6 || length upper <> 6 then
    failwith "analytic certificate variant: expected six coordinates";
  let variables = candle_poly_vector_components base_prepared.vector_term 6 in
  let values = candle_q_point_centers lower upper in
  let intervals =
    candle_analytic_collect_sqrt_intervals
      (candle_q_point_sqrt_callback variables values)
      variables base_prepared.source_term in
  candle_q_dim_taylor_model_prepare_variant_six
    base_prepared intervals;;

end;;
