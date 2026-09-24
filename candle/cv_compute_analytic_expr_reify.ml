(* ========================================================================== *)
(* Theorem-producing source reification for nested analytic expressions.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Maximal polynomial regions remain compact.   *)
(* An untrusted callback supplies rational square-root enclosures, while the *)
(* returned kernel theorem authenticates the complete source expression.     *)
(* Domain and enclosure validity are checked later by the reflected program. *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_reify.ml";;
needs "candle/cv_compute_analytic_expr_program_compute.ml";;

module Candle_cv_analytic_expr_reify = struct

open Candle_cv_exact_interval_reify;;
open Candle_cv_polynomial_expr_reify;;
open Candle_cv_analytic_expr_jet;;

let candle_analytic_poly_term child =
  mk_comb (`Candle_analytic_poly`,child);;

let candle_analytic_neg_term child =
  mk_comb (`Candle_analytic_neg`,child);;

let candle_analytic_add_term left right =
  list_mk_comb (`Candle_analytic_add`,[left;right]);;

let candle_analytic_mul_term left right =
  list_mk_comb (`Candle_analytic_mul`,[left;right]);;

let candle_analytic_square_term child =
  mk_comb (`Candle_analytic_square`,child);;

let candle_analytic_inv_term child =
  mk_comb (`Candle_analytic_inv`,child);;

let candle_analytic_q_components q =
  let signed,denominator_predecessor = dest_pair q in
  let positive,negative = dest_pair signed in
  if not (is_numeral positive && is_numeral negative &&
          is_numeral denominator_predecessor) then
    failwith "candle analytic reifier: non-numeral rational enclosure";
  positive,negative,denominator_predecessor;;

let candle_analytic_sqrt_term interval child =
  let lower,upper = dest_pair interval in
  let lp,ln,ld = candle_analytic_q_components lower in
  let up,un,ud = candle_analytic_q_components upper in
  list_mk_comb
    (`Candle_analytic_sqrt`,[lp;ln;ld;up;un;ud;child]);;

let candle_analytic_source_lhs variables ast =
  list_mk_comb
    (`candle_analytic_value`,[mk_list (variables,`:real`);ast]);;

let candle_analytic_finish_source variables ast tm source_th =
  let expected = mk_eq (candle_analytic_source_lhs variables ast,tm) in
  if hyp source_th <> [] || not (aconv (concl source_th) expected) then
    failwith "candle analytic reifier: kernel source theorem mismatch";
  ast,source_th;;

let candle_analytic_unfold_source variables ast child_theorems =
  let unfolded =
    ONCE_REWRITE_CONV[candle_analytic_value_def]
      (candle_analytic_source_lhs variables ast) in
  PURE_REWRITE_RULE child_theorems unfolded;;

let candle_analytic_polynomial_candidate variables tm =
  try
    ignore (candle_poly_ast_of_real_expression variables tm);
    true
  with Failure _ -> false;;

let rec candle_analytic_reify_real_expression_with sqrt_interval variables tm =
  if candle_analytic_polynomial_candidate variables tm then
    let poly,valid_th,poly_source_th,_,_ =
      candle_poly_reify_real_expression variables tm in
    if hyp valid_th <> [] then
      failwith "candle analytic reifier: polynomial validity assumptions";
    let ast = candle_analytic_poly_term poly in
    let lifted =
      TRANS
        (REWRITE_CONV[candle_analytic_value_def]
          (candle_analytic_source_lhs variables ast))
        poly_source_th in
    candle_analytic_finish_source variables ast tm lifted
  else if candle_q_is_unary `(--):real->real` tm then
    let child_tm = candle_q_dest_unary `(--):real->real` tm in
    let child,child_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables child_tm in
    let ast = candle_analytic_neg_term child in
    candle_analytic_finish_source variables ast tm
      (candle_analytic_unfold_source variables ast [child_th])
  else if candle_q_is_binary `(+):real->real->real` tm then
    let left_tm,right_tm =
      candle_q_dest_binary `(+):real->real->real` tm in
    let left,left_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables left_tm in
    let right,right_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables right_tm in
    let ast = candle_analytic_add_term left right in
    candle_analytic_finish_source variables ast tm
      (candle_analytic_unfold_source variables ast [left_th;right_th])
  else if candle_q_is_binary `(-):real->real->real` tm then
    let left_tm,right_tm =
      candle_q_dest_binary `(-):real->real->real` tm in
    let left,left_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables left_tm in
    let right,right_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables right_tm in
    let ast = candle_analytic_add_term left (candle_analytic_neg_term right) in
    let normalized =
      candle_analytic_unfold_source variables ast [left_th;right_th] in
    let source_normalization = REWRITE_CONV[real_sub] tm in
    candle_analytic_finish_source variables ast tm
      (TRANS normalized (SYM source_normalization))
  else if candle_q_is_binary `(*):real->real->real` tm then
    let left_tm,right_tm =
      candle_q_dest_binary `(*):real->real->real` tm in
    let left,left_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables left_tm in
    let right,right_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables right_tm in
    let ast = candle_analytic_mul_term left right in
    candle_analytic_finish_source variables ast tm
      (candle_analytic_unfold_source variables ast [left_th;right_th])
  else if candle_q_is_binary `(/):real->real->real` tm then
    let left_tm,right_tm =
      candle_q_dest_binary `(/):real->real->real` tm in
    let left,left_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables left_tm in
    let right,right_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables right_tm in
    let ast = candle_analytic_mul_term left (candle_analytic_inv_term right) in
    let normalized =
      candle_analytic_unfold_source variables ast [left_th;right_th] in
    let source_normalization = REWRITE_CONV[real_div] tm in
    candle_analytic_finish_source variables ast tm
      (TRANS normalized (SYM source_normalization))
  else if candle_q_is_unary `inv:real->real` tm then
    let child_tm = candle_q_dest_unary `inv:real->real` tm in
    let child,child_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables child_tm in
    let ast = candle_analytic_inv_term child in
    candle_analytic_finish_source variables ast tm
      (candle_analytic_unfold_source variables ast [child_th])
  else if candle_q_is_unary `sqrt:real->real` tm then
    let child_tm = candle_q_dest_unary `sqrt:real->real` tm in
    let child,child_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables child_tm in
    let interval = sqrt_interval tm in
    if type_of interval <>
       `:((num#num)#num)#((num#num)#num)` then
      failwith "candle analytic reifier: bad square-root enclosure type";
    let ast = candle_analytic_sqrt_term interval child in
    candle_analytic_finish_source variables ast tm
      (candle_analytic_unfold_source variables ast [child_th])
  else if candle_q_is_binary `(pow):real->num->real` tm then
    let base_tm,exponent_tm =
      candle_q_dest_binary `(pow):real->num->real` tm in
    let exponent = Num.int_of_num (dest_numeral exponent_tm) in
    if exponent <> 2 then
      failwith "candle analytic reifier: non-polynomial exponent is not two";
    let child,child_th =
      candle_analytic_reify_real_expression_with
        sqrt_interval variables base_tm in
    let ast = candle_analytic_square_term child in
    let normalized =
      candle_analytic_unfold_source variables ast [child_th] in
    let source_normalization = REWRITE_CONV[REAL_POW_2] tm in
    candle_analytic_finish_source variables ast tm
      (TRANS normalized (SYM source_normalization))
  else
    failwith "candle analytic reifier: unsupported real expression";;

let candle_analytic_reify_real_expression sqrt_interval variables tm =
  if exists (fun variable -> type_of variable <> `:real`) variables then
    failwith "candle analytic reifier: non-real variable basis";
  if type_of tm <> `:real` then
    failwith "candle analytic reifier: expression is not real";
  candle_analytic_reify_real_expression_with
    sqrt_interval variables tm;;

end;;
