(* ========================================================================== *)
(* Theorem-producing Flyspeck vector adapter for polynomial reification.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The ML reifier chooses an AST, but the result  *)
(* is authorized only by an assumption-free kernel equality from the          *)
(* dimension-generic reflected denotation to the original real^N expression.  *)
(* ========================================================================== *)

needs "candle/cv_compute_polynomial_expr_reify.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_dim_bridge.ml";;

module Candle_cv_polynomial_expr_flyspeck_reify = struct

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_flyspeck_dim_bridge;;
open Candle_cv_polynomial_expr_reify;;

let candle_poly_value_list_denote_dim = prove
 (`!e (z:real^N).
     candle_poly_valid_dim (dimindex (:N)) e
     ==>
     candle_poly_value_list
       (list_of_seq (\k. z$(k + 1)) (dimindex (:N))) e =
     candle_poly_denote_dim e z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_poly_denote_dim_def] THEN
  MATCH_MP_TAC candle_poly_value_list_fun THEN
  ASM_REWRITE_TAC[]);;

let candle_poly_vector_components vector dimension =
  let component = mk_icomb (`$`,vector) in
  map
    (fun index -> mk_comb (component,mk_small_numeral index))
    (1--dimension);;

let candle_poly_reify_vector_expression vector source =
  let vector_type = type_of vector in
  let vector_constructor,vector_arguments = dest_type vector_type in
  if vector_constructor <> "cart" || length vector_arguments <> 2 ||
     hd vector_arguments <> `:real` then
    failwith "Candle Flyspeck polynomial reifier: expected a real vector";
  let index_type = List.nth vector_arguments 1 in
  let dimension_theorem =
    DIMINDEX_CONV (inst [index_type,`:N`] `dimindex (:N)`) in
  let dimension = dest_small_numeral (rand (concl dimension_theorem)) in
  if dimension <= 0 then
    failwith "Candle Flyspeck polynomial reifier: empty vector dimension";
  let variables = candle_poly_vector_components vector dimension in
  let ast,valid,source_th,program,run_th =
    candle_poly_reify_real_expression variables source in
  let index = `k:num` in
  let environment =
    mk_abs
      (index,
       mk_comb
         (mk_icomb (`$`,vector),
          mk_binop `(+):num->num->num` index `1`)) in
  let list_value =
    MATCH_MP
      (SPECL [ast;mk_small_numeral dimension;environment]
        candle_poly_value_list_fun)
      valid in
  let list_value_expanded =
    CONV_RULE
      (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV)
      list_value in
  let list_value_beta =
    CONV_RULE (DEPTH_CONV BETA_CONV) list_value_expanded in
  let list_value =
    CONV_RULE (DEPTH_CONV NUM_ADD_CONV) list_value_beta in
  if not (aconv (lhand (concl list_value))
                 (lhand (concl source_th))) then
    failwith
      "Candle Flyspeck polynomial reifier: vector source list mismatch";
  let denotation_term =
    mk_icomb (mk_icomb (`candle_poly_denote_dim`,ast),vector) in
  let denotation_th =
    REWRITE_CONV [candle_poly_denote_dim_def] denotation_term in
  if not (aconv (rand (concl denotation_th))
                 (rand (concl list_value))) then
    failwith
      "Candle Flyspeck polynomial reifier: vector environment mismatch";
  let source_denotation =
    TRANS denotation_th (TRANS (SYM list_value) source_th) in
  let expected =
    mk_eq (denotation_term,source) in
  if hyp source_denotation <> [] ||
     not (aconv (concl source_denotation) expected) then
    failwith
      "Candle Flyspeck polynomial reifier: vector theorem mismatch";
  ast,valid,source_denotation,program,run_th;;

end;;
