(* ========================================================================== *)
(* Theorem-producing reification from real polynomial terms to the AST.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  ML selects an AST, but the selection carries  *)
(* no authority: the exported theorem proves that its dimension-parametric   *)
(* denotation is exactly the original HOL term.                               *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_reify.ml";;
needs "candle/cv_compute_polynomial_expr_jet.ml";;

module Candle_cv_polynomial_expr_reify = struct

open Candle_cv_exact_interval_reify;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;

let candle_poly_const_term rational =
  let signed,denominator_predecessor =
    dest_pair (candle_q_term rational) in
  let positive,negative = dest_pair signed in
  list_mk_comb
    (`Candle_poly_const`,
     [positive;negative;denominator_predecessor]);;

let candle_poly_var_term index =
  mk_comb (`Candle_poly_var`,mk_numeral (Num.num_of_int index));;

let candle_poly_neg_term child =
  mk_comb (`Candle_poly_neg`,child);;

let candle_poly_add_term left right =
  list_mk_comb (`Candle_poly_add`,[left;right]);;

let candle_poly_mul_term left right =
  list_mk_comb (`Candle_poly_mul`,[left;right]);;

let candle_poly_square_term child =
  mk_comb (`Candle_poly_square`,child);;

let rec candle_poly_repeat_ast base count =
  if count = 0 then candle_poly_const_term (Num.num_of_int 1)
  else if count = 1 then base
  else if count = 2 then candle_poly_square_term base
  else candle_poly_mul_term (candle_poly_repeat_ast base (count - 1)) base;;

let rec candle_poly_ast_of_real_expression variables tm =
  match candle_q_variable_index variables tm with
  | Some index -> candle_poly_var_term index
  | None ->
      if is_ratconst tm then candle_poly_const_term (rat_of_term tm)
      else if candle_q_is_unary `(--):real->real` tm then
        candle_poly_neg_term
          (candle_poly_ast_of_real_expression variables
            (candle_q_dest_unary `(--):real->real` tm))
      else if candle_q_is_binary `(+):real->real->real` tm then
        let left,right =
          candle_q_dest_binary `(+):real->real->real` tm in
        candle_poly_add_term
          (candle_poly_ast_of_real_expression variables left)
          (candle_poly_ast_of_real_expression variables right)
      else if candle_q_is_binary `(-):real->real->real` tm then
        let left,right =
          candle_q_dest_binary `(-):real->real->real` tm in
        candle_poly_add_term
          (candle_poly_ast_of_real_expression variables left)
          (candle_poly_neg_term
            (candle_poly_ast_of_real_expression variables right))
      else if candle_q_is_binary `(*):real->real->real` tm then
        let left,right =
          candle_q_dest_binary `(*):real->real->real` tm in
        candle_poly_mul_term
          (candle_poly_ast_of_real_expression variables left)
          (candle_poly_ast_of_real_expression variables right)
      else if candle_q_is_binary `(pow):real->num->real` tm then
        let base_tm,exponent_tm =
          candle_q_dest_binary `(pow):real->num->real` tm in
        let exponent = Num.int_of_num (dest_numeral exponent_tm) in
        if exponent < 0 || exponent > 16 then
          failwith "candle polynomial reifier: exponent is outside 0..16";
        candle_poly_repeat_ast
          (candle_poly_ast_of_real_expression variables base_tm) exponent
      else
        failwith "candle polynomial reifier: unsupported real expression";;

let candle_poly_reify_real_expression variables tm =
  if exists (fun variable -> type_of variable <> `:real`) variables then
    failwith "candle polynomial reifier: non-real variable basis";
  if type_of tm <> `:real` then
    failwith "candle polynomial reifier: expression is not real";
  let ast_tm = candle_poly_ast_of_real_expression variables tm in
  let nvars_tm = mk_numeral (Num.num_of_int (length variables)) in
  let valid_goal =
    list_mk_comb (`candle_poly_valid_dim`,[nvars_tm;ast_tm]) in
  let valid_eq =
    (REWRITE_CONV[candle_poly_valid_dim_def] THENC NUM_REDUCE_CONV)
      valid_goal in
  let valid_th = EQT_ELIM valid_eq in
  let program_tm,real_run_th =
    candle_q_reify_real_expression variables tm in
  let compile_tm = mk_comb (`candle_poly_compile`,ast_tm) in
  let compile_th =
    REWRITE_CONV[candle_poly_compile_def; APPEND] compile_tm in
  let compiled_program = rand (concl compile_th) in
  if not (aconv compiled_program program_tm) then
    failwith "candle polynomial reifier: compiler program mismatch";
  let variables_tm = mk_list (variables,`:real`) in
  let ast_run_th =
    SPECL [ast_tm;variables_tm] candle_poly_compile_real_program in
  let ast_run_th = PURE_REWRITE_RULE[compile_th] ast_run_th in
  if not (aconv (lhand (concl ast_run_th))
                 (lhand (concl real_run_th))) then
    failwith "candle polynomial reifier: execution lhs mismatch";
  let source_th =
    REWRITE_RULE[CONS_11] (TRANS (SYM ast_run_th) real_run_th) in
  let expected_source =
    mk_eq
      (list_mk_comb
        (`candle_poly_value_list`,[variables_tm;ast_tm]),
       tm) in
  if hyp valid_th <> [] || hyp source_th <> [] ||
     not (aconv (concl source_th) expected_source) then
    failwith "candle polynomial reifier: kernel source theorem mismatch";
  ast_tm,valid_th,source_th,program_tm,real_run_th;;

end;;
