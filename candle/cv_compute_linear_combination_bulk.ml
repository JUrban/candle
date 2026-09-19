(* ========================================================================== *)
(* Bulk theorem bridge for exact nonnegative linear combinations.             *)
(*                                                                            *)
(* This deliberately stops before coefficient-vector normalization. It turns  *)
(* authenticated inequalities into one application of the generic fold       *)
(* soundness theorem, avoiding the old theorem-per-addition construction.     *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination_sound.ml";;

module Candle_cv_linear_combination_bulk = struct

open Candle_cv_linear_combination_sound;;

let candle_lc_real_row_type = `:num#(real#real)`;;

let candle_lc_row_of_inequality weight ineq =
  if type_of weight <> `:num` then
    failwith "candle_lc_row_of_inequality: weight is not a natural";
  let lhs,rhs = dest_binop `(<=):real->real->bool` (concl ineq) in
  mk_pair (weight,mk_pair (lhs,rhs));;

let candle_lc_row_holds_rule row ineq =
  let row_holds = mk_comb (`candle_lc_real_row_holds`,row) in
  let row_holds_eq =
    REWRITE_CONV[candle_lc_real_row_holds_def] row_holds in
  EQ_MP (SYM row_holds_eq) ineq;;

let candle_lc_all_rows_rule rows_and_theorems =
  let all_rows rows = mk_comb (`ALL candle_lc_real_row_holds`,rows) in
  let empty_rows = mk_list ([],candle_lc_real_row_type) in
  let empty_all = all_rows empty_rows in
  let empty_eq = ONCE_REWRITE_CONV[ALL] empty_all in
  let empty_th = EQ_MP (SYM empty_eq) TRUTH in
  List.fold_right
    (fun (row,row_th) (tail,tail_th) ->
       let rows = mk_cons row tail in
       let all_eq = ONCE_REWRITE_CONV[ALL] (all_rows rows) in
       rows,EQ_MP (SYM all_eq) (CONJ row_th tail_th))
    rows_and_theorems (empty_rows,empty_th);;

let candle_lc_bulk_inequality weighted_inequalities =
  let rows_and_theorems =
    map
      (fun (ineq,weight) ->
         let row = candle_lc_row_of_inequality weight ineq in
         row,candle_lc_row_holds_rule row ineq)
      weighted_inequalities in
  let rows,all_th = candle_lc_all_rows_rule rows_and_theorems in
  MATCH_MP (SPEC rows candle_lc_real_fold_from_zero) all_th;;

end;;
