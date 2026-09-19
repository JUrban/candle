(* ========================================================================== *)
(* Proof-producing adapter from authenticated inequalities to an exact fold. *)
(*                                                                            *)
(* Callers supply theorem-producing reifiers for each real lhs/rhs. The       *)
(* adapter proves that the exact rows denote the original inequalities, uses  *)
(* the generic bulk soundness theorem, evaluates the exact fold with          *)
(* Kernel.compute, and returns the resulting ordinary HOL inequality.         *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination.ml";;
needs "candle/cv_compute_linear_combination_bulk.ml";;
needs "candle/cv_compute_linear_combination_realize.ml";;

module Candle_cv_linear_combination_adapter = struct

open Candle_cv_linear_combination;;
open Candle_cv_linear_combination_bulk;;
open Candle_cv_linear_combination_realize;;

let candle_lc_exact_row_type = `:num#((num#num)list#(num#num))`;;
let candle_lc_zero_acc = `([]:(num#num)list),(0,0)`;;
let candle_lc_row_map_const =
  rator
    (rator
      `MAP (candle_lc_row_real ([]:real list))
         ([]:(num#((num#num)list#(num#num)))list)`);;

let candle_lc_pair_rule left_th right_th =
  let left_lhs,_ = dest_eq (concl left_th) and
      right_lhs,_ = dest_eq (concl right_th) in
  let pair_const = rator (rator (mk_pair (left_lhs,right_lhs))) in
  MK_COMB (AP_TERM pair_const left_th,right_th);;

let candle_lc_check_reification label expected_lhs expected_rhs th =
  if hyp th <> [] ||
     not (aconv (concl th) (mk_eq (expected_lhs,expected_rhs))) then
    failwith ("candle_lc adapter: invalid " ^ label ^ " reification");;

let candle_lc_reify_row variables_tm reify_lhs reify_rhs
      (inequality,weight) =
  let raw_row = candle_lc_row_of_inequality weight inequality in
  let lhs,rhs = dest_binop `(<=):real->real->bool` (concl inequality) in
  let coefficients,lhs_th = reify_lhs lhs in
  let integer,rhs_th = reify_rhs rhs in
  let exact_lhs =
    mk_comb (mk_comb (`candle_lc_vec_real`,variables_tm),coefficients) in
  let exact_rhs = mk_comb (`candle_lc_zreal`,integer) in
  let _ =
    candle_lc_check_reification "lhs" exact_lhs lhs lhs_th;
    candle_lc_check_reification "rhs" exact_rhs rhs rhs_th in
  let exact_row = mk_pair (weight,mk_pair (coefficients,integer)) in
  let row_real_tm =
    mk_comb (mk_comb (`candle_lc_row_real`,variables_tm),exact_row) in
  let row_expansion =
    REWRITE_CONV[candle_lc_row_real_def] row_real_tm in
  let row_contents =
    candle_lc_pair_rule (REFL weight)
      (candle_lc_pair_rule lhs_th rhs_th) in
  let row_th = TRANS row_expansion row_contents in
  if not (aconv (rand (concl row_th)) raw_row) then
    failwith "candle_lc adapter: row denotation mismatch";
  exact_row,raw_row,row_th;;

let candle_lc_reify_rows variables reify_lhs reify_rhs
      weighted_inequalities =
  let variables_tm = mk_list (variables,`:real`) in
  let rows =
    map
      (candle_lc_reify_row variables_tm reify_lhs reify_rhs)
      weighted_inequalities in
  let exact_rows = mk_list (map (fun (row,_,_) -> row) rows,
                                candle_lc_exact_row_type) in
  let raw_rows = mk_list (map (fun (_,row,_) -> row) rows,
                              candle_lc_real_row_type) in
  let row_ths = map (fun (_,_,th) -> th) rows in
  let row_real_fun = mk_comb (`candle_lc_row_real`,variables_tm) in
  let map_tm =
    mk_comb (mk_comb (candle_lc_row_map_const,row_real_fun),exact_rows) in
  let map_th = REWRITE_CONV (MAP::row_ths) map_tm in
  if not (aconv (rand (concl map_th)) raw_rows) then
    failwith "candle_lc adapter: row-list denotation mismatch";
  variables_tm,exact_rows,map_th;;

let candle_lc_zero_acc_real_conv variables_tm =
  let tm =
    mk_comb
      (mk_comb (`candle_lc_acc_real`,variables_tm),candle_lc_zero_acc) in
  let th =
    REWRITE_CONV
      [candle_lc_acc_real_def; candle_lc_vec_real_def;
       candle_lc_zreal_def; REAL_SUB_REFL] tm in
  if not (aconv (rand (concl th)) `(&0,&0)`) then
    failwith "candle_lc adapter: zero accumulator mismatch";
  th;;

let candle_lc_bulk_compute_with
      variables reify_lhs reify_rhs weighted_inequalities =
  let variables_tm,exact_rows,row_map_th =
    candle_lc_reify_rows
      variables reify_lhs reify_rhs weighted_inequalities in
  let bulk_th = candle_lc_bulk_inequality weighted_inequalities in
  let zero_acc_th = candle_lc_zero_acc_real_conv variables_tm in
  let exact_bulk_th =
    REWRITE_RULE[SYM row_map_th; SYM zero_acc_th] bulk_th in
  let realization_th =
    SPECL [exact_rows;variables_tm;candle_lc_zero_acc]
      candle_lc_fold_real in
  let realized_bulk_th = REWRITE_RULE[realization_th] exact_bulk_th in
  let fold_th = candle_cv_lc_fold_conv candle_lc_zero_acc exact_rows in
  let result = rand (concl fold_th) in
  let coefficients,integer = dest_pair result in
  let computed_bulk_th =
    REWRITE_RULE
      [fold_th; candle_lc_acc_real_def]
      realized_bulk_th in
  let expected_conclusion =
    mk_binop `(<=):real->real->bool`
      (mk_comb (mk_comb (`candle_lc_vec_real`,variables_tm),coefficients))
      (mk_comb (`candle_lc_zreal`,integer)) in
  if not (aconv (concl computed_bulk_th) expected_conclusion) then
    failwith "candle_lc adapter: computed conclusion mismatch";
  result,computed_bulk_th;;

end;;
