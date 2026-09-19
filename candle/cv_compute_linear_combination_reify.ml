(* ========================================================================== *)
(* Strict, theorem-producing reification of normalized linear functions.     *)
(*                                                                            *)
(* The caller supplies the linear-function constant and its defining theorem *)
(* so this layer is testable independently of Flyspeck's load order. The      *)
(* returned coefficient vector is useful only together with the returned HOL *)
(* equality; untrusted ML parsing alone never authorizes a theorem.           *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination_realize.ml";;

module Candle_cv_linear_combination_reify = struct

open Candle_cv_linear_combination_realize;;

let candle_lc_num_zero = num 0;;
let candle_lc_zero_tm = mk_numeral candle_lc_num_zero;;
let candle_lc_z_type = `:num#num`;;

let candle_lc_z_term n =
  if n >=/ candle_lc_num_zero then
    mk_pair (mk_numeral n,candle_lc_zero_tm)
  else
    mk_pair (candle_lc_zero_tm,mk_numeral (minus_num n));;

let rec candle_lc_strictly_sorted less = function
  | [] | [_] -> true
  | x::(y::_ as rest) -> less x y && candle_lc_strictly_sorted less rest;;

let candle_lc_check_variables less variables =
  if not (candle_lc_strictly_sorted less variables) then
    failwith "candle_lc reifier: variable basis is not strictly sorted";
  if exists (fun variable -> type_of variable <> `:real`) variables then
    failwith "candle_lc reifier: non-real variable basis";;

let candle_lc_dest_entries lin_f_const dest_integer lhs =
  let head,terms_tm = dest_comb lhs in
  if head <> lin_f_const then
    failwith "candle_lc reifier: expected normalized lin_f";
  map
    (fun entry ->
       let coefficient,variable = dest_pair entry in
       coefficient,variable,dest_integer coefficient)
    (dest_list terms_tm);;

let candle_lc_check_entries less variables entries =
  let entry_variables = map (fun (_,variable,_) -> variable) entries in
  if not (candle_lc_strictly_sorted less entry_variables) then
    failwith "candle_lc reifier: lin_f variables are not strictly sorted";
  if exists (fun variable -> not (mem variable variables)) entry_variables then
    failwith "candle_lc reifier: lin_f variable is outside the basis";;

let rec candle_lc_lookup_coefficient variable = function
  | [] -> candle_lc_num_zero
  | (_,candidate,coefficient)::rest ->
      if candidate = variable then coefficient
      else candle_lc_lookup_coefficient variable rest;;

let candle_lc_normalize_conv lin_f_def extra_rewrites tm =
  REWRITE_CONV
    (extra_rewrites @
     [lin_f_def; ITLIST;
      candle_lc_vec_real_def; candle_lc_zreal_def;
      REAL_SUB_RZERO; REAL_SUB_LZERO; REAL_NEG_0;
      REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID]) tm;;

let candle_lc_reify_lin_f_with
      less lin_f_const lin_f_def dest_integer extra_rewrites variables lhs =
  candle_lc_check_variables less variables;
  let entries = candle_lc_dest_entries lin_f_const dest_integer lhs in
  candle_lc_check_entries less variables entries;
  let coefficients =
    map
      (fun variable ->
         candle_lc_z_term
           (candle_lc_lookup_coefficient variable entries))
      variables in
  let variables_tm = mk_list (variables,`:real`) in
  let coefficients_tm = mk_list (coefficients,candle_lc_z_type) in
  let exact_tm =
    mk_comb
      (mk_comb (`candle_lc_vec_real`,variables_tm),coefficients_tm) in
  let exact_th =
    candle_lc_normalize_conv lin_f_def extra_rewrites exact_tm in
  let source_th =
    candle_lc_normalize_conv lin_f_def extra_rewrites lhs in
  if not (aconv (rand (concl exact_th)) (rand (concl source_th))) then
    failwith "candle_lc reifier: denotation normalization mismatch";
  coefficients_tm,TRANS exact_th (SYM source_th);;

let candle_lc_reify_integer_with
      lin_f_def dest_integer extra_rewrites integer_tm =
  let z_tm = candle_lc_z_term (dest_integer integer_tm) in
  let exact_tm = mk_comb (`candle_lc_zreal`,z_tm) in
  let exact_th =
    candle_lc_normalize_conv lin_f_def extra_rewrites exact_tm in
  let source_th =
    candle_lc_normalize_conv lin_f_def extra_rewrites integer_tm in
  if not (aconv (rand (concl exact_th)) (rand (concl source_th))) then
    failwith "candle_lc reifier: integer normalization mismatch";
  z_tm,TRANS exact_th (SYM source_th);;

end;;
