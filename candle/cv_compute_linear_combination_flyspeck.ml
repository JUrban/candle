(* ========================================================================== *)
(* Flyspeck instantiation of the exact linear-function reifier.               *)
(*                                                                            *)
(* Load only after Flyspeck's lin_f, Arith_num, and Arith_int modules. The   *)
(* generic reifier remains responsible for constructing a kernel equality;    *)
(* these wrappers select the exact source representation used by the checker. *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination_reify.ml";;
needs "candle/cv_compute_linear_combination_adapter.ml";;

module Candle_cv_linear_combination_flyspeck = struct

open Candle_cv_linear_combination_reify;;
open Candle_cv_linear_combination_adapter;;

let candle_lc_flyspeck_zero = num 0;;

let candle_lc_flyspeck_lin_f_const = `lin_f`;;
let candle_lc_flyspeck_rewrites = [];;

let candle_lc_flyspeck_standardize_numerals tm =
  DEPTH_CONV Arith_nat.NUM_TO_NUMERAL_CONV tm;;

let candle_lc_reify_flyspeck_lin_f variables lhs =
  let standardize_th = candle_lc_flyspeck_standardize_numerals lhs in
  let standard_lhs = rand (concl standardize_th) in
  let coefficients,standard_th =
    candle_lc_reify_lin_f_with
      Term.(<)
      candle_lc_flyspeck_lin_f_const
      Linear_function.lin_f
      dest_realintconst
      candle_lc_flyspeck_rewrites
      variables standard_lhs in
  coefficients,TRANS standard_th (SYM standardize_th);;

let candle_lc_reify_flyspeck_integer integer_tm =
  let standardize_th =
    candle_lc_flyspeck_standardize_numerals integer_tm in
  let standard_integer = rand (concl standardize_th) in
  let integer,standard_th =
    candle_lc_reify_integer_with
      Linear_function.lin_f
      dest_realintconst
      candle_lc_flyspeck_rewrites
      standard_integer in
  integer,TRANS standard_th (SYM standardize_th);;

let candle_lc_dest_canonical_z z_tm =
  let positive_tm,negative_tm = dest_pair z_tm in
  let positive = dest_numeral positive_tm and
      negative = dest_numeral negative_tm in
  if positive =/ candle_lc_flyspeck_zero then minus_num negative
  else if negative =/ candle_lc_flyspeck_zero then positive
  else failwith "Flyspeck adapter: noncanonical signed pair";;

let candle_lc_render_flyspeck_z z_tm =
  Arith_int.my_mk_realintconst (candle_lc_dest_canonical_z z_tm);;

let candle_lc_render_flyspeck_lin_f variables coefficients_tm =
  let coefficients = dest_list coefficients_tm in
  let rec render_entries vars coeffs =
    match vars,coeffs with
    | [],[] -> []
    | variable::vars_tail,coefficient::coeffs_tail ->
        let rest = render_entries vars_tail coeffs_tail in
        let integer = candle_lc_dest_canonical_z coefficient in
        if integer =/ candle_lc_flyspeck_zero then rest
        else mk_pair (Arith_int.my_mk_realintconst integer,variable) :: rest
    | _ -> failwith "Flyspeck adapter: coefficient/basis length mismatch" in
  let entries = render_entries variables coefficients in
  mk_comb
    (candle_lc_flyspeck_lin_f_const,mk_list (entries,`:real#real`));;

let candle_lc_publicize_flyspeck variables result exact_th =
  let variables_tm = mk_list (variables,`:real`) in
  let coefficients,integer = dest_pair result in
  let public_lhs =
    candle_lc_render_flyspeck_lin_f variables coefficients in
  let public_rhs = candle_lc_render_flyspeck_z integer in
  let checked_coefficients,lhs_th =
    candle_lc_reify_flyspeck_lin_f variables public_lhs in
  let checked_integer,rhs_th =
    candle_lc_reify_flyspeck_integer public_rhs in
  if not (aconv checked_coefficients coefficients) ||
     not (aconv checked_integer integer) then
    failwith "Flyspeck adapter: public rendering did not reify exactly";
  let expected_exact =
    mk_binop `(<=):real->real->bool`
      (mk_comb
        (mk_comb (`candle_lc_vec_real`,variables_tm),coefficients))
      (mk_comb (`candle_lc_zreal`,integer)) in
  if not (aconv (concl exact_th) expected_exact) then
    failwith "Flyspeck adapter: exact conclusion mismatch";
  let public_eq =
    MK_COMB (AP_TERM `(<=):real->real->bool` lhs_th,rhs_th) in
  let public_th = EQ_MP public_eq exact_th in
  let expected_public =
    mk_binop `(<=):real->real->bool` public_lhs public_rhs in
  if not (aconv (concl public_th) expected_public) then
    failwith "Flyspeck adapter: public conclusion mismatch";
  public_th;;

let candle_lc_bulk_compute_flyspeck variables weighted_inequalities =
  let result,exact_th =
    candle_lc_bulk_compute_with
      variables
      (candle_lc_reify_flyspeck_lin_f variables)
      candle_lc_reify_flyspeck_integer
      weighted_inequalities in
  result,candle_lc_publicize_flyspeck variables result exact_th;;

let candle_lc_normalize_flyspeck_inequality normalize_lhs inequality =
  let lhs,rhs =
    dest_binop `(<=):real->real->bool` (concl inequality) in
  let lhs_th = normalize_lhs lhs in
  let normalized_source,_ = dest_eq (concl lhs_th) in
  if hyp lhs_th <> [] || normalized_source <> lhs then
    failwith "Flyspeck adapter: invalid lhs normalization theorem";
  let normalized =
    EQ_MP
      (AP_THM (AP_TERM `(<=):real->real->bool` lhs_th) rhs)
      inequality in
  if not (set_eq (hyp normalized) (hyp inequality)) then
    failwith "Flyspeck adapter: normalization changed hypotheses";
  normalized;;

let candle_lc_flyspeck_lhs_variables inequality =
  let lhs,_ = dest_binop `(<=):real->real->bool` (concl inequality) in
  let head,entries_tm = dest_comb lhs in
  if head <> candle_lc_flyspeck_lin_f_const then
    failwith "Flyspeck adapter: normalized lhs is not lin_f";
  map (fun entry -> snd (dest_pair entry)) (dest_list entries_tm);;

let candle_lc_bulk_compute_flyspeck_source
      normalize_lhs weighted_inequalities =
  let normalized =
    map
      (fun (inequality,weight) ->
         candle_lc_normalize_flyspeck_inequality
           normalize_lhs inequality,weight)
      weighted_inequalities in
  let variables =
    setify Term.(<)
      (List.flatten
        (map
          (fun (inequality,_) ->
             candle_lc_flyspeck_lhs_variables inequality)
          normalized)) in
  let result,computed_th =
    candle_lc_bulk_compute_flyspeck variables normalized in
  variables,result,computed_th;;

let candle_lc_flyspeck_final_inequality =
  Arith_nat.NUMERALS_TO_NUM
    (prove
      (`!n. lin_f [] <= -- &n <=> n = 0`,
       REWRITE_TAC
         [Linear_function.LIN_F_EMPTY; REAL_NEG_GE0; REAL_OF_NUM_LE; LE]));;

let candle_lc_all_zero_coefficients coefficients_tm =
  List.for_all
    (fun coefficient_tm ->
       let positive_tm,negative_tm = dest_pair coefficient_tm in
       dest_numeral positive_tm =/ candle_lc_flyspeck_zero &&
       dest_numeral negative_tm =/ candle_lc_flyspeck_zero)
    (dest_list coefficients_tm);;

let candle_lc_bulk_refute_flyspeck_source
      normalize_lhs weighted_inequalities =
  let variables,result,aggregate =
    candle_lc_bulk_compute_flyspeck_source
      normalize_lhs weighted_inequalities in
  let coefficients_tm,integer_tm = dest_pair result in
  let positive_tm,negative_tm = dest_pair integer_tm in
  let positive = dest_numeral positive_tm and
      negative = dest_numeral negative_tm in
  if not (candle_lc_all_zero_coefficients coefficients_tm) ||
     not (positive =/ candle_lc_flyspeck_zero) ||
     negative =/ candle_lc_flyspeck_zero then
    failwith "Flyspeck adapter: aggregate is not a strict contradiction";
  let lhs,rhs = dest_binop `(<=):real->real->bool` (concl aggregate) in
  let expected_lhs =
    candle_lc_render_flyspeck_lin_f variables coefficients_tm and
      expected_rhs = candle_lc_render_flyspeck_z integer_tm in
  if not (aconv lhs expected_lhs) || not (aconv rhs expected_rhs) then
    failwith "Flyspeck adapter: public contradiction shape mismatch";
  let n_tm = rand (Arith_int.my_mk_realintconst negative) in
  let final_iff = SPEC n_tm candle_lc_flyspeck_final_inequality in
  let zero_th = Arith_nat.NUM_EQ0_HASH_CONV n_tm in
  let contradiction = EQ_MP final_iff aggregate in
  variables,result,EQ_MP zero_th contradiction;;

let candle_lc_flyspeck_weight_term weight =
  if weight </ candle_lc_flyspeck_zero then
    failwith "Flyspeck adapter: negative certificate multiplier"
  else mk_numeral weight;;

let candle_lc_bulk_refute_flyspeck_terminal
      normalize_lhs precision_constant constraint_inequalities
      auxiliary_inequalities =
  if precision_constant <=/ candle_lc_flyspeck_zero then
    failwith "Flyspeck adapter: nonpositive precision multiplier";
  let scaled_constraints =
    map
      (fun (inequality,weight) ->
         inequality,
         candle_lc_flyspeck_weight_term (precision_constant */ weight))
      constraint_inequalities and
      auxiliaries =
    map
      (fun (inequality,weight) ->
         inequality,candle_lc_flyspeck_weight_term weight)
      auxiliary_inequalities in
  candle_lc_bulk_refute_flyspeck_source
    normalize_lhs (scaled_constraints @ auxiliaries);;

end;;
