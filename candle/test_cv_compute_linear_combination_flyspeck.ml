(* Run after direct Flyspeck actions 179 and 180 have loaded lin_f/arith_int. *)

needs "candle/compute.ml";;
needs "candle/cv_compute_linear_combination_flyspeck.ml";;

open Candle_cv_linear_combination_reify;;
open Candle_cv_linear_combination_flyspeck;;

let candle_cv_lc_flyspeck_axioms = axioms ();;
let candle_cv_lc_flyspeck_variables = [`x:real`; `y:real`; `z:real`];;
let candle_cv_lc_flyspeck_two = Arith_int.my_mk_realintconst (num 2);;
let candle_cv_lc_flyspeck_neg_three =
  Arith_int.my_mk_realintconst (minus_num (num 3));;
let candle_cv_lc_flyspeck_terms =
  mk_list
    ([mk_pair (candle_cv_lc_flyspeck_two,`x:real`);
      mk_pair (candle_cv_lc_flyspeck_neg_three,`z:real`)],
     `:real#real`);;
let candle_cv_lc_flyspeck_lhs =
  mk_comb (`lin_f`,candle_cv_lc_flyspeck_terms);;
let candle_cv_lc_flyspeck_coefficients,candle_cv_lc_flyspeck_th =
  candle_lc_reify_flyspeck_lin_f
    candle_cv_lc_flyspeck_variables candle_cv_lc_flyspeck_lhs;;

if not (aconv candle_cv_lc_flyspeck_coefficients
              `[(2,0);(0,0);(0,3)]`) ||
   hyp candle_cv_lc_flyspeck_th <> [] ||
   not (aconv (concl candle_cv_lc_flyspeck_th)
         (mk_eq
           (mk_comb
             (mk_comb
               (`candle_lc_vec_real`,
                mk_list (candle_cv_lc_flyspeck_variables,`:real`)),
              candle_cv_lc_flyspeck_coefficients),
            candle_cv_lc_flyspeck_lhs))) then
  failwith "Flyspeck linear-function reification mismatch";;

let candle_cv_lc_flyspeck_integer,candle_cv_lc_flyspeck_integer_th =
  candle_lc_reify_flyspeck_integer candle_cv_lc_flyspeck_neg_three;;
if not (aconv candle_cv_lc_flyspeck_integer `(0,3)`) ||
   hyp candle_cv_lc_flyspeck_integer_th <> [] ||
   not (aconv (concl candle_cv_lc_flyspeck_integer_th)
         (mk_eq
           (mk_comb (`candle_lc_zreal`,candle_cv_lc_flyspeck_integer),
            candle_cv_lc_flyspeck_neg_three))) then
  failwith "Flyspeck integer reification mismatch";;

let candle_cv_lc_flyspeck_one = Arith_int.my_mk_realintconst (num 1);;
let candle_cv_lc_flyspeck_seven = Arith_int.my_mk_realintconst (num 7);;
let candle_cv_lc_flyspeck_neg_one =
  Arith_int.my_mk_realintconst (minus_num (num 1));;
let candle_cv_lc_flyspeck_lhs2 =
  mk_comb
    (`lin_f`,mk_list ([mk_pair (candle_cv_lc_flyspeck_one,`y:real`)],
                       `:real#real`));;
let candle_cv_lc_flyspeck_ineq1 =
  ASSUME
    (mk_binop `(<=):real->real->bool`
      candle_cv_lc_flyspeck_lhs candle_cv_lc_flyspeck_seven);;
let candle_cv_lc_flyspeck_ineq2 =
  ASSUME
    (mk_binop `(<=):real->real->bool`
      candle_cv_lc_flyspeck_lhs2 candle_cv_lc_flyspeck_neg_one);;
let candle_cv_lc_flyspeck_result,candle_cv_lc_flyspeck_public_th =
  candle_lc_bulk_compute_flyspeck
    candle_cv_lc_flyspeck_variables
    [(candle_cv_lc_flyspeck_ineq1,`3`);
     (candle_cv_lc_flyspeck_ineq2,`4`)];;
let candle_cv_lc_flyspeck_expected_lhs =
  candle_lc_render_flyspeck_lin_f
    candle_cv_lc_flyspeck_variables
    `[(6,0);(4,0);(0,9)]`;;
let candle_cv_lc_flyspeck_expected_rhs =
  candle_lc_render_flyspeck_z `(17,0)`;;
if not (aconv candle_cv_lc_flyspeck_result
              `([(6,0);(4,0);(0,9)],(17,0))`) ||
   not (set_eq (hyp candle_cv_lc_flyspeck_public_th)
          [concl candle_cv_lc_flyspeck_ineq1;
           concl candle_cv_lc_flyspeck_ineq2]) ||
   not (aconv (concl candle_cv_lc_flyspeck_public_th)
         (mk_binop `(<=):real->real->bool`
           candle_cv_lc_flyspeck_expected_lhs
           candle_cv_lc_flyspeck_expected_rhs)) then
  failwith "Flyspeck public linear-combination adapter mismatch";;

let candle_cv_lc_flyspeck_raw_lhs1 =
  mk_binop `(+):real->real->real`
    (mk_binop `(*):real->real->real`
      candle_cv_lc_flyspeck_two `x:real`)
    (mk_binop `(*):real->real->real`
      candle_cv_lc_flyspeck_neg_three `z:real`);;
let candle_cv_lc_flyspeck_raw_lhs2 =
  mk_binop `(*):real->real->real`
    candle_cv_lc_flyspeck_one `y:real`;;
let candle_cv_lc_flyspeck_raw_ineq1 =
  ASSUME
    (mk_binop `(<=):real->real->bool`
      candle_cv_lc_flyspeck_raw_lhs1 candle_cv_lc_flyspeck_seven);;
let candle_cv_lc_flyspeck_raw_ineq2 =
  ASSUME
    (mk_binop `(<=):real->real->bool`
      candle_cv_lc_flyspeck_raw_lhs2 candle_cv_lc_flyspeck_neg_one);;
let candle_cv_lc_flyspeck_normalize_lhs lhs =
  let normalized =
    if aconv lhs candle_cv_lc_flyspeck_raw_lhs1 then
      candle_cv_lc_flyspeck_lhs
    else if aconv lhs candle_cv_lc_flyspeck_raw_lhs2 then
      candle_cv_lc_flyspeck_lhs2
    else failwith "unexpected source-normalization test lhs" in
  let normalized_th =
    REWRITE_CONV
      [Linear_function.lin_f; ITLIST; REAL_ADD_RID]
      normalized in
  if not (aconv (rand (concl normalized_th)) lhs) then
    failwith "source-normalization test denotation mismatch";
  SYM normalized_th;;
let candle_cv_lc_flyspeck_source_variables,
    candle_cv_lc_flyspeck_source_result,
    candle_cv_lc_flyspeck_source_th =
  candle_lc_bulk_compute_flyspeck_source
    candle_cv_lc_flyspeck_normalize_lhs
    [(candle_cv_lc_flyspeck_raw_ineq1,`3`);
     (candle_cv_lc_flyspeck_raw_ineq2,`4`)];;
if candle_cv_lc_flyspeck_source_variables <>
     candle_cv_lc_flyspeck_variables ||
   not (aconv candle_cv_lc_flyspeck_source_result
              candle_cv_lc_flyspeck_result) ||
   not (aconv (concl candle_cv_lc_flyspeck_source_th)
              (concl candle_cv_lc_flyspeck_public_th)) ||
   not (set_eq (hyp candle_cv_lc_flyspeck_source_th)
          [concl candle_cv_lc_flyspeck_raw_ineq1;
           concl candle_cv_lc_flyspeck_raw_ineq2]) ||
   not (set_eq (axioms ()) candle_cv_lc_flyspeck_axioms) then
  failwith "Flyspeck source/oracle theorem interface mismatch";;

print_endline "CANDLE_CV_LINEAR_COMBINATION_FLYSPECK_OK";;
