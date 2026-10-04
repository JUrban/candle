(* Direct-source fixture for production nonlinear sibling 149 (case 16479). *)

needs "candle/cv_compute_flyspeck_direct_source_compat.ml";;

module Candle_cv_analytic_expr_disjunctive_case16479_fixture = struct

open Candle_cv_flyspeck_direct_source_compat;;

let candle_disjunctive_case16479_label = "prep-8293089898";;
let candle_disjunctive_case16479_index = 149;;
let candle_disjunctive_case16479_target =
 `ineqm [x1; x2; x3; x4; x5; x6]
   (frac_right 5 #0.5000
   (bisect_right 3
   (bisect_right 2
   (bisect_left 1
   (bisect_right 0
   (bisect_left 4
   (bisect_right 4
   [#4.0,(#2.0 * #1.26) * #2.0 * #1.26;
    #4.0,(#2.0 * #1.26) * #2.0 * #1.26;
    #4.0,(#2.0 * #1.26) * #2.0 * #1.26;
    #4.0,(#2.0 * #1.26) * #2.0 * #1.26;
    #3.01 * #3.01,#3.9 * #3.9;
    #4.0,(#2.0 * #1.26) * #2.0 * #1.26])))))))
   (x1_delta_x x1 x2 x3 x4 x5 x6 * &4 +
    delta4_squared_x x1 x2 x3 x4 x5 x6 * -- #0.833 <
    &0 \/
    unit6 x1 x2 x3 x4 x5 x6 * -- #0.026 +
    rhazimatn_x x1 x2 x3 x4 x5 x6 * -- &1 +
    rhazim2atn_x x1 x2 x3 x4 x5 x6 * -- &1 +
    rhazim3atn_x x1 x2 x3 x4 x5 x6 * -- &1 +
    unit6 x1 x2 x3 x4 x5 x6 * pi +
    unit6 x1 x2 x3 x4 x5 x6 * const1 * pi <
    &0)`;;

let candle_disjunctive_case16479_reconstruction =
  candle_direct_ineqm_conv candle_disjunctive_case16479_target;;

if not
     (aconv (lhand (concl candle_disjunctive_case16479_reconstruction))
       candle_disjunctive_case16479_target) then
  failwith "case16479 direct fixture: reconstruction source mismatch";;

let candle_disjunctive_case16479_case =
  rand (concl candle_disjunctive_case16479_reconstruction);;
let candle_disjunctive_case16479_expansion =
  (REWRITE_CONV
     [TAUT `(P ==> Q) <=> (~P \/ Q)`;
      REAL_ARITH `~(a > b:real) <=> a <= b`;
      REAL_ARITH `~(a < b:real) <=> b <= a`;
      REAL_ARITH `~(a >= b:real) <=> a < b`;
      REAL_ARITH `~(a <= b:real) <=> b < a`]
   THENC candle_direct_expand_ineq_case)
    candle_disjunctive_case16479_case;;
let candle_disjunctive_case16479_converted =
  rand (concl candle_disjunctive_case16479_expansion);;

let candle_disjunctive_case16479_ineq,
    candle_disjunctive_case16479_variable_names,
    candle_disjunctive_case16479_bounds =
  M_verifier_main.dest_ineq candle_disjunctive_case16479_converted;;
let candle_disjunctive_case16479_standard =
  M_verifier_main.mk_standard_ineq
    [REAL_POW_1;real_pow] candle_disjunctive_case16479_ineq;;
let candle_disjunctive_case16479_terms =
  striplist dest_disj
    ((lhand o concl) candle_disjunctive_case16479_standard);;

if length candle_disjunctive_case16479_terms <> 2 then
  failwith "case16479 direct fixture: source disjunction drift";;

let candle_disjunctive_case16479_lhs =
  map lhand candle_disjunctive_case16479_terms;;
let candle_disjunctive_case16479_functions,
    candle_disjunctive_case16479_variable_vector =
  candle_direct_exprs_to_vector_fun candle_disjunctive_case16479_lhs;;

if length candle_disjunctive_case16479_functions <> 2 then
  failwith "case16479 direct fixture: vector-function drift";;

end;;
