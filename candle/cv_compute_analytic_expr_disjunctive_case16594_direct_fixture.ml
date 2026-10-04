(* ========================================================================== *)
(* Direct-source fixture for genuine nonlinear member 16594.                 *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the same pinned source proposition    *)
(* used by the historical generated-closure experiment, reconstructed only  *)
(* from the modules authenticated by the direct Flyspeck load.               *)
(* ========================================================================== *)

needs "candle/cv_compute_flyspeck_direct_source_compat.ml";;

module Candle_cv_analytic_expr_disjunctive_case16594_fixture = struct

open Candle_cv_flyspeck_direct_source_compat;;

let candle_disjunctive_case16594_target =
 `ineqm [x1; x2; x3; x4; x5; x6]
   (frac_right 5 #0.5000
   (frac_left 3 #0.5000
   (bisect_right 2
   (bisect_left 1
   (bisect_right 0
   (bisect_right 4
   (bisect_left 4
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

let candle_disjunctive_case16594_reconstruction =
  candle_direct_ineqm_conv candle_disjunctive_case16594_target;;

if lhand (concl candle_disjunctive_case16594_reconstruction) <>
     candle_disjunctive_case16594_target then
  failwith "case16594 direct fixture: reconstruction source mismatch";;

let candle_disjunctive_case16594_case =
  rand (concl candle_disjunctive_case16594_reconstruction);;

let candle_disjunctive_case16594_expansion =
  (REWRITE_CONV
     [TAUT `(P ==> Q) <=> (~P \/ Q)`;
      REAL_ARITH `~(a > b:real) <=> a <= b`;
      REAL_ARITH `~(a < b:real) <=> b <= a`;
      REAL_ARITH `~(a >= b:real) <=> a < b`;
      REAL_ARITH `~(a <= b:real) <=> b < a`]
   THENC candle_direct_expand_ineq_case)
    candle_disjunctive_case16594_case;;

let candle_disjunctive_case16594_converted =
  rand (concl candle_disjunctive_case16594_expansion);;

let candle_disjunctive_case16594_ineq,
    candle_disjunctive_case16594_variable_names,
    candle_disjunctive_case16594_bounds =
  M_verifier_main.dest_ineq candle_disjunctive_case16594_converted;;

let candle_disjunctive_case16594_standard =
  M_verifier_main.mk_standard_ineq
    [REAL_POW_1; real_pow] candle_disjunctive_case16594_ineq;;

let candle_disjunctive_case16594_terms =
  striplist dest_disj
    ((lhand o concl) candle_disjunctive_case16594_standard);;

if length candle_disjunctive_case16594_terms <> 2 then
  failwith "case16594 direct fixture: source disjunction drift";;

let candle_disjunctive_case16594_lhs =
  map lhand candle_disjunctive_case16594_terms;;

let candle_disjunctive_case16594_functions,
    candle_disjunctive_case16594_variable_vector =
  candle_direct_exprs_to_vector_fun candle_disjunctive_case16594_lhs;;

if length candle_disjunctive_case16594_functions <> 2 then
  failwith "case16594 direct fixture: vector-function drift";;

end;;
