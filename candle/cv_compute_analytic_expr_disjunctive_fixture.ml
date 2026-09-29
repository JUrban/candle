(* ========================================================================== *)
(* Authenticated source fixture for the smallest retained disjunctive case. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The wrapper checks this literal against the   *)
(* pinned target before this fragment runs in the loaded verifier.            *)
(* ========================================================================== *)

module Candle_cv_analytic_expr_disjunctive_fixture = struct

let candle_disjunctive_analytic_target =
 `ineqm [x1; x2; x3; x4; x5; x6]
   (frac_right 5 #0.5000
   (bisect_right 3
   (bisect_right 2
   (bisect_left 1
   (bisect_right 0
   (bisect_left 4
   (bisect_right 4
   [#4.0,(#2.0 * #1.26) * #2.0 * #1.26; #4.0,(#2.0 * #1.26) * #2.0 * #1.26;
   #4.0,
   (#2.0 * #1.26) * #2.0 * #1.26; #4.0,(#2.0 * #1.26) * #2.0 * #1.26;
   #3.01 * #3.01,
   #3.9 * #3.9; #4.0,(#2.0 * #1.26) * #2.0 * #1.26])))))))
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

let candle_disjunctive_analytic_reconstruction =
  Break_case.ineqm_conv candle_disjunctive_analytic_target;;

if lhand (concl candle_disjunctive_analytic_reconstruction) <>
     candle_disjunctive_analytic_target then
  failwith "disjunctive analytic fixture: reconstruction source mismatch";;

let candle_disjunctive_analytic_case =
  rand (concl candle_disjunctive_analytic_reconstruction);;

let candle_disjunctive_analytic_expansion =
  (REWRITE_CONV
     [TAUT `(P ==> Q) <=> (~P \/ Q)`;
      REAL_ARITH `~(a > b:real) <=> a <= b`;
      REAL_ARITH `~(a < b:real) <=> b <= a`;
      REAL_ARITH `~(a >= b:real) <=> a < b`;
      REAL_ARITH `~(a <= b:real) <=> b < a`]
   THENC
   REWRITE_CONV
     ([Definitions.ineq; IMP_IMP; REAL_MUL_LZERO; REAL_MUL_RZERO] @
      Definitions.flyspeck_defs)
   THENC DEPTH_CONV let_CONV)
    candle_disjunctive_analytic_case;;

let candle_disjunctive_analytic_converted =
  rand (concl candle_disjunctive_analytic_expansion);;

let candle_disjunctive_analytic_ineq,
    candle_disjunctive_analytic_variable_names,
    candle_disjunctive_analytic_bounds =
  M_verifier_main.dest_ineq candle_disjunctive_analytic_converted;;

let candle_disjunctive_analytic_standard =
  M_verifier_main.mk_standard_ineq
    [REAL_POW_1; real_pow] candle_disjunctive_analytic_ineq;;

let candle_disjunctive_analytic_terms =
  striplist dest_disj
    ((lhand o concl) candle_disjunctive_analytic_standard);;

if length candle_disjunctive_analytic_terms <> 2 then
  failwith "disjunctive analytic fixture: source disjunction drift";;

let candle_disjunctive_analytic_lhs =
  map lhand candle_disjunctive_analytic_terms;;

let candle_disjunctive_analytic_functions,
    candle_disjunctive_analytic_variable_vector =
  M_verifier_main.exprs_to_vector_fun candle_disjunctive_analytic_lhs;;

if length candle_disjunctive_analytic_functions <> 2 then
  failwith "disjunctive analytic fixture: vector-function drift";;

end;;
