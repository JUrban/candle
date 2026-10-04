(* ========================================================================== *)
(* Authenticated source fixture for the left-half sibling of action 296.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The wrapper checks this literal against the   *)
(* pinned case-10173 target before this fragment runs in the loaded verifier. *)
(* ========================================================================== *)

needs "candle/cv_compute_flyspeck_direct_source_compat.ml";;

module Candle_cv_analytic_expr_case10173_fixture = struct

open Candle_cv_flyspeck_direct_source_compat;;

let candle_case10173_analytic_target =
 `ineqm [x1; x2; x3; x4; x5; x6]
   (frac_left 0 #0.5000
   [#4.7524,#6.3504; #4.0,#4.7524; #4.0,#4.7524; #4.0,#2.25 * #2.25;
   #4.0,
   #2.25 * #2.25; #4.0,#2.25 * #2.25])
   (unit6 x1 x2 x3 x4 x5 x6 * #1.277 +
    sqrt_x1 x1 x2 x3 x4 x5 x6 * #0.273298 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.273298 * -- #2.18 +
    sqrt_x2 x1 x2 x3 x4 x5 x6 * -- #0.273853 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.273853 * #2.0 +
    sqrt_x3 x1 x2 x3 x4 x5 x6 * -- #0.273853 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.273853 * #2.0 +
    sqrt_x4 x1 x2 x3 x4 x5 x6 * #0.708818 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.708818 * -- #2.0 +
    sqrt_x5 x1 x2 x3 x4 x5 x6 * -- #0.313988 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.313988 * #2.0 +
    sqrt_x6 x1 x2 x3 x4 x5 x6 * -- #0.313988 +
    unit6 x1 x2 x3 x4 x5 x6 * #0.313988 * #2.0 +
    dihatn_x x1 x2 x3 x4 x5 x6 * -- &1 <
    &0)`;;

let candle_case10173_analytic_reconstruction =
  candle_direct_ineqm_conv candle_case10173_analytic_target;;

if lhand (concl candle_case10173_analytic_reconstruction) <>
     candle_case10173_analytic_target then
  failwith "case10173 analytic fixture: reconstruction source mismatch";;

let candle_case10173_analytic_case =
  rand (concl candle_case10173_analytic_reconstruction);;

let candle_case10173_analytic_expansion =
  (REWRITE_CONV
     [TAUT `(P ==> Q) <=> (~P \/ Q)`;
      REAL_ARITH `~(a > b:real) <=> a <= b`;
      REAL_ARITH `~(a < b:real) <=> b <= a`;
      REAL_ARITH `~(a >= b:real) <=> a < b`;
      REAL_ARITH `~(a <= b:real) <=> b < a`]
   THENC candle_direct_expand_ineq_case)
    candle_case10173_analytic_case;;

let candle_case10173_analytic_converted =
  rand (concl candle_case10173_analytic_expansion);;

let candle_case10173_analytic_ineq,
    candle_case10173_analytic_variable_names,
    candle_case10173_analytic_bounds =
  M_verifier_main.dest_ineq candle_case10173_analytic_converted;;

let candle_case10173_analytic_standard =
  M_verifier_main.mk_standard_ineq
    [REAL_POW_1; real_pow] candle_case10173_analytic_ineq;;

let candle_case10173_analytic_terms =
  striplist dest_disj
    ((lhand o concl) candle_case10173_analytic_standard);;

if length candle_case10173_analytic_terms <> 1 then
  failwith "case10173 analytic fixture: source disjunction drift";;

let candle_case10173_analytic_lhs =
  lhand (hd candle_case10173_analytic_terms);;

let candle_case10173_analytic_functions,
    candle_case10173_analytic_variable_vector =
  candle_direct_exprs_to_vector_fun [candle_case10173_analytic_lhs];;

if length candle_case10173_analytic_functions <> 1 then
  failwith "case10173 analytic fixture: vector-function drift";;

let candle_case10173_analytic_function =
  hd candle_case10173_analytic_functions;;

end;;
