(* ========================================================================== *)
(* Authenticated source fixture for the first nonlinear inequality at 296.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The wrapper checks this literal against the   *)
(* pinned action-296 target before this fragment runs in the loaded verifier. *)
(* ========================================================================== *)

module Candle_cv_analytic_expr_action296_fixture = struct

let candle_action296_analytic_target =
 `ineqm [x1; x2; x3; x4; x5; x6]
   (frac_right 0 #0.5000
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

let candle_action296_analytic_reconstruction =
  Break_case.ineqm_conv candle_action296_analytic_target;;

if lhand (concl candle_action296_analytic_reconstruction) <>
     candle_action296_analytic_target then
  failwith "action296 analytic fixture: reconstruction source mismatch";;

let candle_action296_analytic_case =
  rand (concl candle_action296_analytic_reconstruction);;

let candle_action296_analytic_expansion =
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
    candle_action296_analytic_case;;

let candle_action296_analytic_converted =
  rand (concl candle_action296_analytic_expansion);;

let candle_action296_analytic_ineq,
    candle_action296_analytic_variable_names,
    candle_action296_analytic_bounds =
  M_verifier_main.dest_ineq candle_action296_analytic_converted;;

let candle_action296_analytic_standard =
  M_verifier_main.mk_standard_ineq
    [REAL_POW_1; real_pow] candle_action296_analytic_ineq;;

let candle_action296_analytic_terms =
  striplist dest_disj
    ((lhand o concl) candle_action296_analytic_standard);;

if length candle_action296_analytic_terms <> 1 then
  failwith "action296 analytic fixture: source disjunction drift";;

let candle_action296_analytic_lhs =
  lhand (hd candle_action296_analytic_terms);;

let candle_action296_analytic_functions,
    candle_action296_analytic_variable_vector =
  M_verifier_main.exprs_to_vector_fun [candle_action296_analytic_lhs];;

if length candle_action296_analytic_functions <> 1 then
  failwith "action296 analytic fixture: vector-function drift";;

let candle_action296_analytic_function =
  hd candle_action296_analytic_functions;;

end;;
