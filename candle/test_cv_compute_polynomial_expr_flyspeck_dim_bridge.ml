load_path :=
  ["/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6/formal_ineqs"] @
  !load_path;;

needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_dim_bridge.ml";;

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_flyspeck_dim_bridge;;

if hyp candle_poly_denote_dim_diff2c <> [] ||
   hyp candle_poly_denote_dim_diff2c_domain <> [] ||
   hyp candle_poly_denote_dim_partials <> [] ||
   hyp candle_poly_diff_flyspeck_partial <> [] ||
   hyp candle_poly_diff2_flyspeck_partial2 <> [] ||
   hyp candle_poly_gradient_flyspeck_partials <> [] ||
   hyp candle_poly_hessian_flyspeck_partials <> [] ||
   hyp candle_poly_flyspeck_analytic_contract <> [] then
  failwith "dimension-generic Flyspeck smoothness assumptions mismatch";;

let candle_poly_dim_bridge_fixture =
 `Candle_poly_add
    (Candle_poly_mul (Candle_poly_var 0) (Candle_poly_var 5))
    (Candle_poly_square (Candle_poly_var 2))`;;

let candle_poly_dim_bridge_fixture_valid = prove
 (mk_comb
   (`candle_poly_valid_dim (dimindex (:6))`,
    candle_poly_dim_bridge_fixture),
  REWRITE_TAC[candle_poly_valid_dim_def] THEN
  CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC);;

let candle_poly_dim_bridge_fixture_diff2c =
  MATCH_MP
    (ISPECL
      [candle_poly_dim_bridge_fixture; `z:real^6`]
      candle_poly_denote_dim_diff2c)
    candle_poly_dim_bridge_fixture_valid;;

if hyp candle_poly_dim_bridge_fixture_diff2c <> [] then
  failwith "six-variable Flyspeck smoothness specialization mismatch";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_FLYSPECK_DIM_BRIDGE_OK";;
