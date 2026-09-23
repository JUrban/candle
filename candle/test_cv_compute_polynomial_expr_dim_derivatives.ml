needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_dim_derivatives.ml";;

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;

if hyp candle_poly_gradient_length <> [] ||
   hyp candle_poly_gradient_el <> [] ||
   hyp candle_poly_hessian_length <> [] ||
   hyp candle_poly_hessian_row_length <> [] ||
   hyp candle_poly_hessian_el <> [] ||
   hyp candle_poly_dd_list_symmetric <> [] ||
   hyp candle_poly_dim_derivatives_2 <> []
then failwith "dimension-parametric polynomial derivative assumptions mismatch";;

let candle_poly_six_var_expr =
 `Candle_poly_add
    (Candle_poly_mul (Candle_poly_var 0) (Candle_poly_var 5))
    (Candle_poly_square (Candle_poly_var 2))`;;

let candle_poly_six_var_gradient_length =
  SPECL
   [`6`;
    `[x1:real;x2;x3;x4;x5;x6]`;
    candle_poly_six_var_expr]
   candle_poly_gradient_length;;

let candle_poly_six_var_hessian_length =
  SPECL
   [`6`;
    `[x1:real;x2;x3;x4;x5;x6]`;
    candle_poly_six_var_expr]
   candle_poly_hessian_length;;

let candle_poly_six_var_cross_partial = prove
 (`candle_poly_dd_list 5 0 [x1;x2;x3;x4;x5;x6]
      (Candle_poly_add
        (Candle_poly_mul (Candle_poly_var 0) (Candle_poly_var 5))
        (Candle_poly_square (Candle_poly_var 2))) = &1`,
  REWRITE_TAC[candle_poly_dd_list_def; candle_poly_d_list_def;
              candle_poly_value_list_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

if hyp candle_poly_six_var_gradient_length <> [] ||
   hyp candle_poly_six_var_hessian_length <> [] ||
   hyp candle_poly_six_var_cross_partial <> []
then failwith "dimension-parametric polynomial derivative fixture mismatch";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_DIM_DERIVATIVES_OK";;
