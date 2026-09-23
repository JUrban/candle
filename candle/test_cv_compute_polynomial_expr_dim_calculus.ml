needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_dim_calculus.ml";;

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_calculus;;

if hyp candle_real_fun_update_same <> [] ||
   hyp candle_poly_value_fun_has_real_derivative <> [] ||
   hyp candle_poly_d_fun_has_real_derivative <> [] ||
   hyp candle_q_real_lookup_in_range <> [] ||
   hyp candle_q_real_lookup_list_of_seq <> [] ||
   hyp candle_poly_value_list_fun <> [] ||
   hyp candle_poly_d_list_fun <> [] ||
   hyp candle_poly_dd_list_fun <> []
then failwith "dimension-parametric polynomial calculus assumptions mismatch";;

let candle_poly_six_var_calculus_expr =
 `Candle_poly_add
    (Candle_poly_mul (Candle_poly_var 0) (Candle_poly_var 5))
    (Candle_poly_square (Candle_poly_var 2))`;;

let candle_poly_six_var_rho =
 `(\i. candle_q_real_lookup i [x1:real;x2;x3;x4;x5;x6])`;;

let candle_poly_six_var_first_derivative =
  SPECL
   [candle_poly_six_var_calculus_expr;
    candle_poly_six_var_rho;
    `5`]
   candle_poly_value_fun_has_real_derivative;;

let candle_poly_six_var_second_derivative =
  SPECL
   [candle_poly_six_var_calculus_expr;
    candle_poly_six_var_rho;
    `0`; `5`]
   candle_poly_d_fun_has_real_derivative;;

let candle_poly_six_var_valid = prove
 (`candle_poly_valid_dim 6
    (Candle_poly_add
      (Candle_poly_mul (Candle_poly_var 0) (Candle_poly_var 5))
      (Candle_poly_square (Candle_poly_var 2)))`,
  REWRITE_TAC[candle_poly_valid_dim_def] THEN ARITH_TAC);;

let candle_poly_six_var_list_fun =
  MATCH_MP
   (SPECL
     [candle_poly_six_var_calculus_expr;
      `6`; `\i. candle_q_real_lookup i [x1:real;x2;x3;x4;x5;x6]`]
     candle_poly_value_list_fun)
   candle_poly_six_var_valid;;

if hyp candle_poly_six_var_first_derivative <> [] ||
   hyp candle_poly_six_var_second_derivative <> [] ||
   hyp candle_poly_six_var_valid <> [] ||
   hyp candle_poly_six_var_list_fun <> []
then failwith "six-variable polynomial calculus fixture mismatch";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_DIM_CALCULUS_OK";;
