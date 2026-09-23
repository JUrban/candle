needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_dim_check.ml";;

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_diff;;
open Candle_cv_polynomial_expr_dim_check;;

if hyp candle_q_rows_width_all <> [] ||
   hyp candle_q_box_valid_list_all <> [] ||
   hyp candle_q_box_valid_list_el <> [] ||
   hyp candle_poly_hessian_programs_rows_width <> [] ||
   hyp candle_poly_derived_inputs_valid <> [] ||
   hyp candle_poly_derived_inputs_valid_length <> [] ||
   hyp candle_poly_dim_whole_box_accept_components <> [] then
  failwith "source-authenticated dimension checker assumptions mismatch";;

let candle_poly_dim_check_fixture =
 `Candle_poly_add
    (Candle_poly_mul (Candle_poly_var 0) (Candle_poly_var 5))
    (Candle_poly_square (Candle_poly_var 2))`;;

let candle_poly_dim_check_fixture_rows =
  SPEC `candle_poly_dim_check_fixture:candle_poly_expr`
    (SPEC `6` candle_poly_hessian_programs_rows_width);;

if hyp candle_poly_dim_check_fixture_rows <> [] then
  failwith "six-variable derived Hessian row-width assumptions mismatch";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_DIM_CHECK_OK";;
