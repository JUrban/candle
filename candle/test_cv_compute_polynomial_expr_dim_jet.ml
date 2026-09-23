needs "candle/cv_compute_polynomial_expr_dim_jet.ml";;

open Candle_cv_polynomial_expr_dim_jet;;

if hyp candle_q_dim_poly_jet_sound <> [] then
  failwith "dimension-generic interval-jet soundness has assumptions";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_DIM_JET_OK";;
