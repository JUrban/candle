needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_calculus.ml";;

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_calculus;;

if hyp candle_poly_has_real_jet_derivatives <> [] then
  failwith "polynomial AST calculus theorem assumptions mismatch";;

let candle_poly_cubic_calculus =
  SPECL
   [`Candle_poly_add
       (Candle_poly_add
         (Candle_poly_mul
           (Candle_poly_square (Candle_poly_var 0))
           (Candle_poly_var 0))
         (Candle_poly_mul
           (Candle_poly_var 0)
           (Candle_poly_square (Candle_poly_var 1))))
       (Candle_poly_neg (Candle_poly_const 1 0 0))`;
    `x:real`; `y:real`]
   candle_poly_has_real_jet_derivatives;;

if hyp candle_poly_cubic_calculus <> [] then
  failwith "polynomial AST cubic calculus assumptions mismatch";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_CALCULUS_OK";;
