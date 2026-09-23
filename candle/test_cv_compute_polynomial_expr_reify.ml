needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_reify.ml";;

open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_reify;;

let candle_poly_reify_variables =
  [`x1:real`;`x2:real`;`x3:real`;`x4:real`;`x5:real`;`x6:real`];;

let candle_poly_reify_source =
  `x1 * x6 + x3 pow 2 - &7`;;

let candle_poly_reified_ast,
    candle_poly_reified_valid,
    candle_poly_reified_source,
    candle_poly_reified_program,
    candle_poly_reified_run =
  candle_poly_reify_real_expression
    candle_poly_reify_variables candle_poly_reify_source;;

let candle_poly_reified_expected_ast =
  `Candle_poly_add
     (Candle_poly_mul (Candle_poly_var 0) (Candle_poly_var 5))
     (Candle_poly_add
       (Candle_poly_square (Candle_poly_var 2))
       (Candle_poly_neg (Candle_poly_const 7 0 0)))`;;

if not (aconv candle_poly_reified_ast candle_poly_reified_expected_ast) then
  failwith "polynomial source reifier AST mismatch";;

if hyp candle_poly_reified_valid <> [] ||
   hyp candle_poly_reified_source <> [] ||
   hyp candle_poly_reified_run <> [] then
  failwith "polynomial source reifier assumptions mismatch";;

if length (dest_list candle_poly_reified_program) <> 9 then
  failwith "polynomial source reifier program length mismatch";;

let candle_poly_reified_source_expected =
  mk_eq
    (list_mk_comb
      (`candle_poly_value_list`,
       [mk_list (candle_poly_reify_variables,`:real`);
        candle_poly_reified_ast]),
     candle_poly_reify_source);;

if not
    (aconv (concl candle_poly_reified_source)
           candle_poly_reified_source_expected) then
  failwith "polynomial source reifier theorem mismatch";;

if !Cakeml.pendingLoadedSourceIds <> [] then
  failwith "polynomial source reifier source identities remain pending";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_REIFY_OK";;
