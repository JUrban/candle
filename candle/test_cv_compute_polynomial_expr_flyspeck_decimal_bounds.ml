needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_fixture.ml";;
needs "candle/cv_compute_flyspeck_nonlinear_driver.ml";;

open Candle_cv_exact_interval_reify;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_flyspeck_nonlinear_driver;;

let candle_decimal_bounds_interval =
  candle_poly_fixture_q_interval
    `#1.2317544220903043901`
    `#1.2317544220903043906`;;

let candle_decimal_bounds_expected =
  mk_pair
    (candle_q_term
      (Num.div_num
        (Num.num_of_string "12317544220903043901")
        (Num.num_of_string "10000000000000000000")),
     candle_q_term
      (Num.div_num
        (Num.num_of_string "12317544220903043906")
        (Num.num_of_string "10000000000000000000")));;

if not (aconv candle_decimal_bounds_interval candle_decimal_bounds_expected) then
  failwith "Flyspeck decimal box endpoint encoding mismatch";;

let candle_decimal_bounds_lower_th =
  candle_reflected_nl_exact_component `#1.2317544220903043901`;;
let candle_decimal_bounds_upper_th =
  candle_reflected_nl_exact_component `#1.2317544220903043906`;;

if hyp candle_decimal_bounds_lower_th <> [] ||
   hyp candle_decimal_bounds_upper_th <> [] ||
   not (is_ratconst (rand (concl candle_decimal_bounds_lower_th))) ||
   not (is_ratconst (rand (concl candle_decimal_bounds_upper_th))) then
  failwith "Flyspeck decimal endpoint theorem normalization mismatch";;

let candle_decimal_bounds_upper_data =
  candle_reflected_nl_exact_component_data `#1.2317544220903043906`;;

if not (is_ratconst candle_decimal_bounds_upper_data) ||
   not
     (Num.eq_num
       (rat_of_term candle_decimal_bounds_upper_data)
       (Num.div_num
         (Num.num_of_string "12317544220903043906")
         (Num.num_of_string "10000000000000000000"))) then
  failwith "Flyspeck decimal endpoint data normalization mismatch";;

if !Cakeml.pendingLoadedSourceIds <> [] then
  failwith "Flyspeck decimal endpoint source identities remain pending";;

print_endline "CANDLE_CV_FLYSPECK_DECIMAL_BOUNDS_OK";;
