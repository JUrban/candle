needs "candle/cv_compute_polynomial_expr_flyspeck_fixture.ml";;

open Candle_cv_polynomial_expr_flyspeck_fixture;;

let candle_poly_fixture_test_vector = `p:real^6`;;
let candle_poly_fixture_test_variables =
  [`x1:real`;`x2:real`;`x3:real`;`x4:real`;`x5:real`;`x6:real`];;
let candle_poly_fixture_test_scalar_source =
  `x1 * x6 + x3 pow 2 + -- &1`;;
let candle_poly_fixture_test_lower = replicate `&0` 6;;
let candle_poly_fixture_test_upper = replicate `&1 / &8` 6;;

let candle_poly_fixture_test_source,
    candle_poly_fixture_test_boxes,
    candle_poly_fixture_test_expression,
    candle_poly_fixture_test_valid,
    candle_poly_fixture_test_source_theorem,
    candle_poly_fixture_test_program,
    candle_poly_fixture_test_run_theorem =
  candle_poly_prepare_scalar_fixture
    candle_poly_fixture_test_vector
    candle_poly_fixture_test_variables
    candle_poly_fixture_test_scalar_source
    candle_poly_fixture_test_lower
    candle_poly_fixture_test_upper;;

let candle_poly_fixture_test_expected_source =
  `(p:real^6)$1 * p$6 + p$3 pow 2 + -- &1`;;
let candle_poly_fixture_test_expected_interval =
 `((((0,0),0),((1,0),7)):
   ((num#num)#num)#((num#num)#num))`;;
let candle_poly_fixture_test_expected_boxes =
  mk_list
    (replicate candle_poly_fixture_test_expected_interval 6,
     `:((num#num)#num)#((num#num)#num)`);;
let candle_poly_fixture_test_expected_source_theorem =
  mk_eq
    (mk_icomb
      (mk_icomb (`candle_poly_denote_dim`,
                  candle_poly_fixture_test_expression),
       candle_poly_fixture_test_vector),
     candle_poly_fixture_test_expected_source);;

if not (aconv candle_poly_fixture_test_source
              candle_poly_fixture_test_expected_source) ||
   not (aconv candle_poly_fixture_test_boxes
              candle_poly_fixture_test_expected_boxes) ||
   hyp candle_poly_fixture_test_valid <> [] ||
   hyp candle_poly_fixture_test_source_theorem <> [] ||
   hyp candle_poly_fixture_test_run_theorem <> [] ||
   not (aconv (concl candle_poly_fixture_test_source_theorem)
              candle_poly_fixture_test_expected_source_theorem) then
  failwith "captured Flyspeck fixture adapter mismatch";;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_FLYSPECK_FIXTURE_OK";;
