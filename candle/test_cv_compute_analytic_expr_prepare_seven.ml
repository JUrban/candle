needs "candle/cv_compute_analytic_expr_jet_prove.ml";;

module Test_cv_compute_analytic_expr_prepare_seven = struct

open Candle_cv_analytic_expr_jet_prove;;

let candle_analytic_prepare_seven_source =
  `(\x:real^7.
      x$1 + x$2 + x$3 + x$4 + x$5 + x$6 + x$7)`;;

let candle_analytic_prepare_seven_result =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_prepare_seven
    candle_analytic_prepare_seven_source;;

let candle_analytic_prepare_six_regression_source =
  `(\x:real^6. x$1 + x$2 + x$3 + x$4 + x$5 + x$6)`;;

let candle_analytic_prepare_six_regression_result =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_prepare_six
    candle_analytic_prepare_six_regression_source;;

if hyp candle_analytic_prepare_seven_result.valid_theorem <> [] ||
   hyp Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_sound_seven <>
     [] ||
   hyp candle_analytic_prepare_seven_result.source_theorem <> [] ||
   hyp candle_analytic_prepare_seven_result.compile_theorem <> [] ||
   hyp candle_analytic_prepare_seven_result.program_representation <> [] ||
   hyp candle_analytic_prepare_six_regression_result.valid_theorem <> [] ||
   hyp candle_analytic_prepare_six_regression_result.source_theorem <> [] ||
   not
     (aconv candle_analytic_prepare_seven_result.function_term
       candle_analytic_prepare_seven_source) ||
   not
     (aconv candle_analytic_prepare_six_regression_result.function_term
       candle_analytic_prepare_six_regression_source) then
  failwith "analytic prepare-seven regression";;

print_endline
  "CANDLE_CV_ANALYTIC_EXPR_PREPARE_SEVEN_OK DEVELOPMENT_NON_RELEASE";;

end;;
