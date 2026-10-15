(* ========================================================================== *)
(* Regression for proof-producing seven-dimensional analytic box checking.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_append_parameter.ml";;

module Test_cv_compute_analytic_expr_prove_seven = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_append_parameter;;

let candle_analytic_prove_seven_source =
  `(\x:real^7.
      x$1 + x$2 + x$3 + x$4 + x$5 + x$6 + x$7 - &9)`;;

let candle_analytic_prove_six_source =
  `(\x:real^6.
      x$1 + x$2 + x$3 + x$4 + x$5 + x$6 + &1 - &9)`;;

let candle_analytic_prove_seven_prepared =
  candle_q_dim_analytic_jet_prepare_seven
    candle_analytic_prove_seven_source;;

let candle_analytic_prove_seven_theorem =
  candle_reflected_nl_append_parameter_prove_box_six
    candle_analytic_prove_seven_prepared
    candle_analytic_prove_seven_source
    candle_analytic_prove_six_source
    `&1`
    (REAL_ARITH `&0 <= &1 /\ &1 <= &2`)
    [`&0`;`&0`;`&0`;`&0`;`&0`;`&0`]
    [`&1`;`&1`;`&1`;`&1`;`&1`;`&1`];;

if hyp candle_analytic_prove_seven_theorem <> [] then
  failwith "analytic prove-seven theorem has assumptions";;

print_endline
  "CANDLE_CV_ANALYTIC_EXPR_PROVE_SEVEN_OK DEVELOPMENT_NON_RELEASE";;

end;;
