(* Regression guard for the original-theorem semantic adapter. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_original_bridge.ml";;

open Candle_cv_analytic_expr_case10173_fixture;;
open Candle_cv_analytic_expr_case10173_historical_authenticated_original_bridge;;

let candle_case10173_hist_original_bridge_antecedent,
    candle_case10173_hist_original_bridge_consequent =
  dest_imp
    (concl candle_case10173_hist_authenticated_original_bridge);;

if not
     (aconv
       candle_case10173_hist_original_bridge_antecedent
       candle_case10173_hist_authenticated_original_cell_goal) ||
   not
     (aconv
       candle_case10173_hist_original_bridge_consequent
       candle_case10173_analytic_target) ||
   hyp candle_case10173_hist_authenticated_original_bridge <> [] then
  failwith "case10173 authenticated original bridge test: theorem drift";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_AUTHENTICATED_ORIGINAL_BRIDGE_TEST_OK DEVELOPMENT_NON_RELEASE";;
