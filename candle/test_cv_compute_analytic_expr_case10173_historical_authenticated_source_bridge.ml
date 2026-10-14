(* Regression guard for the exact historical-AST/original-source bridge. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_source_bridge.ml";;

open Candle_cv_analytic_expr_case10173_historical_authenticated_source_bridge;;

if hyp candle_case10173_hist_authenticated_source_expansion <> [] ||
   hyp candle_case10173_hist_authenticated_source_theorem <> [] ||
   hyp candle_case10173_hist_authenticated_source_function <> [] then
  failwith "case10173 historical source bridge test: assumptions";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_AUTHENTICATED_SOURCE_BRIDGE_TEST_OK DEVELOPMENT_NON_RELEASE";;
