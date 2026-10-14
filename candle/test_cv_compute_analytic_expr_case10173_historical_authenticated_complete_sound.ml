(* Regression guard for the authenticated numerical/topology composition. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_complete_sound.ml";;

open Candle_cv_analytic_expr_case10173_historical_authenticated_complete_sound;;

if hyp candle_case10173_hist_authenticated_complete_sound <> [] then
  failwith "case10173 authenticated complete theorem has assumptions";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_AUTHENTICATED_COMPLETE_TEST_OK DEVELOPMENT_NON_RELEASE";;
