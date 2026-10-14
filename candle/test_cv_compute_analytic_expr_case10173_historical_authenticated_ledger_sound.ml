needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_ledger_sound.ml";;

module Test_cv_compute_analytic_expr_case10173_historical_authenticated_ledger_sound = struct

open Candle_cv_analytic_expr_case10173_historical_authenticated_ledger_sound;;

let _,ledger_body =
  strip_forall
    (concl candle_case10173_hist_authenticated_ledger_original_sound);;

if hyp candle_case10173_hist_authenticated_ledger_original_sound <> [] ||
   not
     (aconv
       (snd (dest_imp ledger_body))
       Candle_cv_analytic_expr_case10173_fixture.candle_case10173_analytic_target)
then failwith "case10173 authenticated ledger sound test: theorem drift";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_AUTHENTICATED_LEDGER_SOUND_TEST_OK DEVELOPMENT_NON_RELEASE";;

end;;
