(* Regression guard for the full authenticated case-10173 composition. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_original_sound.ml";;

open Candle_cv_analytic_expr_case10173_fixture;;
open Candle_cv_analytic_expr_case10173_historical_authenticated_original_sound;;

let _,candle_case10173_hist_original_sound_body =
  strip_forall (concl candle_case10173_hist_authenticated_original_sound);;
let _,candle_case10173_hist_original_sound_consequent =
  dest_imp candle_case10173_hist_original_sound_body;;

if hyp candle_case10173_hist_authenticated_original_sound <> [] ||
   not
     (aconv
       candle_case10173_hist_original_sound_consequent
       candle_case10173_analytic_target) then
  failwith "case10173 authenticated original sound test: theorem drift";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_AUTHENTICATED_ORIGINAL_SOUND_TEST_OK DEVELOPMENT_NON_RELEASE";;
