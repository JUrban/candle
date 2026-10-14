needs "candle/cv_compute_analytic_expr_case10173_historical_authenticated_batch_sound.ml";;

module Test_cv_compute_analytic_expr_case10173_historical_authenticated_batch_sound = struct

open Candle_cv_analytic_expr_case10173_historical_authenticated_batch_sound;;

if hyp candle_case10173_hist_length_seven <> [] ||
   hyp candle_case10173_hist_jobs_well_formed_source_contract <> [] ||
   hyp candle_cv_case10173_hist_job_well_formed_correct <> [] ||
   hyp candle_cv_case10173_hist_jobs_well_formed_correct <> [] ||
   hyp candle_cv_case10173_hist_raw_jobs_well_formed_accept <> [] ||
   hyp candle_case10173_hist_authenticated_checked_jobs_sound <> [] ||
   hyp candle_case10173_hist_authenticated_checked_raw_jobs_sound <> [] then
  failwith "case10173 historical authenticated batch: open theorem";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_AUTHENTICATED_BATCH_TEST_OK DEVELOPMENT_NON_RELEASE";;

end;;
